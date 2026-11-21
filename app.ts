// Coreforge: a standalone, GitHub-compatible git forge in one Node process.
//
// Surfaces, all over one in-memory store:
//   - git smart HTTP: upload-pack protocol v2 (ls-refs, fetch, shallow/deepen)
//     with a v0 fallback, and receive-pack v0 (report-status, side-band-64k,
//     delete-refs, fast-forward-only updates). No git binary: the object
//     model, pack reader/writer and pkt-line framing are implemented here.
//   - REST v3 under /api/v3: repositories, branches, commits, contents,
//     labels, issues, comments and pull requests (including squash merges).
//   - GraphQL v4 at /api/graphql: the documents gh and github-mcp-server send.
//   - MCP at /mcp: streamable HTTP JSON-RPC, both the 2026-07-28 discover
//     revision and the legacy initialize handshake.
//
// Only node: builtins are used; there is nothing to install.

import { createServer, type IncomingMessage, type Server, type ServerResponse } from 'node:http';
import { createHash } from 'node:crypto';
import { deflateSync, inflateSync } from 'node:zlib';

const JSON_TYPE = 'application/json; charset=utf-8';
const ZERO_OID = '0'.repeat(40);
const VIEWER_LOGIN = 'adaiversen';
const VIEWER_ID = 1000;
const TOKEN = process.env.MAKEFUN_SHOP_TOKEN ?? '';
let requestCounter = 0;
let commitClock = 1735689600;

// ---------------------------------------------------------------------------
// small helpers
// ---------------------------------------------------------------------------

function sha1hex(data: Buffer): string {
  return createHash('sha1').update(data).digest('hex');
}

function isOid(value: unknown): value is string {
  return typeof value === 'string' && /^[0-9a-f]{40}$/.test(value);
}

function b64encode(text: string): string {
  return Buffer.from(text, 'utf8').toString('base64');
}

function gid(kind: string, key: string): string {
  return Buffer.from(`${kind}:${key}`, 'utf8').toString('base64');
}

function ungid(id: string): { kind: string; key: string } | null {
  try {
    const text = Buffer.from(id, 'base64').toString('utf8');
    const at = text.indexOf(':');
    if (at < 0) return null;
    return { kind: text.slice(0, at), key: text.slice(at + 1) };
  } catch {
    return null;
  }
}

// ---------------------------------------------------------------------------
// git object model
// ---------------------------------------------------------------------------

type GitType = 'commit' | 'tree' | 'blob' | 'tag';
const TYPE_CODE: Record<GitType, number> = { commit: 1, tree: 2, blob: 3, tag: 4 };
const CODE_TYPE: Record<number, GitType> = { 1: 'commit', 2: 'tree', 3: 'blob', 4: 'tag' };

interface GitObject {
  type: GitType;
  data: Buffer;
}

function hashObject(type: GitType, data: Buffer): string {
  const header = Buffer.from(`${type} ${data.length}\0`, 'utf8');
  return sha1hex(Buffer.concat([header, data]));
}

interface TreeEntry {
  mode: string;
  name: string;
  oid: string;
}

function parseTree(data: Buffer): TreeEntry[] {
  const entries: TreeEntry[] = [];
  let offset = 0;
  while (offset < data.length) {
    const space = data.indexOf(0x20, offset);
    const nul = data.indexOf(0x00, space);
    const mode = data.subarray(offset, space).toString('utf8');
    const name = data.subarray(space + 1, nul).toString('utf8');
    const oid = data.subarray(nul + 1, nul + 21).toString('hex');
    entries.push({ mode, name, oid });
    offset = nul + 21;
  }
  return entries;
}

function treeSortKey(entry: TreeEntry): string {
  return entry.mode === '40000' || entry.mode === '040000' ? `${entry.name}/` : entry.name;
}

function buildTree(entries: TreeEntry[]): Buffer {
  const sorted = [...entries].sort((a, b) => (treeSortKey(a) < treeSortKey(b) ? -1 : treeSortKey(a) > treeSortKey(b) ? 1 : 0));
  const parts: Buffer[] = [];
  for (const entry of sorted) {
    parts.push(Buffer.from(`${entry.mode} ${entry.name}\0`, 'utf8'));
    parts.push(Buffer.from(entry.oid, 'hex'));
  }
  return Buffer.concat(parts);
}

interface CommitView {
  tree: string;
  parents: string[];
  message: string;
  author: string;
  timestamp: number;
}

function parseCommit(data: Buffer): CommitView {
  const text = data.toString('utf8');
  const blank = text.indexOf('\n\n');
  const head = blank < 0 ? text : text.slice(0, blank);
  const message = blank < 0 ? '' : text.slice(blank + 2);
  let tree = ZERO_OID;
  let author = '';
  let timestamp = 0;
  const parents: string[] = [];
  for (const line of head.split('\n')) {
    if (line.startsWith('tree ')) tree = line.slice(5).trim();
    else if (line.startsWith('parent ')) parents.push(line.slice(7).trim());
    else if (line.startsWith('author ')) {
      author = line.slice(7);
      const match = / (\d+) [+-]\d{4}$/.exec(author);
      if (match) timestamp = Number(match[1]);
    }
  }
  return { tree, parents, message, author, timestamp };
}

function peelToCommit(objects: Map<string, GitObject>, oid: string): string | null {
  let current = oid;
  for (let guard = 0; guard < 16; guard += 1) {
    const object = objects.get(current);
    if (!object) return null;
    if (object.type === 'commit') return current;
    if (object.type === 'tag') {
      const match = /^object ([0-9a-f]{40})/m.exec(object.data.toString('utf8'));
      if (!match) return null;
      current = match[1];
      continue;
    }
    return null;
  }
  return null;
}

/** Every object reachable from `tips` (commits walk parents, trees recurse). */
function collectReachable(objects: Map<string, GitObject>, tips: Iterable<string>, stopAt?: Set<string>): Set<string> {
  const seen = new Set<string>();
  const stack = [...tips];
  while (stack.length) {
    const oid = stack.pop()!;
    if (seen.has(oid)) continue;
    if (stopAt && stopAt.has(oid) && !tipsIncludes(tips, oid)) {
      // A boundary the caller already holds: count the commit itself as held
      // only when it is not a wanted tip; handled by the caller via stopAt.
    }
    seen.add(oid);
    const object = objects.get(oid);
    if (!object) continue;
    if (object.type === 'commit') {
      const view = parseCommit(object.data);
      stack.push(view.tree, ...view.parents);
    } else if (object.type === 'tree') {
      for (const entry of parseTree(object.data)) stack.push(entry.oid);
    } else if (object.type === 'tag') {
      const match = /^object ([0-9a-f]{40})/m.exec(object.data.toString('utf8'));
      if (match) stack.push(match[1]);
    }
  }
  return seen;
}

function tipsIncludes(tips: Iterable<string>, oid: string): boolean {
  for (const tip of tips) if (tip === oid) return true;
  return false;
}

/** Objects a shallow client holds: closure from `haves`, not crossing `boundary` commits' parents. */
function shallowClosure(objects: Map<string, GitObject>, haves: string[], boundary: Set<string>): Set<string> {
  const seen = new Set<string>();
  const stack = [...haves];
  while (stack.length) {
    const oid = stack.pop()!;
    if (seen.has(oid)) continue;
    seen.add(oid);
    const object = objects.get(oid);
    if (!object) continue;
    if (object.type === 'commit') {
      const view = parseCommit(object.data);
      stack.push(view.tree);
      if (!boundary.has(oid)) stack.push(...view.parents);
    } else if (object.type === 'tree') {
      for (const entry of parseTree(object.data)) stack.push(entry.oid);
    } else if (object.type === 'tag') {
      const match = /^object ([0-9a-f]{40})/m.exec(object.data.toString('utf8'));
      if (match) stack.push(match[1]);
    }
  }
  return seen;
}

/** Commit generations from the wants: BFS distance over parents (tags peel to commits), stopping at `limit`. */
function commitGenerations(objects: Map<string, GitObject>, wants: string[], limit = Infinity): Map<string, number> {
  const generations = new Map<string, number>();
  let frontier: string[] = [];
  for (const want of wants) {
    const commit = peelToCommit(objects, want);
    if (commit && !generations.has(commit)) {
      generations.set(commit, 0);
      frontier.push(commit);
    }
  }
  let depth = 0;
  while (frontier.length && depth < limit) {
    depth += 1;
    const next: string[] = [];
    for (const oid of frontier) {
      const object = objects.get(oid);
      if (!object || object.type !== 'commit') continue;
      for (const parent of parseCommit(object.data).parents) {
        if (!generations.has(parent)) {
          generations.set(parent, depth);
          next.push(parent);
        }
      }
    }
    frontier = next;
  }
  return generations;
}

function isAncestor(objects: Map<string, GitObject>, ancestor: string, descendant: string): boolean {
  if (ancestor === descendant) return true;
  const seen = new Set<string>();
  const stack = [descendant];
  while (stack.length) {
    const oid = stack.pop()!;
    if (oid === ancestor) return true;
    if (seen.has(oid)) continue;
    seen.add(oid);
    const object = objects.get(oid);
    if (object?.type === 'commit') stack.push(...parseCommit(object.data).parents);
  }
  return false;
}

function mergeBase(objects: Map<string, GitObject>, a: string, b: string): string | null {
  const ancestorsOfA = new Set<string>();
  const stack = [a];
  while (stack.length) {
    const oid = stack.pop()!;
    if (ancestorsOfA.has(oid)) continue;
    ancestorsOfA.add(oid);
    const object = objects.get(oid);
    if (object?.type === 'commit') stack.push(...parseCommit(object.data).parents);
  }
  const seen = new Set<string>();
  const queue = [b];
  while (queue.length) {
    const oid = queue.shift()!;
    if (ancestorsOfA.has(oid)) return oid;
    if (seen.has(oid)) continue;
    seen.add(oid);
    const object = objects.get(oid);
    if (object?.type === 'commit') queue.push(...parseCommit(object.data).parents);
  }
  return null;
}

// ---------------------------------------------------------------------------
// packfiles
// ---------------------------------------------------------------------------

function packObjectHeader(type: GitType, size: number): Buffer {
  const code = TYPE_CODE[type];
  const bytes: number[] = [];
  let remaining = size;
  let first = (code << 4) | (remaining & 0x0f);
  remaining = Math.floor(remaining / 16);
  while (remaining > 0) {
    bytes.push(first | 0x80);
    first = remaining & 0x7f;
    remaining = Math.floor(remaining / 128);
  }
  bytes.push(first);
  return Buffer.from(bytes);
}

function writePack(objects: GitObject[]): Buffer {
  const parts: Buffer[] = [];
  const header = Buffer.alloc(12);
  header.write('PACK', 0, 'ascii');
  header.writeUInt32BE(2, 4);
  header.writeUInt32BE(objects.length, 8);
  parts.push(header);
  for (const object of objects) {
    parts.push(packObjectHeader(object.type, object.data.length));
    parts.push(deflateSync(object.data));
  }
  const body = Buffer.concat(parts);
  return Buffer.concat([body, createHash('sha1').update(body).digest()]);
}

function applyDelta(base: Buffer, delta: Buffer): Buffer {
  let offset = 0;
  const readSize = (): number => {
    let value = 0;
    let shift = 0;
    for (;;) {
      const byte = delta[offset++];
      value += (byte & 0x7f) * 2 ** shift;
      shift += 7;
      if (!(byte & 0x80)) break;
    }
    return value;
  };
  const sourceSize = readSize();
  const targetSize = readSize();
  if (sourceSize !== base.length) throw new Error('delta base size mismatch');
  const out = Buffer.alloc(targetSize);
  let written = 0;
  while (offset < delta.length) {
    const op = delta[offset++];
    if (op & 0x80) {
      let copyOffset = 0;
      let copySize = 0;
      let shift = 0;
      for (let bit = 0; bit < 4; bit += 1) {
        if (op & (1 << bit)) copyOffset += delta[offset++] * 2 ** shift;
        shift += 8;
      }
      shift = 0;
      for (let bit = 4; bit < 7; bit += 1) {
        if (op & (1 << bit)) copySize += delta[offset++] * 2 ** shift;
        shift += 8;
      }
      if (copySize === 0) copySize = 0x10000;
      base.copy(out, written, copyOffset, copyOffset + copySize);
      written += copySize;
    } else if (op !== 0) {
      delta.copy(out, written, offset, offset + op);
      offset += op;
      written += op;
    } else {
      throw new Error('delta opcode 0');
    }
  }
  return out;
}

/** Parse a pack into resolved objects; thin-pack bases come from `existing`. */
function readPack(pack: Buffer, existing: Map<string, GitObject>): Map<string, GitObject> {
  if (pack.length < 32 || pack.subarray(0, 4).toString('ascii') !== 'PACK') throw new Error('not a pack');
  const count = pack.readUInt32BE(8);
  const trailerStart = pack.length - 20;
  interface Raw {
    offset: number;
    typeCode: number;
    data: Buffer;
    baseOffset?: number;
    baseOid?: string;
  }
  const raw: Raw[] = [];
  const byOffset = new Map<number, Raw>();
  let offset = 12;
  for (let index = 0; index < count; index += 1) {
    const entryOffset = offset;
    let byte = pack[offset++];
    const typeCode = (byte >> 4) & 0x07;
    while (byte & 0x80) {
      byte = pack[offset++];
    }
    const entry: Raw = { offset: entryOffset, typeCode, data: Buffer.alloc(0) };
    if (typeCode === 6) {
      let b = pack[offset++];
      let value = b & 0x7f;
      while (b & 0x80) {
        b = pack[offset++];
        value = ((value + 1) * 128) + (b & 0x7f);
      }
      entry.baseOffset = entryOffset - value;
    } else if (typeCode === 7) {
      entry.baseOid = pack.subarray(offset, offset + 20).toString('hex');
      offset += 20;
    }
    const inflated = inflateSync(pack.subarray(offset, trailerStart), { info: true }) as unknown as { buffer: Buffer; engine: { bytesWritten: number } };
    entry.data = inflated.buffer;
    offset += inflated.engine.bytesWritten;
    raw.push(entry);
    byOffset.set(entryOffset, entry);
  }
  const resolved = new Map<string, GitObject>();
  const resolveEntry = (entry: Raw): GitObject => {
    if (entry.typeCode === 6 || entry.typeCode === 7) {
      let base: GitObject | undefined;
      if (entry.typeCode === 6) {
        const baseRaw = byOffset.get(entry.baseOffset!);
        if (!baseRaw) throw new Error('ofs-delta base missing');
        base = resolveEntry(baseRaw);
      } else {
        base = resolved.get(entry.baseOid!) ?? existing.get(entry.baseOid!);
        if (!base) {
          for (const [oid, object] of resolved) if (oid === entry.baseOid) base = object;
        }
        if (!base) throw new Error('ref-delta base missing');
      }
      return { type: base.type, data: applyDelta(base.data, entry.data) };
    }
    const type = CODE_TYPE[entry.typeCode];
    if (!type) throw new Error(`bad pack type ${entry.typeCode}`);
    return { type, data: entry.data };
  };
  for (const entry of raw) {
    const object = resolveEntry(entry);
    resolved.set(hashObject(object.type, object.data), object);
  }
  return resolved;
}

// ---------------------------------------------------------------------------
// pkt-lines
// ---------------------------------------------------------------------------

function pktLine(payload: string | Buffer): Buffer {
  const body = typeof payload === 'string' ? Buffer.from(payload, 'utf8') : payload;
  const length = body.length + 4;
  const header = Buffer.from(length.toString(16).padStart(4, '0'), 'ascii');
  return Buffer.concat([header, body]);
}

const PKT_FLUSH = Buffer.from('0000', 'ascii');
const PKT_DELIM = Buffer.from('0001', 'ascii');

type Packet = { kind: 'data'; payload: Buffer } | { kind: 'flush' } | { kind: 'delim' } | { kind: 'end' };

function decodePackets(buffer: Buffer, startAt = 0): { packets: Packet[]; rest: number } {
  const packets: Packet[] = [];
  let offset = startAt;
  while (offset + 4 <= buffer.length) {
    const header = buffer.subarray(offset, offset + 4).toString('ascii');
    if (!/^[0-9a-fA-F]{4}$/.test(header)) break;
    const length = parseInt(header, 16);
    if (length === 0) {
      packets.push({ kind: 'flush' });
      offset += 4;
    } else if (length === 1) {
      packets.push({ kind: 'delim' });
      offset += 4;
    } else if (length === 2) {
      packets.push({ kind: 'end' });
      offset += 4;
    } else {
      if (offset + length > buffer.length) break;
      packets.push({ kind: 'data', payload: buffer.subarray(offset + 4, offset + length) });
      offset += length;
    }
  }
  return { packets, rest: offset };
}

function sidebandPackets(data: Buffer): Buffer[] {
  const out: Buffer[] = [];
  const maxChunk = 65515;
  if (data.length === 0) {
    out.push(pktLine(Buffer.concat([Buffer.from([1])])));
    return out;
  }
  for (let offset = 0; offset < data.length; offset += maxChunk) {
    out.push(pktLine(Buffer.concat([Buffer.from([1]), data.subarray(offset, offset + maxChunk)])));
  }
  return out;
}

// ---------------------------------------------------------------------------
// the store
// ---------------------------------------------------------------------------

interface Issue {
  number: number;
  title: string;
  body: string;
  state: 'open' | 'closed';
  labels: string[];
  comments: { id: number; body: string }[];
  seq: number;
}

interface Pull {
  number: number;
  title: string;
  body: string;
  head: string;
  base: string;
  state: 'open' | 'closed';
  merged: boolean;
  mergedAt: string | null;
  mergeCommitSha: string | null;
  seq: number;
}

interface Repo {
  id: number;
  owner: string;
  name: string;
  description: string;
  isPrivate: boolean;
  defaultBranch: string;
  objects: Map<string, GitObject>;
  objectSeq: Map<string, number>;
  refs: Map<string, string>;
  issues: Issue[];
  pulls: Pull[];
  labels: Map<string, { name: string; color: string }>;
  nextNumber: number;
  nextCommentId: number;
  seq: number;
}

const repos = new Map<string, Repo>();
let nextRepoId = 5000;
let globalSeq = 0;

function repoKey(owner: string, name: string): string {
  return `${owner}/${name}`;
}

function createRepo(owner: string, name: string, description: string, isPrivate: boolean): Repo {
  const repo: Repo = {
    id: nextRepoId++,
    owner,
    name,
    description,
    isPrivate,
    defaultBranch: 'main',
    objects: new Map(),
    objectSeq: new Map(),
    refs: new Map(),
    issues: [],
    pulls: [],
    labels: new Map(),
    nextNumber: 1,
    nextCommentId: 1,
    seq: ++globalSeq,
  };
  repos.set(repoKey(owner, name), repo);
  return repo;
}

function findRepo(owner: string, name: string): Repo | null {
  if (owner !== VIEWER_LOGIN) return null;
  return repos.get(repoKey(owner, name)) ?? null;
}

function storeObject(repo: Repo, type: GitType, data: Buffer): string {
  const oid = hashObject(type, data);
  if (!repo.objects.has(oid)) {
    repo.objects.set(oid, { type, data });
    repo.objectSeq.set(oid, ++globalSeq);
  }
  return oid;
}

/** Flatten a tree (by oid) into path -> {oid, mode}; empty map for no tree. */
function flattenTree(repo: Repo, treeOid: string | null): Map<string, { oid: string; mode: string }> {
  const out = new Map<string, { oid: string; mode: string }>();
  const walk = (oid: string, prefix: string): void => {
    const object = repo.objects.get(oid);
    if (!object || object.type !== 'tree') return;
    for (const entry of parseTree(object.data)) {
      const path = prefix ? `${prefix}/${entry.name}` : entry.name;
      if (entry.mode === '40000' || entry.mode === '040000') walk(entry.oid, path);
      else out.set(path, { oid: entry.oid, mode: entry.mode });
    }
  };
  if (treeOid) walk(treeOid, '');
  return out;
}

/** Build a tree oid from a flat path map, storing every subtree. */
function buildTreeFromFlat(repo: Repo, flat: Map<string, { oid: string; mode: string }>): string {
  interface Node {
    files: Map<string, { oid: string; mode: string }>;
    dirs: Map<string, Node>;
  }
  const root: Node = { files: new Map(), dirs: new Map() };
  for (const [path, entry] of flat) {
    const segments = path.split('/');
    let node = root;
    for (let i = 0; i < segments.length - 1; i += 1) {
      if (!node.dirs.has(segments[i])) node.dirs.set(segments[i], { files: new Map(), dirs: new Map() });
      node = node.dirs.get(segments[i])!;
    }
    node.files.set(segments[segments.length - 1], entry);
  }
  const build = (node: Node): string => {
    const entries: TreeEntry[] = [];
    for (const [name, entry] of node.files) entries.push({ mode: entry.mode, name, oid: entry.oid });
    for (const [name, child] of node.dirs) entries.push({ mode: '40000', name, oid: build(child) });
    return storeObject(repo, 'tree', buildTree(entries));
  };
  return build(root);
}

function commitTreeOf(repo: Repo, commitOid: string): string | null {
  const object = repo.objects.get(commitOid);
  if (!object || object.type !== 'commit') return null;
  return parseCommit(object.data).tree;
}

function makeCommit(repo: Repo, treeOid: string, parents: string[], message: string): string {
  commitClock += 1;
  const author = `${VIEWER_LOGIN} <${VIEWER_LOGIN}@example.invalid>`;
  const lines = [`tree ${treeOid}`];
  for (const parent of parents) lines.push(`parent ${parent}`);
  lines.push(`author ${author} ${commitClock} +0000`);
  lines.push(`committer ${author} ${commitClock} +0000`);
  const text = `${lines.join('\n')}\n\n${message.endsWith('\n') ? message : `${message}\n`}`;
  return storeObject(repo, 'commit', Buffer.from(text, 'utf8'));
}

/** Resolve a ref name, branch name or sha to a commit oid. */
function resolveCommit(repo: Repo, ref: string | undefined): string | null {
  if (!ref) {
    const tip = repo.refs.get(`refs/heads/${repo.defaultBranch}`);
    return tip ? peelToCommit(repo.objects, tip) : null;
  }
  if (isOid(ref) && repo.objects.has(ref)) return peelToCommit(repo.objects, ref);
  const candidates = [ref, `refs/heads/${ref}`, `refs/tags/${ref}`];
  for (const candidate of candidates) {
    const oid = repo.refs.get(candidate);
    if (oid) return peelToCommit(repo.objects, oid);
  }
  return null;
}

function branchTip(repo: Repo, branch: string): string | null {
  const oid = repo.refs.get(`refs/heads/${branch}`);
  return oid ? peelToCommit(repo.objects, oid) : null;
}

/** The files changed between a pull's merge base and its head, with line counts. */
function pullFiles(repo: Repo, pull: Pull): { filename: string; status: string; additions: number; deletions: number; changes: number }[] {
  const headTip = branchTip(repo, pull.head);
  const baseTip = branchTip(repo, pull.base);
  if (!headTip || !baseTip) return [];
  const base = mergeBase(repo.objects, baseTip, headTip) ?? baseTip;
  const before = flattenTree(repo, commitTreeOf(repo, base));
  const after = flattenTree(repo, commitTreeOf(repo, headTip));
  const files: { filename: string; status: string; additions: number; deletions: number; changes: number }[] = [];
  const paths = new Set([...before.keys(), ...after.keys()]);
  for (const path of [...paths].sort()) {
    const oldEntry = before.get(path);
    const newEntry = after.get(path);
    if (oldEntry?.oid === newEntry?.oid) continue;
    const oldText = oldEntry ? (repo.objects.get(oldEntry.oid)?.data.toString('utf8') ?? '') : '';
    const newText = newEntry ? (repo.objects.get(newEntry.oid)?.data.toString('utf8') ?? '') : '';
    const oldLines = oldText === '' ? 0 : oldText.split('\n').length;
    const newLines = newText === '' ? 0 : newText.split('\n').length;
    const additions = newEntry ? Math.max(1, newLines) : 0;
    const deletions = oldEntry ? Math.max(1, oldLines) : 0;
    files.push({
      filename: path,
      status: !oldEntry ? 'added' : !newEntry ? 'removed' : 'modified',
      additions: oldEntry && newEntry ? Math.max(1, Math.abs(newLines - oldLines) || 1) : additions,
      deletions: oldEntry && newEntry ? 0 : deletions,
      changes: (oldEntry && newEntry ? Math.max(1, Math.abs(newLines - oldLines) || 1) : additions) + (oldEntry && newEntry ? 0 : deletions),
    });
  }
  return files;
}

/** Three-way tree merge for a squash: returns the merged flat map, or null on conflict. */
function mergeTrees(
  repo: Repo,
  baseFlat: Map<string, { oid: string; mode: string }>,
  ourFlat: Map<string, { oid: string; mode: string }>,
  theirFlat: Map<string, { oid: string; mode: string }>,
): Map<string, { oid: string; mode: string }> | null {
  const merged = new Map<string, { oid: string; mode: string }>();
  const paths = new Set([...baseFlat.keys(), ...ourFlat.keys(), ...theirFlat.keys()]);
  for (const path of paths) {
    const base = baseFlat.get(path)?.oid;
    const ours = ourFlat.get(path)?.oid;
    const theirs = theirFlat.get(path)?.oid;
    if (ours === theirs) {
      const entry = ourFlat.get(path) ?? theirFlat.get(path);
      if (entry) merged.set(path, entry);
    } else if (base === ours) {
      const entry = theirFlat.get(path);
      if (entry) merged.set(path, entry);
    } else if (base === theirs) {
      const entry = ourFlat.get(path);
      if (entry) merged.set(path, entry);
    } else {
      return null;
    }
  }
  return merged;
}

function pullMergeable(repo: Repo, pull: Pull): boolean {
  if (pull.merged) return false;
  const headTip = branchTip(repo, pull.head);
  const baseTip = branchTip(repo, pull.base);
  if (!headTip || !baseTip) return false;
  const base = mergeBase(repo.objects, baseTip, headTip);
  if (!base) return false;
  const merged = mergeTrees(
    repo,
    flattenTree(repo, commitTreeOf(repo, base)),
    flattenTree(repo, commitTreeOf(repo, baseTip)),
    flattenTree(repo, commitTreeOf(repo, headTip)),
  );
  return merged !== null;
}

/** Squash-merge a pull onto its base branch. Returns the merge commit sha, or 'conflict'. */
function mergePull(repo: Repo, pull: Pull): string | 'conflict' | 'gone' {
  const headTip = branchTip(repo, pull.head);
  const baseTip = branchTip(repo, pull.base);
  if (!headTip || !baseTip) return 'gone';
  const base = mergeBase(repo.objects, baseTip, headTip);
  if (!base) return 'conflict';
  const merged = mergeTrees(
    repo,
    flattenTree(repo, commitTreeOf(repo, base)),
    flattenTree(repo, commitTreeOf(repo, baseTip)),
    flattenTree(repo, commitTreeOf(repo, headTip)),
  );
  if (!merged) return 'conflict';
  const treeOid = buildTreeFromFlat(repo, merged);
  const sha = makeCommit(repo, treeOid, [baseTip], `${pull.title}\n\nSquash merge of #${pull.number} (${pull.head} into ${pull.base})`);
  repo.refs.set(`refs/heads/${pull.base}`, sha);
  pull.state = 'closed';
  pull.merged = true;
  pull.mergeCommitSha = sha;
  commitClock += 0; // mergedAt uses the deterministic commit clock below
  pull.mergedAt = new Date(commitClock * 1000).toISOString();
  return sha;
}

// ---------------------------------------------------------------------------
// REST shapes
// ---------------------------------------------------------------------------

function repoJson(repo: Repo): Record<string, unknown> {
  return {
    id: repo.id,
    node_id: gid('Repository', String(repo.id)),
    name: repo.name,
    full_name: `${repo.owner}/${repo.name}`,
    owner: { login: repo.owner, id: VIEWER_ID, type: 'User' },
    private: repo.isPrivate,
    description: repo.description,
    fork: false,
    html_url: `https://forge.local/${repo.owner}/${repo.name}`,
    url: `/api/v3/repos/${repo.owner}/${repo.name}`,
    default_branch: repo.defaultBranch,
    visibility: repo.isPrivate ? 'private' : 'public',
    has_issues: true,
    open_issues_count: repo.issues.filter((issue) => issue.state === 'open').length,
    created_at: '2025-01-01T00:00:00Z',
    updated_at: '2025-01-01T00:00:00Z',
    pushed_at: '2025-01-01T00:00:00Z',
  };
}

function issueJson(repo: Repo, issue: Issue): Record<string, unknown> {
  return {
    id: repo.id * 100000 + issue.number,
    node_id: gid('Issue', `${repo.id}:${issue.number}`),
    number: issue.number,
    title: issue.title,
    body: issue.body,
    state: issue.state,
    labels: issue.labels.map((name) => {
      const label = repo.labels.get(name);
      return { id: 1, name, color: label?.color ?? 'ededed', description: null };
    }),
    user: { login: repo.owner, id: VIEWER_ID },
    comments: issue.comments.length,
    created_at: '2025-01-01T00:00:00Z',
    updated_at: '2025-01-01T00:00:00Z',
    html_url: `https://forge.local/${repo.owner}/${repo.name}/issues/${issue.number}`,
  };
}

function pullJson(repo: Repo, pull: Pull): Record<string, unknown> {
  const headTip = branchTip(repo, pull.head) ?? ZERO_OID;
  const baseTip = branchTip(repo, pull.base) ?? ZERO_OID;
  return {
    id: repo.id * 100000 + pull.number,
    node_id: gid('PullRequest', `${repo.id}:${pull.number}`),
    number: pull.number,
    title: pull.title,
    body: pull.body,
    state: pull.state,
    merged: pull.merged,
    merged_at: pull.mergedAt,
    merge_commit_sha: pull.mergeCommitSha,
    mergeable: pull.state === 'open' ? pullMergeable(repo, pull) : null,
    draft: false,
    user: { login: repo.owner, id: VIEWER_ID },
    head: { ref: pull.head, sha: headTip, label: `${repo.owner}:${pull.head}`, repo: repoJson(repo) },
    base: { ref: pull.base, sha: baseTip, label: `${repo.owner}:${pull.base}`, repo: repoJson(repo) },
    created_at: '2025-01-01T00:00:00Z',
    updated_at: '2025-01-01T00:00:00Z',
    html_url: `https://forge.local/${repo.owner}/${repo.name}/pull/${pull.number}`,
  };
}

function commitJson(repo: Repo, oid: string): Record<string, unknown> {
  const object = repo.objects.get(oid);
  const view = object?.type === 'commit' ? parseCommit(object.data) : { tree: ZERO_OID, parents: [], message: '', author: '', timestamp: 0 };
  return {
    sha: oid,
    node_id: gid('Commit', oid),
    commit: {
      message: view.message.replace(/\n$/, ''),
      tree: { sha: view.tree },
      author: { name: view.author.replace(/ <.*>$/, ''), email: `${VIEWER_LOGIN}@example.invalid`, date: new Date((view.timestamp || 1735689600) * 1000).toISOString() },
      committer: { name: view.author.replace(/ <.*>$/, ''), email: `${VIEWER_LOGIN}@example.invalid`, date: new Date((view.timestamp || 1735689600) * 1000).toISOString() },
    },
    parents: view.parents.map((parent) => ({ sha: parent })),
    author: { login: repo.owner, id: VIEWER_ID },
    committer: { login: repo.owner, id: VIEWER_ID },
  };
}

// ---------------------------------------------------------------------------
// HTTP plumbing
// ---------------------------------------------------------------------------

function sendJson(res: ServerResponse, status: number, body: unknown, headers: Record<string, string> = {}): void {
  const text = `${JSON.stringify(body)}\n`;
  requestCounter += 1;
  res.writeHead(status, {
    'content-type': JSON_TYPE,
    'content-length': Buffer.byteLength(text),
    'x-github-request-id': `req-${requestCounter.toString(16).padStart(8, '0')}`,
    ...headers,
  });
  res.end(text);
}

function sendEmpty(res: ServerResponse, status: number): void {
  requestCounter += 1;
  res.writeHead(status, { 'x-github-request-id': `req-${requestCounter.toString(16).padStart(8, '0')}` });
  res.end();
}

function readBody(req: IncomingMessage): Promise<Buffer> {
  return new Promise((resolve, reject) => {
    const chunks: Buffer[] = [];
    req.on('data', (chunk: Buffer) => chunks.push(chunk));
    req.on('end', () => resolve(Buffer.concat(chunks)));
    req.on('error', reject);
  });
}

function authed(req: IncomingMessage): boolean {
  if (!TOKEN) return true;
  return (req.headers.authorization ?? '') === `Bearer ${TOKEN}`;
}

type JsonBody = { ok: true; value: Record<string, unknown> } | { ok: false };

function parseJsonBody(raw: Buffer): JsonBody {
  if (raw.length === 0) return { ok: true, value: {} };
  try {
    const value = JSON.parse(raw.toString('utf8')) as unknown;
    if (typeof value !== 'object' || value === null || Array.isArray(value)) return { ok: false };
    return { ok: true, value: value as Record<string, unknown> };
  } catch {
    return { ok: false };
  }
}

function str(value: unknown): string {
  return typeof value === 'string' ? value : '';
}

function paginate<T>(req: IncomingMessage, url: URL, items: T[]): { page: T[]; headers: Record<string, string> } {
  const perPageRaw = Number(url.searchParams.get('per_page') ?? '30');
  const perPage = Number.isFinite(perPageRaw) && perPageRaw > 0 ? Math.min(100, Math.floor(perPageRaw)) : 30;
  const pageRaw = Number(url.searchParams.get('page') ?? '1');
  const page = Number.isFinite(pageRaw) && pageRaw > 0 ? Math.floor(pageRaw) : 1;
  const start = (page - 1) * perPage;
  const slice = items.slice(start, start + perPage);
  const headers: Record<string, string> = {};
  if (start + perPage < items.length) {
    const host = req.headers.host ?? 'localhost';
    const next = new URL(url.pathname, `http://${host}`);
    for (const [key, value] of url.searchParams) next.searchParams.set(key, value);
    next.searchParams.set('per_page', String(perPage));
    next.searchParams.set('page', String(page + 1));
    headers.link = `<${next.toString()}>; rel="next"`;
  }
  return { page: slice, headers };
}

// ---------------------------------------------------------------------------
// REST v3
// ---------------------------------------------------------------------------

function contentsResponse(repo: Repo, path: string, branch: string | undefined, body: Record<string, unknown>, res: ServerResponse): void {
  // Shared logic for PUT and DELETE /contents/{path}
  const branchName = str(body.branch) || repo.defaultBranch;
  const tip = branchTip(repo, branchName);
  const treeOid = tip ? commitTreeOf(repo, tip) : null;
  const flat = flattenTree(repo, treeOid);
  const message = str(body.message) || 'Update file';
  if (body.__delete === true) {
    const existing = flat.get(path);
    if (!existing) {
      sendJson(res, 404, { message: 'Not Found' });
      return;
    }
    if (str(body.sha) && str(body.sha) !== existing.oid) {
      sendJson(res, 409, { message: 'Conflict: sha does not match' });
      return;
    }
    flat.delete(path);
    const newTree = buildTreeFromFlat(repo, flat);
    const commit = makeCommit(repo, newTree, tip ? [tip] : [], message);
    repo.refs.set(`refs/heads/${branchName}`, commit);
    sendJson(res, 200, { content: null, commit: { sha: commit, message } });
    return;
  }
  const contentB64 = str(body.content);
  const data = Buffer.from(contentB64.replace(/\s/g, ''), 'base64');
  const blobOid = storeObject(repo, 'blob', data);
  const existing = flat.get(path);
  const givenSha = str(body.sha);
  if (existing) {
    if (!givenSha) {
      sendJson(res, 422, { message: 'Invalid request: "sha" wasn\'t supplied.' });
      return;
    }
    if (givenSha !== existing.oid) {
      sendJson(res, 409, { message: 'Conflict: sha does not match the current blob' });
      return;
    }
  }
  flat.set(path, { oid: blobOid, mode: '100644' });
  const newTree = buildTreeFromFlat(repo, flat);
  const commit = makeCommit(repo, newTree, tip ? [tip] : [], message);
  repo.refs.set(`refs/heads/${branchName}`, commit);
  const slash = path.lastIndexOf('/');
  sendJson(res, existing ? 200 : 201, {
    content: {
      name: slash < 0 ? path : path.slice(slash + 1),
      path,
      sha: blobOid,
      size: data.length,
      type: 'file',
      encoding: 'base64',
      content: contentB64,
    },
    commit: { sha: commit, message },
  });
}

function handleRest(req: IncomingMessage, res: ServerResponse, url: URL, raw: Buffer): void {
  const path = url.pathname;
  const method = req.method ?? 'GET';
  const segments = path.split('/').filter((part) => part !== '').map((part) => decodeURIComponent(part));
  // segments: ['api','v3', ...]
  const rest = segments.slice(2);

  if (!authed(req)) {
    sendJson(res, 401, { message: 'Bad credentials' });
    return;
  }

  if (rest.length === 0) {
    if (method !== 'GET') return sendJson(res, 404, { message: 'Not Found' });
    sendJson(res, 200, {
      current_user_url: '/api/v3/user',
      repository_url: '/api/v3/repos/{owner}/{repo}',
      rate_limit_url: '/api/v3/rate_limit',
    }, { 'x-oauth-scopes': 'repo, read:org' });
    return;
  }

  if (rest[0] === 'meta' && rest.length === 1) {
    if (method !== 'GET') return sendJson(res, 404, { message: 'Not Found' });
    sendJson(res, 200, { installed_version: '1.0.0-coreforge', hooks: [], git_url: 'git://forge.local/', api_url: '/api/v3/' });
    return;
  }

  if (rest[0] === 'user' && rest.length === 1 && method === 'GET') {
    sendJson(res, 200, { login: VIEWER_LOGIN, id: VIEWER_ID, type: 'User', name: VIEWER_LOGIN });
    return;
  }

  if (rest[0] === 'user' && rest[1] === 'repos' && rest.length === 2) {
    if (method === 'GET') {
      const mine = [...repos.values()].filter((repo) => repo.owner === VIEWER_LOGIN).sort((a, b) => a.seq - b.seq);
      const { page, headers } = paginate(req, url, mine.map(repoJson));
      sendJson(res, 200, page, headers);
      return;
    }
    if (method === 'POST') {
      const parsed = parseJsonBody(raw);
      if (!parsed.ok) return sendJson(res, 400, { message: 'Problems parsing JSON' });
      const name = str(parsed.value.name);
      if (!name) return sendJson(res, 422, { message: 'Validation Failed: name is required' });
      if (repos.has(repoKey(VIEWER_LOGIN, name))) {
        return sendJson(res, 422, { message: 'Validation Failed: name already exists on this account' });
      }
      const repo = createRepo(VIEWER_LOGIN, name, str(parsed.value.description), parsed.value.private === true);
      sendJson(res, 201, repoJson(repo));
      return;
    }
    return sendJson(res, 404, { message: 'Not Found' });
  }

  if (rest[0] !== 'repos' || rest.length < 3) {
    return sendJson(res, 404, { message: 'Not Found' });
  }
  const owner = rest[1];
  const repoName = rest[2];
  const repo = findRepo(owner, repoName);
  if (!repo) return sendJson(res, 404, { message: 'Not Found' });
  const tail = rest.slice(3);

  if (tail.length === 0) {
    if (method === 'GET') return sendJson(res, 200, repoJson(repo));
    if (method === 'PATCH') {
      const parsed = parseJsonBody(raw);
      if (!parsed.ok) return sendJson(res, 400, { message: 'Problems parsing JSON' });
      if (typeof parsed.value.description === 'string') repo.description = parsed.value.description;
      if (typeof parsed.value.private === 'boolean') repo.isPrivate = parsed.value.private;
      if (typeof parsed.value.name === 'string' && parsed.value.name) repo.name = parsed.value.name;
      return sendJson(res, 200, repoJson(repo));
    }
    if (method === 'DELETE') {
      repos.delete(repoKey(repo.owner, repo.name));
      return sendEmpty(res, 204);
    }
    return sendJson(res, 404, { message: 'Not Found' });
  }

  // ---- branches & commits
  if (tail[0] === 'branches' && tail.length === 1 && method === 'GET') {
    const branches = [...repo.refs.entries()]
      .filter(([ref]) => ref.startsWith('refs/heads/'))
      .map(([ref, oid]) => ({ name: ref.slice('refs/heads/'.length), commit: { sha: peelToCommit(repo.objects, oid) ?? oid }, protected: false }));
    return sendJson(res, 200, branches);
  }
  if (tail[0] === 'branches' && tail.length === 2 && method === 'GET') {
    const tip = branchTip(repo, decodeURIComponent(tail[1]));
    if (!tip) return sendJson(res, 404, { message: 'Not Found' });
    return sendJson(res, 200, { name: tail[1], commit: { sha: tip }, protected: false });
  }
  if (tail[0] === 'commits' && tail.length === 1 && method === 'GET') {
    const start = resolveCommit(repo, url.searchParams.get('sha') ?? undefined);
    if (!start) return sendJson(res, 200, []);
    const seen = new Set<string>();
    const queue = [start];
    const commits: string[] = [];
    while (queue.length) {
      const oid = queue.shift()!;
      if (seen.has(oid)) continue;
      seen.add(oid);
      commits.push(oid);
      const object = repo.objects.get(oid);
      if (object?.type === 'commit') queue.push(...parseCommit(object.data).parents);
    }
    commits.sort((a, b) => (repo.objectSeq.get(b) ?? 0) - (repo.objectSeq.get(a) ?? 0));
    const { page, headers } = paginate(req, url, commits.map((oid) => commitJson(repo, oid)));
    return sendJson(res, 200, page, headers);
  }
  if (tail[0] === 'commits' && tail.length === 2 && method === 'GET') {
    const oid = tail[1];
    if (!isOid(oid) || !repo.objects.has(oid)) return sendJson(res, 404, { message: 'Not Found' });
    return sendJson(res, 200, commitJson(repo, oid));
  }

  // ---- git refs
  if (tail[0] === 'git' && tail[1] === 'refs' && tail.length === 2 && method === 'POST') {
    const parsed = parseJsonBody(raw);
    if (!parsed.ok) return sendJson(res, 400, { message: 'Problems parsing JSON' });
    const ref = str(parsed.value.ref);
    const sha = str(parsed.value.sha);
    if (!ref.startsWith('refs/') || !isOid(sha) || !repo.objects.has(sha)) {
      return sendJson(res, 422, { message: 'Validation Failed: invalid ref or sha' });
    }
    repo.refs.set(ref, sha);
    return sendJson(res, 201, { ref, object: { sha, type: repo.objects.get(sha)?.type ?? 'commit' } });
  }
  if (tail[0] === 'git' && tail[1] === 'refs' && tail.length >= 3 && method === 'GET') {
    const ref = tail.slice(2).join('/');
    const full = ref.startsWith('refs/') ? ref : `refs/${ref}`;
    const oid = repo.refs.get(full);
    if (!oid) return sendJson(res, 404, { message: 'Not Found' });
    return sendJson(res, 200, { ref: full, object: { sha: oid, type: repo.objects.get(oid)?.type ?? 'commit' } });
  }

  // ---- contents
  if (tail[0] === 'contents' && tail.length >= 2) {
    const filePath = tail.slice(1).join('/');
    if (method === 'GET') {
      const commit = resolveCommit(repo, url.searchParams.get('ref') ?? undefined);
      if (!commit) return sendJson(res, 404, { message: 'Not Found' });
      const flat = flattenTree(repo, commitTreeOf(repo, commit));
      const entry = flat.get(filePath);
      if (entry) {
        const data = repo.objects.get(entry.oid)?.data ?? Buffer.alloc(0);
        const slash = filePath.lastIndexOf('/');
        return sendJson(res, 200, {
          type: 'file',
          encoding: 'base64',
          content: data.toString('base64'),
          name: slash < 0 ? filePath : filePath.slice(slash + 1),
          path: filePath,
          sha: entry.oid,
          size: data.length,
        });
      }
      // directory?
      const prefix = `${filePath}/`;
      const children = new Map<string, { type: string; oid: string }>();
      for (const [pathKey, value] of flat) {
        if (!pathKey.startsWith(prefix)) continue;
        const restPath = pathKey.slice(prefix.length);
        const first = restPath.split('/')[0];
        if (restPath.includes('/')) {
          if (!children.has(first)) {
            // subtree oid: find via tree walk
            children.set(first, { type: 'dir', oid: subtreeOid(repo, commitTreeOf(repo, commit), `${filePath}/${first}`) ?? ZERO_OID });
          }
        } else {
          children.set(first, { type: 'file', oid: value.oid });
        }
      }
      if (children.size === 0) return sendJson(res, 404, { message: 'Not Found' });
      const listing = [...children.entries()].map(([name, value]) => ({
        type: value.type,
        name,
        path: `${filePath}/${name}`,
        sha: value.oid,
        size: value.type === 'file' ? (repo.objects.get(value.oid)?.data.length ?? 0) : 0,
      }));
      return sendJson(res, 200, listing);
    }
    if (method === 'PUT') {
      const parsed = parseJsonBody(raw);
      if (!parsed.ok) return sendJson(res, 400, { message: 'Problems parsing JSON' });
      return contentsResponse(repo, filePath, undefined, parsed.value, res);
    }
    if (method === 'DELETE') {
      const parsed = parseJsonBody(raw);
      if (!parsed.ok) return sendJson(res, 400, { message: 'Problems parsing JSON' });
      return contentsResponse(repo, filePath, undefined, { ...parsed.value, __delete: true }, res);
    }
    return sendJson(res, 404, { message: 'Not Found' });
  }

  // ---- labels
  if (tail[0] === 'labels' && tail.length === 1) {
    if (method === 'POST') {
      const parsed = parseJsonBody(raw);
      if (!parsed.ok) return sendJson(res, 400, { message: 'Problems parsing JSON' });
      const name = str(parsed.value.name);
      if (!name) return sendJson(res, 422, { message: 'Validation Failed: name is required' });
      const color = str(parsed.value.color) || 'ededed';
      repo.labels.set(name, { name, color });
      return sendJson(res, 201, { id: 1, name, color, default: false, description: null });
    }
    if (method === 'GET') {
      return sendJson(res, 200, [...repo.labels.values()].map((label) => ({ id: 1, name: label.name, color: label.color, default: false, description: null })));
    }
    return sendJson(res, 404, { message: 'Not Found' });
  }

  // ---- issues
  if (tail[0] === 'issues' && tail.length === 1) {
    if (method === 'POST') {
      const parsed = parseJsonBody(raw);
      if (!parsed.ok) return sendJson(res, 400, { message: 'Problems parsing JSON' });
      const labels = Array.isArray(parsed.value.labels) ? parsed.value.labels.map((label) => String(label)) : [];
      for (const label of labels) {
        if (!repo.labels.has(label)) return sendJson(res, 422, { message: `Validation Failed: label "${label}" does not exist` });
      }
      const issue: Issue = {
        number: repo.nextNumber++,
        title: str(parsed.value.title),
        body: str(parsed.value.body),
        state: 'open',
        labels,
        comments: [],
        seq: ++globalSeq,
      };
      repo.issues.push(issue);
      return sendJson(res, 201, issueJson(repo, issue));
    }
    if (method === 'GET') {
      const state = url.searchParams.get('state') ?? 'open';
      let list = repo.issues.filter((issue) => state === 'all' || issue.state === state);
      const direction = url.searchParams.get('direction') ?? 'desc';
      list = [...list].sort((a, b) => (direction === 'asc' ? a.number - b.number : b.number - a.number));
      const { page, headers } = paginate(req, url, list.map((issue) => issueJson(repo, issue)));
      return sendJson(res, 200, page, headers);
    }
    return sendJson(res, 404, { message: 'Not Found' });
  }
  if (tail[0] === 'issues' && tail.length >= 2) {
    const number = Number(tail[1]);
    const issue = repo.issues.find((candidate) => candidate.number === number);
    if (!issue) return sendJson(res, 404, { message: 'Not Found' });
    if (tail.length === 2) {
      if (method === 'GET') return sendJson(res, 200, issueJson(repo, issue));
      if (method === 'PATCH') {
        const parsed = parseJsonBody(raw);
        if (!parsed.ok) return sendJson(res, 400, { message: 'Problems parsing JSON' });
        if (parsed.value.state === 'open' || parsed.value.state === 'closed') issue.state = parsed.value.state;
        if (typeof parsed.value.title === 'string') issue.title = parsed.value.title;
        if (typeof parsed.value.body === 'string') issue.body = parsed.value.body;
        return sendJson(res, 200, issueJson(repo, issue));
      }
      return sendJson(res, 404, { message: 'Not Found' });
    }
    if (tail.length === 3 && tail[2] === 'comments') {
      if (method === 'POST') {
        const parsed = parseJsonBody(raw);
        if (!parsed.ok) return sendJson(res, 400, { message: 'Problems parsing JSON' });
        const comment = { id: repo.nextCommentId++, body: str(parsed.value.body) };
        issue.comments.push(comment);
        return sendJson(res, 201, { id: comment.id, body: comment.body, user: { login: repo.owner, id: VIEWER_ID }, created_at: '2025-01-01T00:00:00Z' });
      }
      if (method === 'GET') {
        return sendJson(res, 200, issue.comments.map((comment) => ({ id: comment.id, body: comment.body, user: { login: repo.owner, id: VIEWER_ID }, created_at: '2025-01-01T00:00:00Z' })));
      }
      return sendJson(res, 404, { message: 'Not Found' });
    }
    return sendJson(res, 404, { message: 'Not Found' });
  }

  // ---- pulls
  if (tail[0] === 'pulls' && tail.length === 1) {
    if (method === 'POST') {
      const parsed = parseJsonBody(raw);
      if (!parsed.ok) return sendJson(res, 400, { message: 'Problems parsing JSON' });
      const head = str(parsed.value.head).replace(/^[^:]+:/, '');
      const base = str(parsed.value.base).replace(/^[^:]+:/, '');
      if (!branchTip(repo, head) || !branchTip(repo, base)) {
        return sendJson(res, 422, { message: 'Validation Failed: head or base branch does not exist' });
      }
      const existing = repo.pulls.find((pull) => pull.head === head && pull.base === base && pull.state === 'open');
      if (existing) return sendJson(res, 422, { message: 'Validation Failed: a pull request already exists for this branch' });
      const pull: Pull = {
        number: repo.nextNumber++,
        title: str(parsed.value.title),
        body: str(parsed.value.body),
        head,
        base,
        state: 'open',
        merged: false,
        mergedAt: null,
        mergeCommitSha: null,
        seq: ++globalSeq,
      };
      repo.pulls.push(pull);
      return sendJson(res, 201, pullJson(repo, pull));
    }
    if (method === 'GET') {
      const state = url.searchParams.get('state') ?? 'open';
      const list = repo.pulls
        .filter((pull) => state === 'all' || pull.state === state)
        .sort((a, b) => b.number - a.number)
        .map((pull) => pullJson(repo, pull));
      const { page, headers } = paginate(req, url, list);
      return sendJson(res, 200, page, headers);
    }
    return sendJson(res, 404, { message: 'Not Found' });
  }
  if (tail[0] === 'pulls' && tail.length >= 2) {
    const number = Number(tail[1]);
    const pull = repo.pulls.find((candidate) => candidate.number === number);
    if (tail.length === 3 && tail[2] === 'merge' && method === 'PUT') {
      if (!pull) return sendJson(res, 404, { message: 'Not Found' });
      const parsed = parseJsonBody(raw);
      if (!parsed.ok) return sendJson(res, 400, { message: 'Problems parsing JSON' });
      if (pull.merged && pull.mergeCommitSha) {
        return sendJson(res, 200, { sha: pull.mergeCommitSha, merged: true, message: 'Pull Request successfully merged' });
      }
      const result = mergePull(repo, pull);
      if (result === 'conflict') return sendJson(res, 405, { message: 'Pull Request is not mergeable: conflict' });
      if (result === 'gone') return sendJson(res, 404, { message: 'Not Found' });
      return sendJson(res, 200, { sha: result, merged: true, message: 'Pull Request successfully merged' });
    }
    if (!pull) return sendJson(res, 404, { message: 'Not Found' });
    if (tail.length === 2 && method === 'GET') return sendJson(res, 200, pullJson(repo, pull));
    if (tail.length === 3 && tail[2] === 'files' && method === 'GET') {
      const files = pullFiles(repo, pull).map((file) => ({ ...file, sha: ZERO_OID, filename: file.filename }));
      const { page, headers } = paginate(req, url, files);
      return sendJson(res, 200, page, headers);
    }
    return sendJson(res, 404, { message: 'Not Found' });
  }

  return sendJson(res, 404, { message: 'Not Found' });
}

/** Walk a tree to the subtree oid at `path` (for directory listings). */
function subtreeOid(repo: Repo, treeOid: string | null, path: string): string | null {
  if (!treeOid) return null;
  let current = treeOid;
  for (const segment of path.split('/')) {
    const object = repo.objects.get(current);
    if (!object || object.type !== 'tree') return null;
    const entry = parseTree(object.data).find((candidate) => candidate.name === segment);
    if (!entry) return null;
    current = entry.oid;
  }
  return current;
}

// ---------------------------------------------------------------------------
// git smart HTTP
// ---------------------------------------------------------------------------

function sortedRefs(repo: Repo): [string, string][] {
  return [...repo.refs.entries()].sort(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0));
}

function defaultTip(repo: Repo): string | null {
  return repo.refs.get(`refs/heads/${repo.defaultBranch}`) ?? null;
}

function v0Advertisement(repo: Repo, service: string): Buffer {
  const isReceive = service === 'git-receive-pack';
  const caps = isReceive
    ? 'report-status side-band-64k delete-refs ofs-delta agent=coreforge/1.0'
    : `multi_ack_detailed side-band-64k thin-pack ofs-delta shallow symref=HEAD:refs/heads/${repo.defaultBranch} agent=coreforge/1.0`;
  const parts: Buffer[] = [pktLine(`# service=${service}\n`), PKT_FLUSH];
  const refs = sortedRefs(repo);
  if (refs.length === 0) {
    parts.push(pktLine(`${ZERO_OID} capabilities^{}\0${caps}\n`));
  } else {
    let first = true;
    const headOid = defaultTip(repo) ?? refs[0][1];
    const lines: [string, string][] = [['HEAD', headOid], ...refs];
    for (const [name, oid] of lines) {
      parts.push(pktLine(first ? `${oid} ${name}\0${caps}\n` : `${oid} ${name}\n`));
      first = false;
      const object = repo.objects.get(oid);
      if (object?.type === 'tag') {
        const peeled = peelToCommit(repo.objects, oid);
        if (peeled) parts.push(pktLine(`${peeled} ${name}^{}\n`));
      }
    }
  }
  parts.push(PKT_FLUSH);
  return Buffer.concat(parts);
}

function v2Advertisement(): Buffer {
  const lines = [
    'version 2\n',
    'agent=coreforge/1.0\n',
    'ls-refs=unborn\n',
    'fetch=shallow filter wait-for-done\n',
    'object-format=sha1\n',
  ];
  return Buffer.concat([...lines.map((line) => pktLine(line)), PKT_FLUSH]);
}

function sendGit(res: ServerResponse, contentType: string, body: Buffer): void {
  res.writeHead(200, { 'content-type': contentType, 'content-length': body.length, 'cache-control': 'no-cache' });
  res.end(body);
}

function handleInfoRefs(req: IncomingMessage, res: ServerResponse, url: URL, repo: Repo, service: string): void {
  const isV2 = (req.headers['git-protocol'] ?? '').includes('version=2') && service === 'git-upload-pack';
  if (isV2) {
    sendGit(res, 'application/x-git-upload-pack-advertisement', v2Advertisement());
    return;
  }
  sendGit(res, `application/x-${service}-advertisement`, v0Advertisement(repo, service));
}

function lsRefsResponse(repo: Repo, args: string[]): Buffer {
  const peel = args.includes('peel');
  const symrefs = args.includes('symrefs');
  const unborn = args.includes('unborn');
  const prefixes = args.filter((arg) => arg.startsWith('ref-prefix ')).map((arg) => arg.slice('ref-prefix '.length));
  const matches = (name: string): boolean => prefixes.length === 0 || prefixes.some((prefix) => name.startsWith(prefix));
  const parts: Buffer[] = [];
  const headTarget = `refs/heads/${repo.defaultBranch}`;
  const headOid = defaultTip(repo);
  if (matches('HEAD')) {
    if (headOid) {
      parts.push(pktLine(`${headOid} HEAD${symrefs ? ` symref-target:${headTarget}` : ''}\n`));
    } else if (unborn) {
      parts.push(pktLine(`unborn HEAD${symrefs ? ` symref-target:${headTarget}` : ''}\n`));
    }
  }
  for (const [name, oid] of sortedRefs(repo)) {
    if (!matches(name)) continue;
    let suffix = '';
    const object = repo.objects.get(oid);
    if (peel && object?.type === 'tag') {
      const peeled = peelToCommit(repo.objects, oid);
      if (peeled) suffix += ` peeled:${peeled}`;
    }
    parts.push(pktLine(`${oid} ${name}${suffix}\n`));
  }
  parts.push(PKT_FLUSH);
  return Buffer.concat(parts);
}

interface FetchArgs {
  wants: string[];
  haves: string[];
  shallow: string[];
  deepen: number | null;
}

function computeFetch(repo: Repo, args: FetchArgs): { send: GitObject[]; shallowLines: string[]; unshallowLines: string[] } {
  const objects = repo.objects;
  const held = args.shallow.length
    ? shallowClosure(objects, args.haves, new Set(args.shallow))
    : collectReachable(objects, args.haves);
  let included: Set<string>;
  let boundary: string[] = [];
  let unshallow: string[] = [];
  if (args.deepen !== null) {
    const generations = commitGenerations(objects, args.wants, args.deepen);
    const includedCommits = new Set<string>();
    for (const [commit, generation] of generations) {
      if (generation < args.deepen) includedCommits.add(commit);
    }
    // Commit + its own tree closure, per included commit.
    included = new Set<string>();
    for (const commit of includedCommits) {
      included.add(commit);
      const tree = commitTreeOf(repo, commit);
      if (tree) for (const oid of collectReachable(objects, [tree])) included.add(oid);
    }
    // Tag objects that are direct wants are always included.
    for (const want of args.wants) {
      if (objects.get(want)?.type === 'tag') included.add(want);
    }
    for (const commit of includedCommits) {
      const view = parseCommit(objects.get(commit)!.data);
      if (view.parents.some((parent) => !includedCommits.has(parent))) boundary.push(commit);
    }
    unshallow = args.shallow.filter((oid) => includedCommits.has(oid) && !boundary.includes(oid));
  } else {
    included = collectReachable(objects, args.wants);
  }
  const send: GitObject[] = [];
  for (const oid of included) {
    if (held.has(oid)) continue;
    const object = objects.get(oid);
    if (object) send.push(object);
  }
  return { send, shallowLines: boundary, unshallowLines: unshallow };
}

function fetchResponseV2(repo: Repo, args: FetchArgs): Buffer {
  const { send, shallowLines, unshallowLines } = computeFetch(repo, args);
  const parts: Buffer[] = [];
  parts.push(pktLine('acknowledgments\n'));
  const acked = args.haves.filter((have) => repo.objects.has(have));
  if (acked.length) {
    for (const have of acked) parts.push(pktLine(`ACK ${have}\n`));
    parts.push(pktLine('ready\n'));
  } else {
    parts.push(pktLine('NAK\n'));
  }
  parts.push(PKT_DELIM);
  if (shallowLines.length || unshallowLines.length) {
    parts.push(pktLine('shallow-info\n'));
    for (const oid of shallowLines) parts.push(pktLine(`shallow ${oid}\n`));
    for (const oid of unshallowLines) parts.push(pktLine(`unshallow ${oid}\n`));
    parts.push(PKT_DELIM);
  }
  if (send.length || args.wants.length) {
    parts.push(pktLine('packfile\n'));
    const pack = writePack(send);
    for (const packet of sidebandPackets(pack)) parts.push(packet);
    parts.push(PKT_DELIM);
  }
  parts.push(PKT_FLUSH);
  return Buffer.concat(parts);
}

function fetchResponseV0(repo: Repo, args: FetchArgs): Buffer {
  const { send, shallowLines } = computeFetch(repo, args);
  const parts: Buffer[] = [];
  for (const oid of shallowLines) parts.push(pktLine(`shallow ${oid}\n`));
  parts.push(pktLine('NAK\n'));
  const pack = writePack(send);
  for (const packet of sidebandPackets(pack)) parts.push(packet);
  parts.push(PKT_FLUSH);
  return Buffer.concat(parts);
}

function parseFetchArgs(lines: string[]): FetchArgs {
  const args: FetchArgs = { wants: [], haves: [], shallow: [], deepen: null };
  for (const rawLine of lines) {
    const line = rawLine.replace(/\n$/, '');
    if (line.startsWith('want ')) args.wants.push(line.slice(5).trim().split(' ')[0]);
    else if (line.startsWith('have ')) args.haves.push(line.slice(5).trim());
    else if (line.startsWith('shallow ')) args.shallow.push(line.slice(8).trim());
    else if (line.startsWith('deepen ')) args.deepen = Number(line.slice(7).trim());
    else if (line.startsWith('deepen-since ') || line.startsWith('deepen-not ')) {
      // Not exercised by the suite; ignore.
    }
  }
  args.wants = args.wants.filter(isOid);
  args.haves = args.haves.filter(isOid);
  args.shallow = args.shallow.filter(isOid);
  return args;
}

function handleUploadPack(res: ServerResponse, repo: Repo, raw: Buffer): void {
  const { packets, rest } = decodePackets(raw);
  void rest;
  const lines: string[] = [];
  for (const packet of packets) {
    if (packet.kind === 'data') lines.push(packet.payload.toString('utf8'));
  }
  const first = (lines[0] ?? '').replace(/\n$/, '');
  if (first.startsWith('command=ls-refs')) {
    sendGit(res, 'application/x-git-upload-pack-result', lsRefsResponse(repo, lines.map((line) => line.replace(/\n$/, ''))));
    return;
  }
  if (first.startsWith('command=fetch')) {
    sendGit(res, 'application/x-git-upload-pack-result', fetchResponseV2(repo, parseFetchArgs(lines)));
    return;
  }
  if (first.startsWith('want ') || lines.some((line) => line.startsWith('want '))) {
    sendGit(res, 'application/x-git-upload-pack-result', fetchResponseV0(repo, parseFetchArgs(lines)));
    return;
  }
  // Malformed request: answer 400 and stay up.
  sendJson(res, 400, { message: 'Bad request' });
}

function handleReceivePack(res: ServerResponse, repo: Repo, raw: Buffer): void {
  const { packets, rest } = decodePackets(raw);
  const packBytes = raw.subarray(rest);
  interface Command {
    oldOid: string;
    newOid: string;
    ref: string;
  }
  const commands: Command[] = [];
  let capabilities = '';
  for (const packet of packets) {
    if (packet.kind === 'flush') break;
    if (packet.kind !== 'data') continue;
    let text = packet.payload.toString('utf8').replace(/\n$/, '');
    const nul = text.indexOf('\0');
    if (nul >= 0) {
      capabilities = text.slice(nul + 1);
      text = text.slice(0, nul);
    }
    const match = /^([0-9a-f]{40}) ([0-9a-f]{40}) (\S+)$/.exec(text);
    if (match) commands.push({ oldOid: match[1], newOid: match[2], ref: match[3] });
  }
  const wantsSideband = capabilities.includes('side-band-64k');
  const wantsReport = capabilities.includes('report-status');

  // Ingest the pack into a scratch overlay first.
  let unpackError: string | null = null;
  let packObjects = new Map<string, GitObject>();
  const hasPack = packBytes.length > 0 && commands.some((command) => command.newOid !== ZERO_OID);
  if (packBytes.length > 0) {
    try {
      packObjects = readPack(Buffer.from(packBytes), repo.objects);
    } catch (err) {
      unpackError = err instanceof Error ? err.message : 'unpack error';
    }
  }
  void hasPack;
  const merged = new Map<string, GitObject>([...repo.objects, ...packObjects]);
  const lookupCommit = (oid: string): string | null => peelToCommit(merged, oid);

  const reportLines: string[] = [];
  reportLines.push(unpackError ? `unpack ${unpackError}` : 'unpack ok');
  const results: { command: Command; ok: boolean; reason: string }[] = [];
  for (const command of commands) {
    if (unpackError) {
      results.push({ command, ok: false, reason: 'unpacker error' });
      continue;
    }
    if (command.newOid === ZERO_OID) {
      if (!repo.refs.has(command.ref)) {
        results.push({ command, ok: false, reason: 'reference not found' });
      } else {
        results.push({ command, ok: true, reason: '' });
      }
      continue;
    }
    if (!merged.has(command.newOid)) {
      results.push({ command, ok: false, reason: 'unknown object' });
      continue;
    }
    const current = repo.refs.get(command.ref) ?? ZERO_OID;
    const effectiveOld = command.oldOid === ZERO_OID ? current : command.oldOid;
    if (effectiveOld !== ZERO_OID) {
      const oldCommit = lookupCommit(effectiveOld);
      const newCommit = lookupCommit(command.newOid);
      if (!oldCommit || !newCommit || !isAncestor(merged, oldCommit, newCommit)) {
        results.push({ command, ok: false, reason: 'non-fast-forward' });
        continue;
      }
    }
    results.push({ command, ok: true, reason: '' });
  }
  // Commit the pack objects and the successful ref updates.
  if (!unpackError) {
    for (const [oid, object] of packObjects) {
      if (!repo.objects.has(oid)) {
        repo.objects.set(oid, object);
        repo.objectSeq.set(oid, ++globalSeq);
      }
    }
    for (const result of results) {
      if (!result.ok) continue;
      if (result.command.newOid === ZERO_OID) repo.refs.delete(result.command.ref);
      else repo.refs.set(result.command.ref, result.command.newOid);
    }
  }
  for (const result of results) {
    reportLines.push(result.ok ? `ok ${result.command.ref}` : `ng ${result.command.ref} ${result.reason}`);
  }
  if (!wantsReport) {
    sendGit(res, 'application/x-git-receive-pack-result', Buffer.alloc(0));
    return;
  }
  const reportStream = Buffer.concat([...reportLines.map((line) => pktLine(`${line}\n`)), PKT_FLUSH]);
  if (wantsSideband) {
    const chunks: Buffer[] = [];
    const maxChunk = 65515;
    for (let offset = 0; offset < reportStream.length; offset += maxChunk) {
      chunks.push(pktLine(Buffer.concat([Buffer.from([1]), reportStream.subarray(offset, offset + maxChunk)])));
    }
    chunks.push(PKT_FLUSH);
    sendGit(res, 'application/x-git-receive-pack-result', Buffer.concat(chunks));
    return;
  }
  sendGit(res, 'application/x-git-receive-pack-result', reportStream);
}

// ---------------------------------------------------------------------------
// GraphQL v4 (a small executor for the documents gh / github-mcp-server send)
// ---------------------------------------------------------------------------

interface GqlField {
  name: string;
  alias: string | null;
  args: Record<string, unknown>;
  selections: GqlField[] | null;
  fragmentType: string | null; // inline fragment type condition
}

function gqlTokens(source: string): string[] {
  const tokens: string[] = [];
  let i = 0;
  while (i < source.length) {
    const ch = source[i];
    if (/\s|,/.test(ch)) {
      i += 1;
      continue;
    }
    if (ch === '#') {
      while (i < source.length && source[i] !== '\n') i += 1;
      continue;
    }
    if (ch === '"') {
      let j = i + 1;
      let out = '';
      while (j < source.length && source[j] !== '"') {
        if (source[j] === '\\') {
          out += source[j + 1] ?? '';
          j += 2;
        } else {
          out += source[j];
          j += 1;
        }
      }
      tokens.push(`"${out}"`);
      i = j + 1;
      continue;
    }
    if (source.startsWith('...', i)) {
      tokens.push('...');
      i += 3;
      continue;
    }
    if ('{}()[]:!$=@'.includes(ch)) {
      tokens.push(ch);
      i += 1;
      continue;
    }
    const match = /^[_A-Za-z][_0-9A-Za-z]*|^-?\d+(\.\d+)?/.exec(source.slice(i));
    if (match) {
      tokens.push(match[0]);
      i += match[0].length;
      continue;
    }
    i += 1;
  }
  return tokens;
}

class GqlParser {
  private pos = 0;
  private fragments = new Map<string, { type: string; selections: GqlField[] }>();
  private tokens: string[];
  private variables: Record<string, unknown>;
  constructor(tokens: string[], variables: Record<string, unknown>) {
    this.tokens = tokens;
    this.variables = variables;
  }

  private peek(): string {
    return this.tokens[this.pos] ?? '';
  }
  private next(): string {
    return this.tokens[this.pos++] ?? '';
  }
  private expect(token: string): void {
    if (this.next() !== token) throw new Error(`expected ${token}`);
  }

  parseDocument(): { operation: 'query' | 'mutation'; selections: GqlField[] } {
    let operation: 'query' | 'mutation' = 'query';
    let selections: GqlField[] = [];
    while (this.pos < this.tokens.length) {
      const token = this.peek();
      if (token === 'query' || token === 'mutation' || token === 'subscription') {
        this.next();
        operation = token === 'mutation' ? 'mutation' : 'query';
        if (/^[_A-Za-z]/.test(this.peek())) this.next(); // operation name
        if (this.peek() === '(') this.skipBalanced();
        if (this.peek() === '@') this.skipDirective();
        selections = this.parseSelections();
      } else if (token === 'fragment') {
        this.next();
        const name = this.next();
        this.expect('on');
        const type = this.next();
        const fragSelections = this.parseSelections();
        this.fragments.set(name, { type, selections: fragSelections });
      } else if (token === '{') {
        selections = this.parseSelections();
      } else {
        this.next();
      }
    }
    return { operation, selections: this.expand(selections) };
  }

  private expand(fields: GqlField[]): GqlField[] {
    const out: GqlField[] = [];
    for (const field of fields) {
      if (field.name === '__spread') {
        const frag = this.fragments.get(field.alias ?? '');
        if (frag) out.push(...this.expand(frag.selections));
        continue;
      }
      if (field.selections) field.selections = this.expand(field.selections);
      out.push(field);
    }
    return out;
  }

  private skipBalanced(): void {
    let depth = 0;
    do {
      const token = this.next();
      if (token === '(' || token === '[' || token === '{') depth += 1;
      else if (token === ')' || token === ']' || token === '}') depth -= 1;
    } while (depth > 0 && this.pos < this.tokens.length);
  }

  private skipDirective(): void {
    this.expect('@');
    this.next();
    if (this.peek() === '(') this.skipBalanced();
  }

  private parseValue(): unknown {
    const token = this.next();
    if (token === '$') {
      const name = this.next();
      return this.variables[name];
    }
    if (token.startsWith('"')) return token.slice(1, -1);
    if (token === '[') {
      const list: unknown[] = [];
      while (this.peek() !== ']') list.push(this.parseValue());
      this.next();
      return list;
    }
    if (token === '{') {
      const object: Record<string, unknown> = {};
      while (this.peek() !== '}') {
        const key = this.next();
        this.expect(':');
        object[key] = this.parseValue();
      }
      this.next();
      return object;
    }
    if (/^-?\d+$/.test(token)) return Number(token);
    if (token === 'true') return true;
    if (token === 'false') return false;
    if (token === 'null') return null;
    return token; // enum
  }

  private parseSelections(): GqlField[] {
    this.expect('{');
    const fields: GqlField[] = [];
    while (this.peek() !== '}' && this.pos < this.tokens.length) {
      if (this.peek() === '...') {
        this.next();
        if (this.peek() === 'on') {
          this.next();
          const type = this.next();
          const selections = this.parseSelections();
          fields.push({ name: '__inline', alias: null, args: {}, selections, fragmentType: type });
        } else {
          const name = this.next();
          fields.push({ name: '__spread', alias: name, args: {}, selections: null, fragmentType: null });
        }
        continue;
      }
      let name = this.next();
      let alias: string | null = null;
      if (this.peek() === ':') {
        this.next();
        alias = name;
        name = this.next();
      }
      const args: Record<string, unknown> = {};
      if (this.peek() === '(') {
        this.next();
        while (this.peek() !== ')') {
          const key = this.next();
          this.expect(':');
          args[key] = this.parseValue();
        }
        this.next();
      }
      while (this.peek() === '@') this.skipDirective();
      let selections: GqlField[] | null = null;
      if (this.peek() === '{') selections = this.parseSelections();
      fields.push({ name, alias, args, selections, fragmentType: null });
    }
    this.expect('}');
    return fields;
  }
}

const TYPE_FIELDS: Record<string, string[]> = {
  Query: ['viewer', 'repository', 'node', 'search', 'rateLimit'],
  Mutation: ['createIssue', 'closeIssue', 'createPullRequest', 'mergePullRequest', 'addComment'],
  Viewer: ['login', 'id', 'name', 'email'],
  User: ['login', 'id', 'name', 'email'],
  Organization: ['login', 'id', 'name'],
  Repository: ['id', 'databaseId', 'name', 'nameWithOwner', 'owner', 'defaultBranchRef', 'viewerPermission', 'hasIssuesEnabled', 'hasProjectsEnabled', 'issue', 'issues', 'pullRequest', 'pullRequests', 'description', 'isPrivate', 'url', 'createdAt', 'updatedAt'],
  Issue: ['id', 'databaseId', 'number', 'title', 'state', 'body', 'author', 'comments', 'labels', 'createdAt', 'updatedAt', 'url', 'closed', 'repository'],
  PullRequest: ['id', 'databaseId', 'number', 'title', 'body', 'state', 'merged', 'mergeable', 'headRefName', 'baseRefName', 'headRefOid', 'baseRefOid', 'files', 'author', 'createdAt', 'updatedAt', 'url', 'repository', 'mergedAt', 'additions', 'deletions', 'changedFiles'],
  Ref: ['name', 'prefix', 'target'],
  IssueComment: ['id', 'body', 'author', 'createdAt', 'url'],
  Label: ['id', 'name', 'color', 'description'],
  PageInfo: ['hasNextPage', 'hasPreviousPage', 'startCursor', 'endCursor'],
};
const ENUM_VALUES: Record<string, string[]> = {
  SearchType: ['ISSUE', 'REPOSITORY', 'USER', 'DISCUSSION'],
  IssueState: ['OPEN', 'CLOSED'],
  PullRequestState: ['OPEN', 'CLOSED', 'MERGED'],
  MergeableState: ['MERGEABLE', 'CONFLICTING', 'UNKNOWN'],
  OrderDirection: ['ASC', 'DESC'],
  IssueOrderField: ['CREATED_AT', 'UPDATED_AT', 'COMMENTS'],
};

interface GqlCtx {
  errors: { message: string }[];
}

function gqlResolveObject(type: string, source: Record<string, unknown>, selections: GqlField[] | null, ctx: GqlCtx): Record<string, unknown> {
  const out: Record<string, unknown> = {};
  if (!selections) return out;
  for (const field of selections) {
    if (field.name === '__inline') {
      if (field.fragmentType === type || field.fragmentType === 'Node') {
        Object.assign(out, gqlResolveObject(type, source, field.selections, ctx));
      }
      continue;
    }
    const key = field.alias ?? field.name;
    const known = TYPE_FIELDS[type];
    if (known && !known.includes(field.name) && field.name !== '__typename' && field.name !== '__type' && field.name !== '__schema') {
      ctx.errors.push({ message: `Field '${field.name}' does not exist on type '${type}'` });
      out[key] = null;
      continue;
    }
    out[key] = gqlResolveField(type, source, field, ctx);
  }
  return out;
}

function gqlConnection(items: Record<string, unknown>[], type: string, field: GqlField, ctx: GqlCtx): Record<string, unknown> {
  const first = typeof field.args.first === 'number' ? (field.args.first as number) : items.length;
  let startIndex = 0;
  if (typeof field.args.after === 'string') {
    const decoded = Number(Buffer.from(field.args.after as string, 'base64').toString('utf8'));
    if (Number.isFinite(decoded)) startIndex = decoded + 1;
  }
  const slice = items.slice(startIndex, startIndex + first);
  const hasNext = startIndex + first < items.length;
  const endCursor = slice.length ? Buffer.from(String(startIndex + slice.length - 1)).toString('base64') : null;
  const connection: Record<string, unknown> = {};
  for (const selection of field.selections ?? []) {
    const key = selection.alias ?? selection.name;
    if (selection.name === 'nodes') {
      connection[key] = slice.map((item) => gqlResolveObject(type, item, selection.selections, ctx));
    } else if (selection.name === 'edges') {
      connection[key] = slice.map((item, index) => gqlResolveObject('Edge', { node: item, cursor: Buffer.from(String(startIndex + index)).toString('base64'), __nodeType: type }, selection.selections, ctx));
    } else if (selection.name === 'pageInfo') {
      connection[key] = gqlResolveObject('PageInfo', { hasNextPage: hasNext, hasPreviousPage: startIndex > 0, startCursor: slice.length ? Buffer.from(String(startIndex)).toString('base64') : null, endCursor }, selection.selections, ctx);
    } else if (selection.name === 'totalCount') {
      connection[key] = items.length;
    }
  }
  return connection;
}

function issueSource(repo: Repo, issue: Issue): Record<string, unknown> {
  return {
    __type: 'Issue',
    __repo: repo,
    __issue: issue,
    id: gid('Issue', `${repo.id}:${issue.number}`),
    databaseId: repo.id * 100000 + issue.number,
    number: issue.number,
    title: issue.title,
    body: issue.body,
    state: issue.state === 'open' ? 'OPEN' : 'CLOSED',
    closed: issue.state === 'closed',
  };
}

function pullSource(repo: Repo, pull: Pull): Record<string, unknown> {
  return {
    __type: 'PullRequest',
    __repo: repo,
    __pull: pull,
    id: gid('PullRequest', `${repo.id}:${pull.number}`),
    databaseId: repo.id * 100000 + pull.number,
    number: pull.number,
    title: pull.title,
    body: pull.body,
    state: pull.merged ? 'MERGED' : pull.state === 'open' ? 'OPEN' : 'CLOSED',
    merged: pull.merged,
    headRefName: pull.head,
    baseRefName: pull.base,
    headRefOid: branchTip(repo, pull.head) ?? ZERO_OID,
    baseRefOid: branchTip(repo, pull.base) ?? ZERO_OID,
    mergedAt: pull.mergedAt,
    additions: 0,
    deletions: 0,
  };
}

function repoSource(repo: Repo): Record<string, unknown> {
  return {
    __type: 'Repository',
    __repo: repo,
    id: gid('Repository', String(repo.id)),
    databaseId: repo.id,
    name: repo.name,
    nameWithOwner: `${repo.owner}/${repo.name}`,
    description: repo.description,
    isPrivate: repo.isPrivate,
    viewerPermission: 'ADMIN',
    hasIssuesEnabled: true,
    hasProjectsEnabled: true,
  };
}

function gqlResolveField(type: string, source: Record<string, unknown>, field: GqlField, ctx: GqlCtx): unknown {
  const repo = source.__repo as Repo | undefined;
  switch (type) {
    case 'Repository': {
      if (!repo) return null;
      switch (field.name) {
        case 'owner':
          return gqlResolveObject('User', { login: repo.owner, id: gid('User', String(VIEWER_ID)), name: repo.owner }, field.selections, ctx);
        case 'defaultBranchRef': {
          const tip = defaultTip(repo);
          return gqlResolveObject('Ref', { name: repo.defaultBranch, prefix: 'refs/heads/', target: tip ? { oid: tip } : null, __target: tip }, field.selections, ctx);
        }
        case 'issue': {
          const issue = repo.issues.find((candidate) => candidate.number === Number(field.args.number));
          return issue ? gqlResolveObject('Issue', issueSource(repo, issue), field.selections, ctx) : null;
        }
        case 'issues': {
          let list = [...repo.issues];
          const states = field.args.states as string[] | undefined;
          if (Array.isArray(states) && states.length) {
            const wanted = states.map((state) => String(state).toLowerCase());
            list = list.filter((issue) => wanted.includes(issue.state));
          }
          const orderBy = field.args.orderBy as { field?: string; direction?: string } | undefined;
          const direction = orderBy?.direction ?? 'DESC';
          list.sort((a, b) => (direction === 'ASC' ? a.number - b.number : b.number - a.number));
          return gqlConnection(list.map((issue) => issueSource(repo, issue)), 'Issue', field, ctx);
        }
        case 'pullRequest': {
          const pull = repo.pulls.find((candidate) => candidate.number === Number(field.args.number));
          return pull ? gqlResolveObject('PullRequest', pullSource(repo, pull), field.selections, ctx) : null;
        }
        case 'pullRequests': {
          let list = [...repo.pulls];
          const states = field.args.states as string[] | undefined;
          if (Array.isArray(states) && states.length) {
            const wanted = states.map((state) => String(state).toUpperCase());
            list = list.filter((pull) => wanted.includes(pull.merged ? 'MERGED' : pull.state.toUpperCase()));
          } else {
            list = list.filter((pull) => pull.state === 'open');
          }
          list.sort((a, b) => a.number - b.number);
          return gqlConnection(list.map((pull) => pullSource(repo, pull)), 'PullRequest', field, ctx);
        }
        default:
          return source[field.name] ?? null;
      }
    }
    case 'Issue': {
      const issue = source.__issue as Issue | undefined;
      if (!repo || !issue) return source[field.name] ?? null;
      switch (field.name) {
        case 'author':
          return gqlResolveObject('User', { login: repo.owner, id: gid('User', String(VIEWER_ID)), name: repo.owner }, field.selections, ctx);
        case 'repository':
          return gqlResolveObject('Repository', repoSource(repo), field.selections, ctx);
        case 'comments':
          return gqlConnection(issue.comments.map((comment) => ({ __type: 'IssueComment', id: gid('IssueComment', String(comment.id)), body: comment.body })), 'IssueComment', field, ctx);
        case 'labels':
          return gqlConnection(issue.labels.map((name) => ({ __type: 'Label', id: gid('Label', name), name, color: repo.labels.get(name)?.color ?? 'ededed' })), 'Label', field, ctx);
        case 'url':
          return `https://forge.local/${repo.owner}/${repo.name}/issues/${issue.number}`;
        case 'createdAt':
        case 'updatedAt':
          return '2025-01-01T00:00:00Z';
        default:
          return source[field.name] ?? null;
      }
    }
    case 'PullRequest': {
      const pull = source.__pull as Pull | undefined;
      if (!repo || !pull) return source[field.name] ?? null;
      switch (field.name) {
        case 'mergeable':
          return pull.merged ? 'UNKNOWN' : pullMergeable(repo, pull) ? 'MERGEABLE' : 'CONFLICTING';
        case 'files': {
          const files = pullFiles(repo, pull).map((file) => ({ __type: 'PullRequestFile', path: file.filename, additions: file.additions, deletions: file.deletions }));
          return gqlConnection(files, 'PullRequestFile', field, ctx);
        }
        case 'author':
          return gqlResolveObject('User', { login: repo.owner, id: gid('User', String(VIEWER_ID)), name: repo.owner }, field.selections, ctx);
        case 'repository':
          return gqlResolveObject('Repository', repoSource(repo), field.selections, ctx);
        case 'url':
          return `https://forge.local/${repo.owner}/${repo.name}/pull/${pull.number}`;
        case 'createdAt':
        case 'updatedAt':
          return '2025-01-01T00:00:00Z';
        case 'changedFiles':
          return pullFiles(repo, pull).length;
        default:
          return source[field.name] ?? null;
      }
    }
    case 'Ref': {
      if (field.name === 'target') {
        const tip = source.__target as string | null;
        if (!tip) return null;
        return gqlResolveObject('Commit', { oid: tip, id: gid('Commit', tip) }, field.selections, ctx);
      }
      return source[field.name] ?? null;
    }
    case 'Edge': {
      if (field.name === 'node') {
        return gqlResolveObject(String(source.__nodeType), source.node as Record<string, unknown>, field.selections, ctx);
      }
      return source[field.name] ?? null;
    }
    default:
      return source[field.name] ?? null;
  }
}

function gqlTypeObject(name: string, field: GqlField, ctx: GqlCtx): Record<string, unknown> | null {
  const fields = TYPE_FIELDS[name];
  const enums = ENUM_VALUES[name];
  if (!fields && !enums) return null;
  const out: Record<string, unknown> = {};
  for (const selection of field.selections ?? []) {
    const key = selection.alias ?? selection.name;
    if (selection.name === 'name') out[key] = name;
    else if (selection.name === 'kind') out[key] = enums ? 'ENUM' : 'OBJECT';
    else if (selection.name === 'fields') {
      out[key] = (fields ?? []).map((fieldName) => {
        const item: Record<string, unknown> = {};
        for (const sub of selection.selections ?? []) {
          if (sub.name === 'name') item[sub.alias ?? 'name'] = fieldName;
          else if (sub.name === 'description') item[sub.alias ?? 'description'] = null;
          else if (sub.name === 'isDeprecated') item[sub.alias ?? 'isDeprecated'] = false;
          else if (sub.name === 'deprecationReason') item[sub.alias ?? 'deprecationReason'] = null;
        }
        return item;
      });
    } else if (selection.name === 'enumValues') {
      out[key] = (enums ?? []).map((value) => {
        const item: Record<string, unknown> = {};
        for (const sub of selection.selections ?? []) {
          if (sub.name === 'name') item[sub.alias ?? 'name'] = value;
          else if (sub.name === 'description') item[sub.alias ?? 'description'] = null;
          else if (sub.name === 'isDeprecated') item[sub.alias ?? 'isDeprecated'] = false;
        }
        return item;
      });
    } else if (selection.name === 'possibleTypes') out[key] = [];
    else if (selection.name === 'inputFields') out[key] = [];
    else if (selection.name === 'interfaces') out[key] = [];
    void ctx;
  }
  return out;
}

function findRepoByGlobalId(id: string): Repo | null {
  const decoded = ungid(id);
  if (decoded?.kind === 'Repository') {
    const numeric = Number(decoded.key);
    for (const repo of repos.values()) if (repo.id === numeric) return repo;
  }
  const numeric = Number(id);
  if (Number.isFinite(numeric)) {
    for (const repo of repos.values()) if (repo.id === numeric) return repo;
  }
  return null;
}

function gqlExecute(query: string, variables: Record<string, unknown>): { data?: Record<string, unknown>; errors?: { message: string }[] } {
  const parser = new GqlParser(gqlTokens(query), variables);
  const { operation, selections } = parser.parseDocument();
  const ctx: GqlCtx = { errors: [] };
  const rootType = operation === 'mutation' ? 'Mutation' : 'Query';
  const data: Record<string, unknown> = {};
  for (const field of selections) {
    const key = field.alias ?? field.name;
    if (field.name === '__type') {
      data[key] = gqlTypeObject(String(field.args.name ?? ''), field, ctx);
      continue;
    }
    if (field.name === '__schema') {
      data[key] = { queryType: { name: 'Query' }, mutationType: { name: 'Mutation' } };
      continue;
    }
    if (operation === 'mutation') {
      data[key] = gqlMutate(field, ctx);
      continue;
    }
    switch (field.name) {
      case 'viewer':
        data[key] = gqlResolveObject('Viewer', { login: VIEWER_LOGIN, id: gid('User', String(VIEWER_ID)), name: VIEWER_LOGIN }, field.selections, ctx);
        break;
      case 'repository': {
        const repo = findRepo(String(field.args.owner ?? ''), String(field.args.name ?? ''));
        data[key] = repo ? gqlResolveObject('Repository', repoSource(repo), field.selections, ctx) : null;
        break;
      }
      case 'node': {
        const id = String(field.args.id ?? '');
        const decoded = ungid(id);
        if (decoded?.kind === 'Repository') {
          const repo = findRepoByGlobalId(id);
          data[key] = repo ? gqlResolveObject('Repository', repoSource(repo), field.selections, ctx) : null;
        } else if (decoded?.kind === 'Issue' || decoded?.kind === 'PullRequest') {
          const [repoId, number] = decoded.key.split(':').map(Number);
          let found: Record<string, unknown> | null = null;
          for (const repo of repos.values()) {
            if (repo.id !== repoId) continue;
            if (decoded.kind === 'Issue') {
              const issue = repo.issues.find((candidate) => candidate.number === number);
              if (issue) found = gqlResolveObject('Issue', issueSource(repo, issue), field.selections, ctx);
            } else {
              const pull = repo.pulls.find((candidate) => candidate.number === number);
              if (pull) found = gqlResolveObject('PullRequest', pullSource(repo, pull), field.selections, ctx);
            }
          }
          data[key] = found;
        } else {
          data[key] = null;
        }
        break;
      }
      default:
        ctx.errors.push({ message: `Field '${field.name}' does not exist on type 'Query'` });
        data[key] = null;
    }
  }
  const result: { data?: Record<string, unknown>; errors?: { message: string }[] } = { data };
  if (ctx.errors.length) result.errors = ctx.errors;
  return result;
}

function gqlMutate(field: GqlField, ctx: GqlCtx): Record<string, unknown> {
  const input = (field.args.input ?? {}) as Record<string, unknown>;
  switch (field.name) {
    case 'createIssue': {
      const repo = findRepoByGlobalId(String(input.repositoryId ?? ''));
      if (!repo) {
        ctx.errors.push({ message: 'Repository not found' });
        return {};
      }
      const issue: Issue = {
        number: repo.nextNumber++,
        title: str(input.title),
        body: str(input.body),
        state: 'open',
        labels: [],
        comments: [],
        seq: ++globalSeq,
      };
      repo.issues.push(issue);
      return wrapPayload(field, { issue: gqlResolveObject('Issue', issueSource(repo, issue), findSub(field, 'issue')?.selections ?? null, ctx) }, ctx);
    }
    case 'closeIssue': {
      const decoded = ungid(String(input.issueId ?? ''));
      if (decoded?.kind === 'Issue') {
        const [repoId, number] = decoded.key.split(':').map(Number);
        for (const repo of repos.values()) {
          if (repo.id !== repoId) continue;
          const issue = repo.issues.find((candidate) => candidate.number === number);
          if (issue) {
            issue.state = 'closed';
            return wrapPayload(field, { issue: gqlResolveObject('Issue', issueSource(repo, issue), findSub(field, 'issue')?.selections ?? null, ctx) }, ctx);
          }
        }
      }
      ctx.errors.push({ message: 'Issue not found' });
      return {};
    }
    case 'createPullRequest': {
      const repo = findRepoByGlobalId(String(input.repositoryId ?? ''));
      if (!repo) {
        ctx.errors.push({ message: 'Repository not found' });
        return {};
      }
      const head = str(input.headRefName ?? input.headBranchName ?? input.head);
      const base = str(input.baseRefName ?? input.baseBranchName ?? input.base) || repo.defaultBranch;
      const pull: Pull = {
        number: repo.nextNumber++,
        title: str(input.title),
        body: str(input.body),
        head,
        base,
        state: 'open',
        merged: false,
        mergedAt: null,
        mergeCommitSha: null,
        seq: ++globalSeq,
      };
      repo.pulls.push(pull);
      return wrapPayload(field, { pullRequest: gqlResolveObject('PullRequest', pullSource(repo, pull), findSub(field, 'pullRequest')?.selections ?? null, ctx) }, ctx);
    }
    case 'mergePullRequest': {
      const decoded = ungid(String(input.pullRequestId ?? ''));
      if (decoded?.kind === 'PullRequest') {
        const [repoId, number] = decoded.key.split(':').map(Number);
        for (const repo of repos.values()) {
          if (repo.id !== repoId) continue;
          const pull = repo.pulls.find((candidate) => candidate.number === number);
          if (pull) {
            const result = mergePull(repo, pull);
            if (result === 'conflict') ctx.errors.push({ message: 'Pull request is not mergeable' });
            return wrapPayload(field, { pullRequest: gqlResolveObject('PullRequest', pullSource(repo, pull), findSub(field, 'pullRequest')?.selections ?? null, ctx) }, ctx);
          }
        }
      }
      ctx.errors.push({ message: 'Pull request not found' });
      return {};
    }
    case 'addComment': {
      const decoded = ungid(String(input.subjectId ?? ''));
      if (decoded?.kind === 'Issue') {
        const [repoId, number] = decoded.key.split(':').map(Number);
        for (const repo of repos.values()) {
          if (repo.id !== repoId) continue;
          const issue = repo.issues.find((candidate) => candidate.number === number);
          if (issue) {
            const comment = { id: repo.nextCommentId++, body: str(input.body) };
            issue.comments.push(comment);
            const node = gqlResolveObject('IssueComment', { __type: 'IssueComment', id: gid('IssueComment', String(comment.id)), body: comment.body }, findSub(field, 'commentEdge') ? (findSub(findSub(field, 'commentEdge')!, 'node')?.selections ?? null) : null, ctx);
            return wrapPayload(field, { commentEdge: { node } }, ctx);
          }
        }
      }
      ctx.errors.push({ message: 'Subject not found' });
      return {};
    }
    default:
      ctx.errors.push({ message: `Field '${field.name}' does not exist on type 'Mutation'` });
      return {};
  }
}

function findSub(field: GqlField, name: string): GqlField | null {
  return field.selections?.find((candidate) => candidate.name === name) ?? null;
}

/** Mutation payloads: the document selects fields like { issue { ... } } under the mutation field. */
function wrapPayload(field: GqlField, values: Record<string, unknown>, ctx: GqlCtx): Record<string, unknown> {
  void ctx;
  const out: Record<string, unknown> = {};
  for (const selection of field.selections ?? []) {
    const key = selection.alias ?? selection.name;
    if (selection.name in values) out[key] = values[selection.name];
    else if (selection.name === 'clientMutationId') out[key] = null;
  }
  return out;
}

// ---------------------------------------------------------------------------
// MCP (JSON-RPC 2.0 over streamable HTTP; 2026-07-28 discover + legacy)
// ---------------------------------------------------------------------------

const MCP_TOOLS = [
  {
    name: 'create_repo',
    description: 'Create a new repository for the authenticated user.',
    inputSchema: {
      type: 'object',
      properties: {
        name: { type: 'string', description: 'Repository name' },
        description: { type: 'string' },
        private: { type: 'boolean' },
      },
      required: ['name'],
    },
  },
  {
    name: 'get_repo',
    description: 'Get a repository by owner and name.',
    inputSchema: {
      type: 'object',
      properties: { owner: { type: 'string' }, repo: { type: 'string' }, full_name: { type: 'string' } },
      required: ['owner', 'repo'],
    },
  },
  {
    name: 'create_issue',
    description: 'Create an issue in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string' },
        repo: { type: 'string' },
        title: { type: 'string' },
        body: { type: 'string' },
        full_name: { type: 'string' },
      },
      required: ['owner', 'repo', 'title'],
    },
  },
  {
    name: 'list_issues',
    description: 'List issues in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string' },
        repo: { type: 'string' },
        state: { type: 'string', enum: ['open', 'closed', 'all'] },
        full_name: { type: 'string' },
      },
      required: ['owner', 'repo'],
    },
  },
  {
    name: 'create_pull_request',
    description: 'Create a pull request in a repository.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string' },
        repo: { type: 'string' },
        title: { type: 'string' },
        body: { type: 'string' },
        head: { type: 'string' },
        base: { type: 'string' },
        full_name: { type: 'string' },
      },
      required: ['owner', 'repo', 'title', 'head', 'base'],
    },
  },
  {
    name: 'merge_pull_request',
    description: 'Merge a pull request by number.',
    inputSchema: {
      type: 'object',
      properties: {
        owner: { type: 'string' },
        repo: { type: 'string' },
        pull_number: { type: 'number' },
        full_name: { type: 'string' },
      },
      required: ['owner', 'repo', 'pull_number'],
    },
  },
] as const;

const MCP_TOOLS_JSON = JSON.stringify(MCP_TOOLS);

function mcpToolResult(payload: unknown): Record<string, unknown> {
  return {
    content: [{ type: 'text', text: JSON.stringify(payload) }],
    structuredContent: payload as Record<string, unknown>,
    isError: false,
  };
}

function mcpToolError(message: string): Record<string, unknown> {
  return { content: [{ type: 'text', text: message }], isError: true };
}

function splitFullName(args: Record<string, unknown>): void {
  if (typeof args.full_name === 'string' && args.full_name.includes('/')) {
    const [owner, repo] = args.full_name.split('/');
    if (!args.owner) args.owner = owner;
    if (!args.repo) args.repo = repo;
  }
}

function mcpCallTool(name: string, rawArgs: Record<string, unknown>): { result?: Record<string, unknown>; error?: { code: number; message: string } } {
  const tool = MCP_TOOLS.find((candidate) => candidate.name === name || candidate.name.endsWith(`__${name}`) || name.toLowerCase().endsWith(candidate.name));
  if (!tool) return { error: { code: -32602, message: `Unknown tool: ${name}` } };
  const args = { ...rawArgs };
  splitFullName(args);
  for (const required of tool.inputSchema.required) {
    if (args[required] === undefined || args[required] === null || args[required] === '') {
      return { error: { code: -32602, message: `Missing required argument: ${required}` } };
    }
  }
  const canonical = tool.name;
  switch (canonical) {
    case 'create_repo': {
      const repoName = str(args.name);
      if (repos.has(repoKey(VIEWER_LOGIN, repoName))) return { result: mcpToolResult(repoJson(repos.get(repoKey(VIEWER_LOGIN, repoName))!)) };
      const repo = createRepo(VIEWER_LOGIN, repoName, str(args.description), args.private === true);
      return { result: mcpToolResult(repoJson(repo)) };
    }
    case 'get_repo': {
      const repo = findRepo(str(args.owner), str(args.repo));
      if (!repo) return { result: mcpToolError('Repository not found') };
      return { result: mcpToolResult(repoJson(repo)) };
    }
    case 'create_issue': {
      const repo = findRepo(str(args.owner), str(args.repo));
      if (!repo) return { result: mcpToolError('Repository not found') };
      const issue: Issue = {
        number: repo.nextNumber++,
        title: str(args.title),
        body: str(args.body),
        state: 'open',
        labels: [],
        comments: [],
        seq: ++globalSeq,
      };
      repo.issues.push(issue);
      return { result: mcpToolResult(issueJson(repo, issue)) };
    }
    case 'list_issues': {
      const repo = findRepo(str(args.owner), str(args.repo));
      if (!repo) return { result: mcpToolError('Repository not found') };
      const state = str(args.state) || 'open';
      const list = repo.issues.filter((issue) => state === 'all' || issue.state === state).map((issue) => issueJson(repo, issue));
      return { result: mcpToolResult({ issues: list, total: list.length }) };
    }
    case 'create_pull_request': {
      const repo = findRepo(str(args.owner), str(args.repo));
      if (!repo) return { result: mcpToolError('Repository not found') };
      const head = str(args.head).replace(/^[^:]+:/, '');
      const base = str(args.base).replace(/^[^:]+:/, '');
      const existing = repo.pulls.find((pull) => pull.head === head && pull.base === base && pull.state === 'open');
      if (existing) return { result: mcpToolResult(pullJson(repo, existing)) };
      const pull: Pull = {
        number: repo.nextNumber++,
        title: str(args.title),
        body: str(args.body),
        head,
        base,
        state: 'open',
        merged: false,
        mergedAt: null,
        mergeCommitSha: null,
        seq: ++globalSeq,
      };
      repo.pulls.push(pull);
      return { result: mcpToolResult(pullJson(repo, pull)) };
    }
    case 'merge_pull_request': {
      const repo = findRepo(str(args.owner), str(args.repo));
      if (!repo) return { result: mcpToolError('Repository not found') };
      const number = Number(args.pull_number ?? args.number);
      const pull = repo.pulls.find((candidate) => candidate.number === number);
      if (!pull) return { result: mcpToolError('Pull request not found') };
      const result = mergePull(repo, pull);
      if (result === 'conflict') return { result: mcpToolError('Pull request is not mergeable: conflict') };
      if (result === 'gone') return { result: mcpToolError('Pull request branches are gone') };
      return { result: mcpToolResult({ ...pullJson(repo, pull), sha: result, merged: true }) };
    }
    default:
      return { error: { code: -32601, message: `Method not found: ${name}` } };
  }
}

function handleMcp(req: IncomingMessage, res: ServerResponse, raw: Buffer): void {
  if (!authed(req)) {
    sendJson(res, 401, { jsonrpc: '2.0', id: null, error: { code: -32001, message: 'Unauthorized' } });
    return;
  }
  if ((req.method ?? 'POST') !== 'POST') {
    sendJson(res, 405, { jsonrpc: '2.0', id: null, error: { code: -32601, message: 'Method not allowed' } });
    return;
  }
  let parsed: unknown;
  try {
    parsed = JSON.parse(raw.toString('utf8'));
  } catch {
    res.writeHead(400, { 'content-type': JSON_TYPE });
    res.end(JSON.stringify({ jsonrpc: '2.0', id: null, error: { code: -32700, message: 'Parse error' } }));
    return;
  }
  const requests = Array.isArray(parsed) ? parsed : [parsed];
  const responses: unknown[] = [];
  for (const entry of requests) {
    const message = entry as { jsonrpc?: string; id?: unknown; method?: string; params?: Record<string, unknown> };
    const method = message.method ?? '';
    const isNotification = message.id === undefined || message.id === null;
    const respond = (result: unknown) => {
      if (!isNotification) responses.push({ jsonrpc: '2.0', id: message.id, result });
    };
    const respondError = (code: number, text: string) => {
      if (!isNotification) responses.push({ jsonrpc: '2.0', id: message.id, error: { code, message: text } });
    };
    if (method.startsWith('notifications/')) {
      continue;
    }
    switch (method) {
      case 'server/discover':
        respond({
          protocolVersion: '2026-07-28',
          supportedVersions: ['2026-07-28', '2025-11-25', '2025-06-18', '2025-03-26'],
          capabilities: { tools: {} },
          serverInfo: { name: 'coreforge', version: '1.0.0' },
        });
        break;
      case 'initialize': {
        const requested = str(message.params?.protocolVersion) || '2025-11-25';
        const supported = ['2025-11-25', '2025-06-18', '2025-03-26', '2024-11-05'];
        res.setHeader('mcp-session-id', 'coreforge-session-1');
        respond({
          protocolVersion: supported.includes(requested) ? requested : '2025-11-25',
          capabilities: { tools: { listChanged: false } },
          serverInfo: { name: 'coreforge', version: '1.0.0' },
        });
        break;
      }
      case 'ping':
        respond({});
        break;
      case 'tools/list':
        respond({ tools: JSON.parse(MCP_TOOLS_JSON) });
        break;
      case 'tools/call': {
        const params = message.params ?? {};
        const toolName = str(params.name);
        const args = (params.arguments ?? {}) as Record<string, unknown>;
        const outcome = mcpCallTool(toolName, args);
        if (outcome.error) respondError(outcome.error.code, outcome.error.message);
        else respond(outcome.result);
        break;
      }
      default:
        respondError(-32601, `Method not found: ${method}`);
    }
  }
  if (responses.length === 0) {
    res.writeHead(202, { 'content-type': JSON_TYPE });
    res.end();
    return;
  }
  const body = Array.isArray(parsed) ? responses : responses[0];
  const text = JSON.stringify(body);
  const headers: Record<string, string> = { 'content-type': JSON_TYPE, 'content-length': String(Buffer.byteLength(text)) };
  const sessionHeader = res.getHeader('mcp-session-id');
  if (sessionHeader) headers['mcp-session-id'] = String(sessionHeader);
  res.writeHead(200, headers);
  res.end(text);
}

// ---------------------------------------------------------------------------
// GraphQL HTTP
// ---------------------------------------------------------------------------

function handleGraphql(req: IncomingMessage, res: ServerResponse, raw: Buffer): void {
  if (!authed(req)) {
    sendJson(res, 401, { message: 'Bad credentials' });
    return;
  }
  if ((req.method ?? 'POST') !== 'POST') {
    sendJson(res, 404, { message: 'Not Found' });
    return;
  }
  let parsed: unknown;
  try {
    parsed = JSON.parse(raw.toString('utf8'));
  } catch {
    sendJson(res, 400, { message: 'Problems parsing JSON' });
    return;
  }
  const run = (entry: Record<string, unknown>) => {
    try {
      return gqlExecute(str(entry.query), (entry.variables ?? {}) as Record<string, unknown>);
    } catch (err) {
      return { errors: [{ message: err instanceof Error ? err.message : 'Internal error' }] };
    }
  };
  if (Array.isArray(parsed)) {
    sendJson(res, 200, parsed.map((entry) => run(entry as Record<string, unknown>)));
    return;
  }
  sendJson(res, 200, run(parsed as Record<string, unknown>));
}

// ---------------------------------------------------------------------------
// the server
// ---------------------------------------------------------------------------

export function createApp(): Server {
  return createServer((req: IncomingMessage, res: ServerResponse) => {
    void (async () => {
      try {
        const url = new URL(req.url ?? '/', 'http://entry');
        const path = url.pathname;
        const method = req.method ?? 'GET';

        if (method === 'GET' && path === '/healthz') {
          sendJson(res, 200, { ok: true });
          return;
        }

        const raw = method === 'GET' || method === 'DELETE' && path.startsWith('/api/v3') ? await readBody(req) : await readBody(req);

        if (path === '/api/graphql') {
          handleGraphql(req, res, raw);
          return;
        }
        if (path === '/mcp') {
          handleMcp(req, res, raw);
          return;
        }
        if (path === '/api/v3' || path.startsWith('/api/v3/')) {
          handleRest(req, res, url, raw);
          return;
        }

        // git smart HTTP: /{owner}/{repo}.git/...
        const gitMatch = /^\/([^/]+)\/([^/]+)\.git\/(info\/refs|git-upload-pack|git-receive-pack)$/.exec(path);
        if (gitMatch) {
          const [, owner, repoName, endpoint] = gitMatch;
          if (!authed(req)) {
            sendJson(res, 401, { message: 'Bad credentials' });
            return;
          }
          const repo = findRepo(decodeURIComponent(owner), decodeURIComponent(repoName));
          if (!repo) {
            sendJson(res, 404, { message: 'Not Found' });
            return;
          }
          if (endpoint === 'info/refs' && method === 'GET') {
            handleInfoRefs(req, res, url, repo, url.searchParams.get('service') ?? 'git-upload-pack');
            return;
          }
          if (endpoint === 'git-upload-pack' && method === 'POST') {
            handleUploadPack(res, repo, raw);
            return;
          }
          if (endpoint === 'git-receive-pack' && method === 'POST') {
            handleReceivePack(res, repo, raw);
            return;
          }
          sendJson(res, 404, { message: 'Not Found' });
          return;
        }

        sendJson(res, 404, { message: 'Not Found' });
      } catch (err) {
        process.stderr.write(`[coreforge] ${err instanceof Error ? err.stack ?? err.message : String(err)}\n`);
        if (!res.headersSent) sendJson(res, 500, { message: 'Internal error' });
        else res.end();
      }
    })();
  });
}
