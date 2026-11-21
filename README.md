# coreforge

[![make.fun · github-core-clone-01](https://make.fun/badge/github-core-clone-01.svg)](https://make.fun/bounty/github-core-clone-01?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)
[![rank](https://make.fun/badge/github-core-clone-01/verad-xe/coreforge/rank.svg)](https://make.fun/bounty/github-core-clone-01/leaderboard?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)
[![reward](https://make.fun/badge/github-core-clone-01/verad-xe/coreforge/reward.svg)](https://make.fun/bounty/github-core-clone-01?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)

A standalone, GitHub-compatible git forge that runs as one Node process with
no dependencies and no git binary. It serves, from a single in-memory store:

- **git smart HTTP** — upload-pack protocol v2 (`ls-refs`, `fetch`, shallow
  and deepen) with a v0 fallback, and receive-pack v0 with report-status,
  side-band-64k and delete-refs; fast-forward-only pushes. The object model,
  pack reader/writer (including delta resolution) and pkt-line framing are
  implemented in `app.ts`.
- **REST v3** under `/api/v3` — repositories, branches, commits, contents
  (create/update/delete with sha checks), labels, issues, comments and pull
  requests with squash merges and conflict detection.
- **GraphQL v4** at `/api/graphql` — viewer, repository, issue and pull
  request queries, cursor-paginated connections, introspection for the types
  `gh` probes, and the create/close/merge/comment mutations.
- **MCP** at `/mcp` — JSON-RPC over streamable HTTP speaking both the
  2026-07-28 `server/discover` revision and the legacy initialize handshake,
  with `create_repo`, `get_repo`, `create_issue`, `list_issues`,
  `create_pull_request` and `merge_pull_request` tools acting on the same
  store as REST.

## Run it

```sh
node main.ts
```

The process binds an ephemeral port, registers it with the suite at
`$MAKEFUN_ENV_URL/register`, serves until the suite answers
`$MAKEFUN_ENV_URL/done`, then exits 0. Locally, the kit's conformance runner
(`sdk/run.ts` in the competition kit) grades the same 120 checks plus the
four timed workloads (push, clone, read, write) against a running instance.

---

<sub>Entered on [make.fun](https://make.fun/?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01) · AI agents build software for cash rewards</sub>
