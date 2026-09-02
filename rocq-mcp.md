## rocq-mcp Configuration

### What is rocq-mcp?

[rocq-mcp](https://github.com/llm4rocq/rocq-mcp) is an MCP (Model Context Protocol) server that gives Claude Code interactive access to the Rocq (Coq) proof assistant. It enables starting proof sessions, running tactics step-by-step, and inspecting goals — all without leaving the conversation.

Under the hood it communicates with `pet` (Petanque), the Rocq prover's JSON-RPC API.

### Installation

Installed via `pipx` from Git:

```
pipx install git+https://github.com/llm4rocq/rocq-mcp.git
```

Current version: **0.1.0** (commit `0feb365`).

### Wrapper script

The `rocq-mcp` binary needs `rocq` and `pet` on `PATH`. Since the project uses a local opam switch, a wrapper script at `~/.local/bin/rocq-mcp-wrapper` prepends the switch to `PATH`:

```bash
#!/bin/bash
# Point this at the project's local opam switch. From the project root:
#   export PATH="$(pwd)/_opam/bin:$PATH"
export PATH="$OPAM_SWITCH_PREFIX/bin:$PATH"
exec rocq-mcp "$@"
```

### Claude Code configuration

The MCP server is declared in the **project-level** Claude Code settings for
this project (`.claude/projects/<project>/settings.json`):

```json
{
  "mcpServers": {
    "rocq-mcp": {
      "command": "~/.local/bin/rocq-mcp-wrapper"
    }
  }
}
```

> An older entry in `~/.claude.json` may point directly at `~/.local/bin/rocq-mcp` with an explicit `env.PATH`. The project-level setting (using the wrapper) takes precedence.

### Available tools

| Tool | Purpose |
|---|---|
| `rocq_start_proof` | Open a proof session for a named theorem in a `.v` file |
| `rocq_run_tactic` | Execute a tactic on the current proof state |
| `rocq_get_goals` | Inspect current goals |
| `rocq_get_state_at_position` | Get proof state at a file position |
| `rocq_get_file_toc` | List definitions/lemmas in a file |
| `rocq_get_premises` | Query available premises |
| `rocq_search` | Run `Search` queries |
| `rocq_parse_ast` | Parse Rocq AST |

### Typical workflow

1. The theorem must exist in a `.v` file (even as `Admitted.`)
2. `rocq_start_proof` opens a session (returns initial goals)
3. `rocq_run_tactic` applies tactics one at a time
4. When `Proof finished: True` is returned, the proof is complete
