# Backends

A question the tools can't decide goes to a model through a configurable backend. Keep backend
selection outside specifications: set `SPEC_TOOLS_BACKEND` to the path of a JSON file, then use
`SpecTools.Gaps.runConfigured ledger prose` (with `requirements := true` for unproved requirements).
Missing or malformed configuration fails before launching a process.

The examples' configuration, [`examples/backend.json`](../examples/backend.json), runs Opus at
medium reasoning effort through Claude Code's login:

```json
{"adapter": "claude-code", "model": "claude-opus-5-5", "effort": "medium", "dataGoesTo": "Anthropic, through the Claude Code login"}
```

For Codex using its existing login:

```json
{"adapter": "codex", "model": "YOUR_MODEL", "effort": "medium", "dataGoesTo": "Codex using the configured account"}
```

## Fields

- `adapter`: `claude-code`, `codex` or `command`.
- `model`: an opaque string passed to the harness; the checker holds no provider-specific allowlist.
- `effort` (optional): the reasoning effort, passed as it is written: Claude Code's `--effort`
  (`low`, `medium`, `high`, `xhigh`, `max`), Codex's `model_reasoning_effort` setting, and the
  `effort` field of a command adapter's request. Without it the harness uses its own default; an
  empty value is refused.
- `dataGoesTo`: documents the actual destination. It neither authorizes a call nor changes routing:
  the planner's allowlist compares adapter configuration and model, and changing this note can't
  change that decision or the invocation (`plan_ignores_destination` in `SpecTools/ModelProofs`).

The `ask` and `clauses` CLI commands accept `configured` in place of `HARNESS`; their `MODEL`
argument overrides the configured model and keeps the configured effort. Their explicit
`codex MODEL` and `claude-code MODEL` forms remain available. Synthetic runs use the configured
adapter and effort with the agent and tool models their command line names.

## Command adapters

For any other harness, provider or locally hosted model, configure an adapter executable:

```json
{"adapter": "command", "command": "/absolute/path/to/adapter", "args": [], "model": "YOUR_MODEL", "dataGoesTo": "local inference server"}
```

The executable receives its configured arguments followed by `request.json`, relative to the fresh
working directory. That UTF-8 JSON file contains `protocol: 1`, `model`, `prompt`, `schema`,
`timeoutMs`, `mode` (`question` or `agent`), `tools` (the requested agent tool policy) and, when
configured, `effort`. Arguments are passed literally without a shell. Return the answer itself as
JSON on stdout, diagnostics on stderr, and a nonzero status on failure. The shared checker validates
the answer against `schema`; a backend need not support constrained JSON generation. The executable
adapts this contract to its chosen service or local inference engine, keeping credentials in its own
deployment configuration.

**Adapter configuration is trusted executable configuration.** Command adapters must enforce the
requested mode and tool restrictions; the generic launcher does not sandbox arbitrary commands. The
built-in Codex and Claude adapters keep their sandbox and tool restrictions (a question to Claude
Code runs with `--safe-mode` and no tools, one to Codex in a read-only sandbox: theorems
`claude_question_cannot_act` and `codex_question_read_only`). Switching to another adapter never
grants data access or permission to contact its destination.
