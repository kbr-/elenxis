# Tailor booking requests

`text.md` holds an example brief from a tailor who wants a booking page. The generated key
identifies deliberate gaps and imperfections by ledger row. The [table](table.md) compares matching
rows and false alarms across the arms.

Run the commands from the Elenxis project directory. For the backend used in the table, configure
Codex with GPT-6.2 Sol at medium effort. A Codex session supplies those defaults. When using
`SPEC_TOOLS_HOST` to run Codex on another machine, set `SPEC_TOOLS_CHECK_HOST` and
`SPEC_TOOLS_CHECK_LAUNCHER` for the ledger arm as described in the
[reference](../../../docs/reference.md).

```sh
lake build spec-tools
trial=$(mktemp -d)
cp examples/owners/tailor/text.md "$trial/text.md"
lake exe spec-tools synthetic owners-variants "$trial" 20261121 12 2 vocab=tailor
cmp examples/owners/tailor/key.jsonl "$trial/key.jsonl"
lake exe spec-tools synthetic gapsrun 20261121 5 "$trial" default
lake exe spec-tools synthetic run "$trial" default default baseline
lake exe spec-tools synthetic run "$trial" default default ledger
lake exe spec-tools synthetic run "$trial" default default tools
lake exe spec-tools synthetic owners-table "$trial" 12 codex-input
```

The variant generation and key are deterministic. Model calls can produce different findings and
usage on a repeat run. The table's time is the recorded model or agent duration.
