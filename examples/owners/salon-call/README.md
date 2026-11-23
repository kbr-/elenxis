# A salon's first booking call

[The conversation](text.md) is a fictional first call between Mae, who owns the salon, and Rob, who
is developing its booking page. Mae gives conflicting limits for children's haircuts and leaves the
unpaid-visit threshold open. The generated key identifies these imperfections and the planted blind
spots by ledger row. The [table](table.md) compares matching rows and false alarms across the arms.
Tells scored the packaged dialogue 1.00 against a threshold of 0.95.

Run these commands from the Elenxis project directory. The table uses Codex with GPT-6.2 Sol at
medium effort. A Codex session supplies those defaults. If `SPEC_TOOLS_HOST` runs Codex on another
machine, set `SPEC_TOOLS_CHECK_HOST` and `SPEC_TOOLS_CHECK_LAUNCHER` for the ledger arm as described
in the [reference](../../../docs/reference.md).

```sh
lake build spec-tools
trial=$(mktemp -d)
cp examples/owners/salon-call/text.md "$trial/text.md"
lake exe spec-tools synthetic owners-variants "$trial" 20261120 12 2 vocab=salon
cmp examples/owners/salon-call/key.jsonl "$trial/key.jsonl"
lake exe spec-tools synthetic gapsrun 20261120 5 "$trial" default
lake exe spec-tools synthetic run "$trial" default default baseline
lake exe spec-tools synthetic run "$trial" default default ledger
lake exe spec-tools synthetic run "$trial" default default tools
lake exe spec-tools synthetic owners-table "$trial" 12 codex-input
```

The variant generation and key are deterministic. Model calls can give different findings and usage
on a repeat run. The table reports recorded model or agent duration. A hit means the finding matched
a ledger row. Read the findings to assess their meaning.
