# A salon's first booking call

[The conversation](text.md) is a fictional first call between Mae, who owns the salon, and Rob, who
is developing its booking page. Mae first says that two no-shows block an online booking for a
child's haircut, then reads a note that gives the limit as four. She also says that customers with
“a few” unpaid visits should call the salon, leaving the exact threshold open. Both cases call for a
decision from the owner before the booking rules are finalized.

The benchmark generates variants of a Lean specification, a Python implementation and property tests
for this dialogue. Some variants deliberately share a blind spot across all three artifacts. For
example, variant 3 marks the staff exception to the no-show rule for evening bookings as a planted
blind spot. The [scoring key](key.jsonl) identifies the planted gaps and ambiguities by ledger row.
The two variants without planted blind spots still contain the ambiguities in the dialogue.

The [results table](table.md) shows matches and false alarms for `gaps`, an agent reading the files,
an agent with access to the tools, and an agent given the tools' reports before it starts. Tells
scored the packaged dialogue 1.00 against a threshold of 0.95.

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
