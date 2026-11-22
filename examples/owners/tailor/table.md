# Tailor owner experiment

Tells scored the input at 1.00 against the 0.95 threshold. The table scores findings by ledger row.
A row match does not verify the description of the planted defect. Time is the recorded model or
agent run time, and the tools arm prepares reports before its agent starts. Tokens include the agent
and its checks, using Codex's input totals, which already include cache reads.

| Row | Runs | Blind spots found | Imperfections found | False alarms | Time per run | Tokens per run | Output tokens per run | Failed runs |
|---|---|---|---|---|---|---|---|---|
| `gaps` alone | 10 | 30 of 30 | 20 of 20 | 0 | 27 s | 19422 | 1196 | 0 |
| `gaps` on the no-plant variants | 2 | 0 of 0 | 4 of 4 | 8 | 23 s | 19127 | 997 | 0 |
| baseline arm | 12 | 30 of 30 | 12 of 24 | 0 | 69 s | 266730 | 2521 | 0 |
| ledger arm | 12 | 30 of 30 | 21 of 24 | 8 | 119 s | 602362 | 5643 | 0 |
| tools arm | 12 | 30 of 30 | 23 of 24 | 4 | 92 s | 349159 | 4855 | 0 |
