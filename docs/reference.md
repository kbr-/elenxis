# Reference

## The ledger

A ledger is a `List SpecTools.Ledger.Row`, written in Lean beside the specification:

```lean
import SpecTools.Audit
import SpecTools.GapsRun

def ledger : List SpecTools.Ledger.Row := [
  { id := "prerelease", source := "DESIGN.md, Tiers",
    clause := "a base whose version carries a pre-release suffix ... admits no space",
    theorems := [``prerelease_admits_none],
    evidence := [⟨``prerelease_admits_none, ``wit_prerelease, .inhabited⟩],
    tests := ["test_prerelease_admits_none"] } ]

#eval SpecTools.Audit.run ledger `Root
```

A row names the theorems stating its clause, evidence about their premise domains, and the tests
covering it in the implementation's language. An `evidence` binding names the subject theorem, the
evidence theorem and its kind. For a statement `∀ n : Nat, n < 18 → P n`, an `.inhabited`
certificate proves `∃ n : Nat, ∃ _h : n < 18, True`. An `.inconsistent` certificate proves the
negation of that domain. Each certificate needs an accepted axiom inventory. Legacy `witnesses`
entries still claim declarations for the audit's coverage check. Upgrade them by binding a
certificate of the exact domain to each relevant theorem.

A row's `status` is `covered` (the default), `uncovered REASON`, `provisional DECISION` or
`accepted DECISION`. A ledger kept as a Markdown table instead is read by `SpecTools.LedgerTable`;
its header row is `| id | clause | source | theorems | witnesses | tests | status |`.

## The audit's verdicts

`SpecTools.Audit.run ledger Root` judges every row from its theorems' statements, axioms and
hypotheses, and prints one verdict per row:

- **proved**: every named theorem exists and rests only on `propext`, `Classical.choice` and
  `Quot.sound`. Each theorem with propositional premises has checked inhabitation evidence in that
  row;
- **unknown nonvacuity**: a theorem's premises lack a checked inhabitation certificate;
- **inconsistent premises**: a checked certificate refutes the premise domain of a theorem;
- **conditional**: a theorem rests on another axiom;
- **not stated**: the row names no theorem;
- **specified (unproved)**: in requirements mode, the row's declarations are proposition
  definitions, well formed and not proved.

It fails, rather than reports, on what makes the report itself wrong: a repeated identifier, a named
theorem that is no theorem, a theorem under `Root` no row claims, a source module it doesn't import.
With a digest file, rows whose clause, declarations and evidence results are unchanged are not
judged again. An older digest format triggers a fresh audit.

## Specifying before implementing

For a specification written before its implementation, opt into requirement declarations:

```lean
def obligation (n : Nat) : Prop := n + 0 = n

def requirements : List SpecTools.Ledger.Row := [
  { id := "identity", clause := "adding zero preserves the input",
    theorems := [``obligation] } ]

#eval SpecTools.Audit.run requirements `Spec (requirements := true)
#eval SpecTools.Gaps.runConfigured requirements prose (requirements := true)
```

This mode reads parameterized proposition definitions and labels them **specified (unproved)**. The
`theorems` field supplies the declaration names in either mode. Requirement declarations cannot
receive a proved verdict. Witness declarations must remain proved theorems. Empty ledgers, missing
declarations, non-propositions, unsafe or unavailable bodies and unaccepted axioms fail requirement
admission; the report lists invalid declarations across each row. Expose a definition's body with
the module's appropriate public interface or `import all` when the module system hides it. The gaps
model reads the requirement bodies and judges their coverage; admitting a declaration does not
establish its adequacy or truth. The default mode continues to require theorem declarations.

## Gaps

`#eval SpecTools.Gaps.runConfigured ledger prose` prints the four gaps between the prose and the
statements, each naming its row: `uncovered` (a clause no statement establishes), `too weak` (a
statement weaker than its clause), `undecided` (a case the prose leaves open that the statements
decide), `extra` (a statement the prose neither asks for nor implies). Lean reports a checked
contradiction in a theorem's premises and prints missing nonvacuity evidence separately. The model
proposes issues and sees checked premise evidence apart from the clause statements. A proposal
naming an unknown row or kind is printed as refused, and an answer that breaks the schema is
rejected.

## Adversarial admission

`adversarial_claim ENTRY in theorem ...` (`SpecTools.Adversarial`) admits a theorem only with a
witness inhabiting the existential closure of its binders and, for each attack, a mutant
implementation with a proof that the same law fails for it. A law that a do-nothing or constant
implementation also satisfies has no such proof, so its theorem is never admitted; the check runs
before the theorem's own proof is elaborated. Set `specTools.adversarial.root` in the audit module
to require this of every source theorem under that root.

## Tests

`SpecTools.Tests.run rows adapter module testFile` reports a test a row names that the test file
doesn't define, and a guard of the implementation whose removal no test notices. The Python adapter
(`adapters/python_guards.py`) replaces each disjunct of a refusing `if` (and each term of a sum
inside one) by `False` (or `0`) in a copy and runs the named tests with pytest.

An executable fixture can supply the optional `replay` action to `Tests.run`. The loans fixture
sends the same initial state and operation sequence to its Lean and Python implementations. Replay
compares acceptance and the resulting state at each step, reports the first difference, and fails on
an incomplete or invalid response. Run the check from the Elenxis project directory:

```sh
SPEC_TOOLS_TESTS=1 lake env lean fixtures/loans/Loans.lean
```

## Review before writing the specification

Use `spec-tools draft-check INVENTORY DRAFT` to check the complete source inventory locally. Both
files are JSON arrays. Each inventory object has an `id` and `clause`. Each draft object has a
`source` with the same fields and an `evidence` object. Use
`{"contract":{"name":"Geometry.keep","statement":"∀ eye, keep eye = eye"}}` for a planned Lean
declaration, or
`{"externalCheck":{"reason":"physical optics","acceptance":"verify fusion in the glasses"}}` for
external evidence.

Run `spec-tools draft-review HARNESS MODEL PROSE INVENTORY DRAFT` for semantic review. An incomplete
draft fails before the model call. The complete draft and prose go to one call, and findings or
malformed proposals cause a nonzero exit. This review checks the written draft statements without
elaborating them as Lean definitions.

After writing the specification, `SpecTools.Gaps.checkDraftContracts` checks that the supplied
bindings cover the approved draft's contract names exactly. It then calls
`SpecTools.Audit.checkApprovedContracts` to compare actual definitions with separately elaborated
baselines by type and proposition body. The caller supplies the baselines from the approved draft.

## Clauses

`spec-tools clauses HARNESS MODEL PROSE` has a model extract a prose file's clauses twice, blind to
each other, and prints the differences as rows to add.

## The model interface

`SpecTools.Model`, `SpecTools.BackendConfig` and `SpecTools.Schema`: a question goes to a configured
backend ([backends.md](backends.md)), and the answer is checked against a JSON schema subset
(`type`, `properties`, `required`, `additionalProperties`, `items`, `enum`; any other keyword is
refused). The effects sit in a `Runner`, so tests script it and reach no model.

## Usage and trace

Every call returns what it used (`SpecTools.Usage`): input, cache-write, cache-read and output
tokens, turns, wall time and the harness's API time, and the list price where the harness reports
one. Each count is known or unknown, never a 0 standing for a count no report gave, and a total over
calls keeps how many lacked each count. The counts come from Claude Code's JSON report, from Codex's
`--json` events (the last turn's `usage`) and from a command adapter's `usage.json`. The list price
is the harness's (Claude Code's `total_cost_usd`); a subscription's user doesn't pay it, so it is
printed as a list price. Every command that asks a model (`gaps`, `clauses`, `draft-review`, `ask`)
ends with a line such as

```text
usage: 1 calls; tokens input 2, cache write 2223, cache read 649, output 4; 5196 ms; claude-code claude-opus-5-5, effort medium; list price $0.0180018 (not billed under a subscription)
```

`synthetic run` saves each run's usage (its agent's and its tools') in its results file and prints
totals per arm; `synthetic gapsrun` prints the batch's total. Two variables, set outside any
specification, record more:

- `SPEC_TOOLS_USAGE=FILE`: each call appends its usage to FILE, one JSON line;
- `SPEC_TOOLS_TRACE=DIR`: each call appends one JSON line to `DIR/calls-PID.jsonl` with its tool,
  backend, prompt, schema, raw answer or failure, and usage. Unset, nothing is written, since a
  prompt carries the target's text; a directory that can't be written fails before the call.

An explicit `SPEC_TOOLS_BACKEND` configuration selects the adapter, model and effort. When no file
is selected, a nonempty `CODEX_THREAD_ID` selects the calling Codex account with GPT-6.2 Sol at
medium effort. Use `configured default` where a command takes both a harness and a model.
`owners-suite` and `owners-fidelity` use this selection for their model calls.

`SPEC_TOOLS_HOST=HOST` runs the harness over SSH while Lean runs on the calling machine. Codex
transfers its schema and structured answer through an isolated directory under `/tmp`. Agent runs
also transfer the variant's working files. Set `CODEX_HOME` to the existing Codex auth directory on
the model host when that login lives outside the default directory. Pass these variables through the
launcher as part of the command's environment. Claude calls retain their existing transport.

For a remote Codex `synthetic run` with the `ledger` arm, set `SPEC_TOOLS_CHECK_HOST` to the SSH
name of the machine holding the original variant and `SPEC_TOOLS_CHECK_LAUNCHER` to the absolute
path of that machine's protected launcher. The model host must be able to connect to this host over
SSH. The agent can request `audit`, `tests`, `gaps` or `clauses` through the Elenxis MCP server with
empty arguments. Each request runs on the original variant, whose lock serializes requests from
independent connections. The result's `check_events` records attempts and terminal statuses. An
agent can skip a check or submit findings after a failed check.

## The synthetic evaluation

`spec-tools score-observations KEY FINDINGS` reads two JSON objects with `"version": 1`. The
protected key holds a `plants` array. Each plant has a unique natural-number `id`, a unique nonempty
`property` identifier, a `location` of the form `{"rule": 2, "part": "exception"}`, and a `kind`
name (`uncovered`, `too weak`, `undecided` or `extra`). Findings go in a `findings` array. Each
finding has an `evidenceId` and may supply a `location`, `property` and `kind`. Reuse an evidence ID
for repeated records from the same source observation. Conflicting scoring fields under that ID
exclude the observation.

The report lists exact observed key locations as `located` and plant IDs matched by location,
property and kind as `classified`. It returns `unknown` for `distinguished` and `humanReviewed` at
this entry point. Both input files must use version 1.

Use `#score_journal` in Lean to check directional witnesses and include independent human decisions:

```lean
import SpecTools.ScoreEvidence

#score_journal "key.json" "findings.json" with "review.json"
```

Put the domain definitions and evidence theorems in the same Lean environment and run the file with
`lake env lean`. For each property with a formal criterion, add an entry to the protected key's
`formalBindings` array with `property`, `reference` and `candidate` declaration names, and a
`direction` of `admitsExtra` or `rejectsRequired`. A finding can supply a `formal` object containing
`observation` and `theoremName`. Lean checks that the theorem proves `BoundDistinction` for the
key's exact binding and the named observation. The report lists the accepted direction, theorem and
observation. Unsupported or absent evidence leaves the distinction unknown.

The optional independent review file contains `{"version": 1, "decisions": [...]}`. Each decision
has an `evidenceId`, a `reviewer` supplied by the independent reviewer, and an `accepted` or
`rejected` `judgment`. The command joins these decisions by evidence ID and reports one judgment
with the agreeing reviewers for that ID. Conflicts and unattributed decisions leave its human result
unknown. The caller supplies the independent source.

The output is a versioned JSON object. Its `findings` preserve the original evidence references,
explanations and proposed reviews. A saved object can be read again as the findings input, with the
same key, Lean environment and independent review file to recheck all observations.

`SpecTools.Synthetic`, `SpecTools.Generated`, `SpecTools.Score` and `spec-tools synthetic` generate
a requirement of N rules from a seed with its four artifacts (prose, Lean model and ledger, Python
and its tests) agreeing by construction, plant gaps in one artifact with the key kept apart, and
score a run's findings against the key: how many planted gaps are found, and the false alarms.

- `spec-tools synthetic gvariants SEED N COUNT EMPTY DIR [blind [hard]]` writes a batch of COUNT
  variants of N rules, the first EMPTY with no plant; `blind` gives each three *shared blind spots*:
  a prose clause the Lean, the Python and its tests all leave out (an exception dropped from all
  three; an exception written for one rule's twin and not the rule; a sum checked on its first
  measure alone), so the artifacts agree with each other and only the prose shows the gap. The key
  names each plant's ledger row and each rule's *presentation*, the way a person's prose states it:
  plain, spread (the limit and its exception in different sections), defined term (a group or
  quantity defined elsewhere), example only (a worked case), two wordings, or folded (two rules in
  one sentence), drawn from all six, or from spread, defined term and example only with `hard`.
- `spec-tools synthetic prose DIR [MODEL]` rewrites each variant's `loans.md` as a library's manager
  would write it to staff, each rule in its presentation, with the configured backend; the template
  stays as `loans.template.md`. A document is kept only when two extractions of its rules, each
  blind to the other and to the rule list, give the rule list back exactly; otherwise it is written
  again, up to three times, and a variant failing all three gets `LEFT_OUT`, which `run` skips. Each
  variant's prompt, discards and usage go to its `prose.json`.
- `spec-tools synthetic run DIR AGENT-MODEL TOOL-MODEL [ARM]` gives each variant to an agent: the
  `baseline` arm with the files alone, the `ledger` arm offered the tools, the `workflow` arm with
  the ledger arm's prompt alone, and the `tools` arm with the audit, tests and gaps reports supplied
  before it starts. The `confirmed` arm supplies audit, tests, gaps and clauses before the agent
  starts, with three independent readings for gaps. A failed preparatory check prevents that
  variant's agent invocation. The default run includes `ledger` and `baseline`. For exact generated
  prose and supported Lean conditions, the mechanical gaps check can witness differing scopes or
  confirm the same condition. Its witness search materializes the product of the bounded value sets
  for the fields involved. A numeric field contributes the larger cutoff plus one values, and a
  flag-only field contributes two.
- `spec-tools synthetic compare DIR ...` compares the saved `tools` and `confirmed` journals on each
  directory's key. Use the same frozen fixtures for both runs and keep key variant IDs in order
  starting at zero. A missing successful result, a lost baseline hit, or a confirmed finding on an
  intact control fails the comparison. Scoring uses successful attempts. The usage report includes
  every attempt, including failed attempts and any checks the agent invoked.
- `spec-tools synthetic gapsrun SEED N DIR MODEL` runs `gaps` alone on each variant, scored by the
  row it names.
- A finding names the ledger row of the rule it concerns, and a plant is found by a finding naming
  its rule's row, whatever it quotes; results saved without rows are scored by their quotes. `run`
  and `gapsrun` print the planted, found and false alarms per presentation when the key has them.
- `spec-tools synthetic rescore DIR` scores a batch's saved findings again. The historical
  `legacy_row_match` metric localizes findings using rule identifiers and a quote fallback. Its
  counts measure agreement with the saved key at that level.
- `generate`, `gplants`, `gvariants` and the owners' commands take `vocab=NAME` for the domain's
  words: `library` (the default), `salon`, `tailor` or `bakery`.

Use the saved fixture and key or the producer revision when replaying a historical run. Typed
premise evidence changes the generated Lean source and the audit seen by the agent. Use
`ca6aa2d227ae1758dc324b9b70f872f34db7ba65` for the generator immediately before that change.
Rescoring saved journals needs their original key and findings only.

The owners' tests (`SpecTools.Owners`) have a small business owner, non-technical and imperfect,
describe the program they want. The owner gets two rules of each kind wrong: a limit given loosely,
a limit given twice with two numbers, an exception the business has but the owner forgets, and a
number given without saying whether that number itself is refused.

- `spec-tools synthetic owners-write DIR SEED prose|conversation` writes the owner's text as a
  message to a developer or a first call. The optional positional arguments are `NOTES-FILE`,
  `MODEL` and `DRAFT-FILE`. Add `vocab=NAME` to select a domain. The text goes through five rounds
  of a reviewer who sees only the persona and the text and lists what gives away that no such person
  wrote it, then through two blind readings, which must give each rule as the owner was told to
  state it, its flaw included. Every step's text and reader's list go to `steps.jsonl`, the kept
  text to `text.md`. An optional `DRAFT-FILE` supplies the first text for one start of the same
  review and fidelity process. Pass an empty string for `NOTES-FILE` to use the draft without notes.
  A final optional `REVIEW-DIR` resumes an incomplete review from its saved consecutive rounds.
  Supply the same draft, seed, form and vocabulary and use a fresh destination.
- `spec-tools synthetic owners-interview DIR SEED TURNS [MODEL]` collects a first call one turn at a
  time. The developer receives the conversation so far, and the owner also receives the private
  booking brief. The journal records completed turns and usage. Repeat the command with the same
  brief and backend to continue an interrupted call. A completed `draft.md` can be supplied to
  `owners-write` for review and fidelity checks.
- `spec-tools synthetic owners-variants DIR SEED COUNT EMPTY vocab=NAME` writes COUNT variants with
  the owner's text as their prose, the first EMPTY without plants, the others three shared blind
  spots on rules with no flaw; the key names the blind spots and the flaws by row, so a finding on a
  flaw's row counts as an imperfection found and no false alarm.
- `spec-tools synthetic owners-table DIR [COUNT [codex-input]]` prints the five rows from the saved
  results: `gaps` alone on the variants with blind spots, `gaps` on those without, and the baseline,
  ledger and tools arms. With a positive `COUNT`, require a successful score from each variant in
  every arm and ignore earlier failed attempts for variants that succeeded on retry. Use
  `codex-input` when the agent and all checks used Codex. Codex's reported input already includes
  cached input.

The hand-written loans fixture is in `fixtures/loans`.

## Lean demonstrations

Build with `lake build` and run these from the repository root. For a Lean-only run, leave
`SPEC_TOOLS_BACKEND` unset.

| Example | Command | Checked evidence |
| --- | --- | --- |
| Age limit | `lake env lean examples/age-limit/Wrong.lean` and `lake env lean examples/age-limit/Fixed.lean` | The original rule approves a 16-year-old. The corrected rule refuses them and approves an 18-year-old. The audit checks the premise witnesses. |
| Sorting | `lake env lean examples/sorting/Countermodels.lean` | The weak postcondition admits an empty output, and the length cap rejects a valid sorted permutation. The score journal checks both directions. |
| Refund | `lake env lean examples/refund/Refund.lean` | The audit distinguishes an ordinary proved bound from a theorem with checked inconsistent premises. |
| Salon booking | `lake env lean examples/owners/salon-call/Interpretations.lean` | Two readings of the synthetic conversation decide the same booking differently. The owner chooses the rule. |

## Running

```bash
lake build
lake env lean path/to/Spec.lean
lake test
```

`lake build` builds the library and `spec-tools`; `lake env lean` checks a specification and runs
its `#eval` lines (the audit, and `gaps` when the specification asks for it); `lake test` runs the
tests, which call no model. `spec-tools` with no arguments lists its commands. The toolchain is
`leanprover/lean4:v4.36.0`, with no dependencies.

## What is proved

Each pure core has its `*Proofs` module: the ledger's verdicts, the table reader, the clause
comparison, the gaps the ledger decides, the tests' findings, the model interface's invocations, the
generator and the scorer. The effectful layers (running Lean's environment queries, a model, pytest)
are tested.
