# Reference

## The ledger

A ledger is a `List SpecTools.Ledger.Row`, written in Lean beside the specification:

```lean
import SpecTools.Audit
import SpecTools.GapsRun

def ledger : List SpecTools.Ledger.Row := [
  { id := "prerelease", source := "DESIGN.md, Tiers",
    clause := "a base whose version carries a pre-release suffix ... admits no space",
    theorems := [``prerelease_admits_none], witnesses := [``wit_prerelease],
    tests := ["test_prerelease_admits_none"] } ]

#eval SpecTools.Audit.run ledger `Root
```

A row names the theorems stating its clause, the witnesses showing those theorems' hypotheses can
hold, and the tests covering it in the implementation's language. Its `status` is `covered` (the
default), `uncovered REASON`, `provisional DECISION` or `accepted DECISION`. A ledger kept as a
Markdown table instead is read by `SpecTools.LedgerTable`; its header row is
`| id | clause | source | theorems | witnesses | tests | status |`.

## The audit's verdicts

`SpecTools.Audit.run ledger Root` judges every row from its theorems' statements, axioms and
hypotheses, and prints one verdict per row:

- **proved**: every named theorem exists, rests only on `propext`, `Classical.choice` and
  `Quot.sound`, and either has no hypotheses or the row names a witness;
- **too weak or vacuous**: a theorem has hypotheses and the row gives no witness that they can hold;
- **conditional**: a theorem rests on another axiom;
- **not stated**: the row names no theorem;
- **specified (unproved)**: in requirements mode, the row's declarations are proposition
  definitions, well formed and not proved.

It fails, rather than reports, on what makes the report itself wrong: a repeated identifier, a named
theorem that is no theorem, a theorem under `Root` no row claims, a source module it doesn't import.
With a digest file, rows whose clause and statements are unchanged are not judged again.

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
decide), `extra` (a statement the prose neither asks for nor implies). Lean decides one of them with
no model: a row whose theorems have hypotheses and no witness is too weak. The model proposes the
rest; a proposal naming a row the ledger lacks, or of an unknown kind, is printed as refused, and an
answer that breaks the schema is no answer. The model sees each row's witnesses apart from its
statements, as facts showing the statements' hypotheses can hold.

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

## The synthetic evaluation

`SpecTools.Synthetic`, `SpecTools.Generated`, `SpecTools.Score` and `spec-tools synthetic` generate
a requirement of N rules from a seed with its four artifacts (prose, Lean model and ledger, Python
and its tests) agreeing by construction, plant gaps in one artifact with the key kept apart, and
score a run's findings against the key: how many planted gaps are found, and the false alarms.

- `spec-tools synthetic gvariants SEED N COUNT EMPTY DIR [blind]` writes a batch of COUNT variants
  of N rules, the first EMPTY with no plant; `blind` gives each three *shared blind spots*: a prose
  clause the Lean, the Python and its tests all leave out (an exception dropped from all three; an
  exception written for one rule's twin and not the rule; a sum checked on its first measure alone),
  so the artifacts agree with each other and only the prose shows the gap.
- `spec-tools synthetic run DIR AGENT-MODEL TOOL-MODEL [ARM]` gives each variant to an agent: the
  `baseline` arm with the files alone, the `ledger` arm offered the tools, the `workflow` arm with
  the ledger arm's prompt and no tools, the `tools` arm with the tools' reports handed over before
  it starts; both `ledger` and `baseline` when no arm is named.
- `spec-tools synthetic gapsrun SEED N DIR MODEL` runs `gaps` alone on each variant, scored by the
  row it names.
- `spec-tools synthetic rescore DIR` scores a batch's saved findings again.

The hand-written loans fixture is in `fixtures/loans`.

## Running

```bash
lake build
lake env lean path/to/Spec.lean
lake test
```

`lake build` builds the library and `spec-tools`; `lake env lean` checks a specification and runs
its `#eval` lines (the audit, and `gaps` when the specification asks for it); `lake test` runs the
tests, which call no model. `spec-tools` with no arguments lists its commands. The toolchain is
`leanprover/lean4:v4.36.0-rc2`, with no dependencies.

## What is proved

Each pure core has its `*Proofs` module: the ledger's verdicts, the table reader, the clause
comparison, the gaps the ledger decides, the tests' findings, the model interface's invocations, the
generator and the scorer. The effectful layers (running Lean's environment queries, a model, pytest)
are tested.
