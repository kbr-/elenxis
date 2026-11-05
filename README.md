# lean-spec-tools

Tools for checking a requirement written in prose against its specification in Lean, and that
specification against an implementation's property tests. Lean decides what it can; a model is asked
only for what Lean can't decide, and its answers are proposals a person judges.

The workflow it serves: the requirement's clauses go into a ledger, each row naming the theorems
that state it, the witnesses showing those theorems' hypotheses can hold, and the tests covering it
in the implementation's language. The audit judges the rows against the Lean environment, `gaps`
finds what the theorems leave out, and `tests` checks that the property tests notice each guard of
the implementation.

The toolchain is `leanprover/lean4:v4.34.0`, with no dependencies.

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

A row's `status` is `covered` (the default), `uncovered REASON`, `provisional DECISION` or
`accepted DECISION`. A ledger kept as a Markdown table instead is read by `SpecTools.LedgerTable`;
its header row is `| id | clause | source | theorems | witnesses | tests | status |`.

## The tools

For a specification written before implementation, opt into requirement declarations:

```lean
def obligation (n : Nat) : Prop := n + 0 = n

def requirements : List SpecTools.Ledger.Row := [
  { id := "identity", clause := "adding zero preserves the input",
    theorems := [``obligation] } ]

#eval SpecTools.Audit.run requirements `Spec (requirements := true)
#eval SpecTools.Gaps.run requirements prose backend (requirements := true)
```

This mode reads parameterized proposition definitions and labels them **specified (unproved)**. The
`theorems` field supplies the declaration names in either mode. Requirement declarations cannot
receive a proved verdict. Witness declarations must remain proved theorems. Empty ledgers, missing
declarations, non-propositions, unsafe or unavailable bodies and unaccepted axioms fail requirement
admission; the report lists invalid declarations across each row. Expose a definition's body with
the module's appropriate public interface or `import all` when the module system hides it. The gaps
model reads the requirement bodies and judges their coverage; admitting a declaration does not
establish its adequacy or truth. The default mode continues to require theorem declarations.

- **Audit** (`SpecTools.Audit`) judges every row from its theorems' statements, axioms and
  hypotheses. It fails on what makes the report wrong (a repeated identifier, a named theorem that
  is no theorem, a theorem under `Root` no row claims, a source module it doesn't import); a row not
  stated, conditional or too weak is reported, not failed. With a digest file, rows whose clause and
  statements are unchanged are not judged again.
- **Gaps** (`SpecTools.Gaps`, `SpecTools.GapsRun`): `#eval SpecTools.Gaps.run ledger prose backend`
  finds the four gaps between the prose and the statements. Lean decides a row whose theorems have
  hypotheses and no witness; a model proposes the rest: a clause no statement covers, a statement
  weaker than its clause, a case the prose leaves undecided, a statement the prose doesn't ask for.
- **Tests** (`SpecTools.Tests`, `adapters/python_guards.py`):
  `SpecTools.Tests.run rows adapter module testFile` reports a test a row names that the test file
  doesn't define, and a guard of the implementation whose removal no test notices. The Python
  adapter replaces each disjunct of a refusing `if` (and each term of a sum inside one) by `False`
  (or `0`) in a copy and runs the named tests with pytest.
- **Clauses** (`spec-tools clauses`): a model extracts a prose file's clauses twice, blind to each
  other, and the differences are printed as rows to add.
- **Model interface** (`SpecTools.Model`, `SpecTools.Schema`): a question goes to a backend, a
  harness (`claudeCode` or `codex`) with a model and where its data goes, and the answer is checked
  against a JSON schema subset (`type`, `properties`, `required`, `additionalProperties`, `items`,
  `enum`; any other keyword is refused). The effects sit in a `Runner`, so tests script it and reach
  no model.
- **Synthetic test** (`SpecTools.Synthetic`, `SpecTools.Generated`, `SpecTools.Score`,
  `spec-tools synthetic`): generates a requirement of N rules from a seed with its four artifacts
  (prose, Lean model and ledger, Python and its tests) agreeing by construction, plants gaps in one
  artifact with the key kept apart, and scores a run's findings against the key. It measures how
  many planted gaps an agent with these tools finds, and its false alarms. The hand-written loans
  fixture is in `fixtures/loans`.

## Running

```bash
lake build
lake env lean path/to/Spec.lean
lake test
```

`lake build` builds the library and `spec-tools`; `lake env lean` checks a specification and runs
its `#eval` lines (the audit, and `gaps` when the specification asks for it); `lake test` runs the
tests, which call no model. `spec-tools` with no arguments lists its commands.

## What is proved

Each pure core has its `*Proofs` module: the ledger's verdicts, the table reader, the clause
comparison, the gaps the ledger decides, the tests' findings, the generator and the scorer. The
effectful layers (running Lean's environment queries, a model, pytest) are tested.
