# lean-spec-tools

**Lean's kernel checks a proof against its theorem. Nothing checks the theorem against what you
meant. This does.**

lean-spec-tools holds a requirement written in prose against its specification in Lean, and that
specification against an implementation's property tests. Lean decides what it can; a model is asked
only for what Lean can't decide, and its answers are proposals a person judges.

## The problem

AI writes more and more of the code, and increasingly the proofs. A proof is the easy part to trust:
Lean's kernel checks it, and a wrong proof doesn't compile. What nobody checks is the *statement*. A
theorem can be proved and still say nothing useful:

- its hypotheses can never hold together, so it proves anything (it is *vacuous*);
- it is stated for one special case of the clause it was meant to capture (it is *too weak*);
- a clause of the requirement has no theorem at all (*uncovered*);
- the prose never decided a case the code has to handle (*undecided*);
- a theorem constrains something the requirement never asked for (*extra*).

Every one of these compiles, and a reviewer who sees a green build and a theorem named after the
requirement has no reason to look twice. When a model writes both the specification and its proof,
it can produce exactly these, and the kernel accepts every one.

[Formal Vibefication](https://proofofkeags.com/research/2026-05-12-formal-vibefication.html) (Proof
of Keags, 12 May 2026) argues that once AI absorbs the cost of writing, verified software stops
being an academic luxury, and that the specification becomes the scarce artifact. Of the
infrastructure it says still has to mature, this repository builds the third piece: "can a model
help a human author a faithful formal specification — proposing properties, surfacing implicit
assumptions, flagging where the spec under-determines the system?"

## The idea

Treat the requirement as data. Each clause of the prose becomes a row of a **ledger**, written in
Lean beside the specification, naming:

- the theorems that state the clause,
- the witnesses showing those theorems' hypotheses can hold,
- the tests that cover it in the implementation's language.

Then split every question about the ledger by who can answer it:

- **Lean decides** whatever the environment settles: whether a named theorem exists and is a
  proposition, which axioms it rests on, whether it has hypotheses without a witness, whether every
  theorem under the specification's root is claimed by some row. These verdicts are computed, never
  guessed, and the code computing them is proved (`*Proofs` modules).
- **A model proposes** only what needs reading the prose: a clause no statement covers, a statement
  weaker than its clause, a case the prose leaves undecided, a statement nobody asked for. Its
  answer must validate against a schema and name rows the ledger has; anything else is refused as
  malformed. A proposal is a finding for a person to judge, not a verdict.

The model never gets the last word on anything Lean can decide, and every finding points at a
clause.

## A two-minute example

[`examples/refund`](examples/refund) has a two-line requirement:

```markdown
1. A refund never exceeds the amount the customer paid.
2. A customer who used nothing gets back everything they paid.
```

and a specification whose two theorems the kernel accepts:

```lean
def refund (paid used : Nat) : Nat := paid - used

-- Clause 1, stated only for the customer who used nothing.
theorem refund_le_paid (paid : Nat) : refund paid 0 ≤ paid := by
  simp [refund]

-- Clause 2, under a hypothesis no order meets.
theorem full_refund (paid used : Nat) (h : used = 0 ∧ used > 0) : refund paid used = paid := by
  omega
```

Both compile, and both are wrong. `lake env lean examples/refund/Refund.lean` runs the audit, which
needs no model:

```text
proved: bounded: A refund never exceeds the amount the customer paid.
  Refund.refund_le_paid : ∀ (paid : Nat), Refund.refund paid 0 ≤ paid
    axioms: [propext, Quot.sound]
too weak or vacuous: full: A customer who used nothing gets back everything they paid.
  Refund.full_refund : ∀ (paid used : Nat), used = 0 ∧ used > 0 → Refund.refund paid used = paid
    axioms: [propext, Quot.sound]
2 rows: 1 proved, 0 conditional, 1 too weak or vacuous, 0 not stated (2 judged)
```

Lean alone catches the second: the theorem has a hypothesis and the row gives no witness that it can
hold. The first it calls proved, and as far as Lean can tell it is: the statement has no hypotheses
and its proof checks. Only reading the clause shows it covers one order out of all of them. That is
the gap `gaps` asks a model about,
`SPEC_TOOLS_GAPS=sonnet lake env lean examples/refund/Refund.lean` (one run's output; a model's
wording varies from run to run):

```text
Requirements check: process adapter claude-code; model sonnet; destination note: Anthropic
too weak: full: its theorems have hypotheses and no witness shows they can hold
too weak: bounded: Only states refund paid 0 ≤ paid, i.e. for used = 0. The prose says a refund never exceeds the amount paid for any usage; the statement should quantify over all used values (refund paid used ≤ paid).
too weak: full: The hypothesis `used = 0 ∧ used > 0` is contradictory, so the theorem is vacuously true and says nothing. It should be `used = 0 → refund paid used = paid`.
3 gaps, 0 proposals refused
```

The first finding is Lean's, decided with no model. The other two are the model's proposals, each
tied to a row of the ledger and checked against the answer schema before it is printed: one finds
the gap Lean called proved, the other explains the one Lean caught and proposes the statement the
clause meant.

## The tools

- **Audit** (`SpecTools.Audit`) judges every row from its theorems' statements, axioms and
  hypotheses. It fails on what makes the report wrong (a repeated identifier, a named theorem that
  is no theorem, a theorem under the root no row claims, a source module it doesn't import); a row
  not stated, conditional or too weak is reported, not failed. With a digest file, rows whose clause
  and statements are unchanged are not judged again.
- **Gaps** (`SpecTools.Gaps`, `SpecTools.GapsRun`): `#eval SpecTools.Gaps.run ledger prose backend`
  finds the four gaps between the prose and the statements. Lean decides a row whose theorems have
  hypotheses and no witness; a model proposes the rest.
- **Adversarial admission** (`SpecTools.Adversarial`): `adversarial_claim ENTRY in theorem ...`
  admits a theorem only with a witness inhabiting its hypotheses and, for each attack, a mutant
  implementation (the cheapest wrong one: a constant, doing nothing) with a proof that the same law
  fails for it. A law a do-nothing implementation also satisfies has no such proof, so its theorem
  is never admitted, and the check runs before the theorem's own proof is elaborated.
- **Tests** (`SpecTools.Tests`, `adapters/python_guards.py`):
  `SpecTools.Tests.run rows adapter module testFile` reports a test a row names that the test file
  doesn't define, and a guard of the implementation whose removal no test notices. The Python
  adapter replaces each disjunct of a refusing `if` (and each term of a sum inside one) by `False`
  (or `0`) in a copy and runs the named tests with pytest.
- **Clauses** (`spec-tools clauses`): a model extracts a prose file's clauses twice, blind to each
  other, and the differences are printed as rows to add.
- **Draft review** (`spec-tools draft-check`, `spec-tools draft-review`): before any Lean is
  written, every clause of the source inventory gets a planned contract or an external check, and
  the complete draft goes to one model call for semantic review.
- **Model interface** (`SpecTools.Model`, `SpecTools.BackendConfig`, `SpecTools.Schema`): a question
  goes to a configurable backend, and the answer is checked against a JSON schema subset (`type`,
  `properties`, `required`, `additionalProperties`, `items`, `enum`; any other keyword is refused).
  The effects sit in a `Runner`, so tests script it and reach no model.
- **Synthetic test** (`SpecTools.Synthetic`, `SpecTools.Generated`, `SpecTools.Score`,
  `spec-tools synthetic`): generates a requirement of N rules from a seed with its four artifacts
  (prose, Lean model and ledger, Python and its tests) agreeing by construction, plants gaps in one
  artifact with the key kept apart, and scores a run's findings against the key: how many planted
  gaps an agent with these tools finds, and its false alarms. The hand-written loans fixture is in
  `fixtures/loans`.

## The ledger

A ledger is a `List SpecTools.Ledger.Row`:

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

### Specifying before implementing

For a specification written before its implementation, opt into requirement declarations:

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

### Review before writing the specification

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

### Backend configuration

Keep backend selection outside specifications. Set `SPEC_TOOLS_BACKEND` to the absolute path of a
JSON file, then use `SpecTools.Gaps.runConfigured ledger prose` (with `requirements := true` for
unproved requirements). Missing or malformed configuration fails before launching a process.

For Codex using its existing login/subscription:

```json
{"adapter":"codex","model":"YOUR_MODEL","dataGoesTo":"Codex using the configured account"}
```

For Claude Code use `"adapter":"claude-code"` and its model/account description. Model names are
opaque strings; the checker contains no provider-specific model allowlist. `dataGoesTo` documents
the actual destination; it neither authorizes a call nor changes routing. The planner's allowlist
compares adapter configuration and model; changing this note cannot change that decision or the
invocation.

For any other harness, provider or locally hosted model, configure an adapter executable:

```json
{"adapter":"command","command":"/absolute/path/to/adapter","args":[],"model":"YOUR_MODEL","dataGoesTo":"local inference server"}
```

The executable receives its configured arguments followed by `request.json`, relative to the fresh
working directory. That UTF-8 JSON file contains `protocol: 1`, `model`, `prompt`, `schema`,
`timeoutMs`, `mode` (`question` or `agent`) and `tools` (the requested agent tool policy). Arguments
are passed literally without a shell. Return the answer itself as JSON on stdout, diagnostics on
stderr, and a nonzero status on failure. The shared checker validates the answer against `schema`; a
backend need not support constrained JSON generation. The executable adapts this contract to its
chosen service or local inference engine, keeping credentials in its own deployment configuration.

Adapter configuration is trusted executable configuration. Command adapters must enforce the
requested mode and tool restrictions; the generic launcher does not sandbox arbitrary commands. The
built-in Codex and Claude adapters retain their existing sandbox/tool restrictions. Switching to
another adapter never grants data access or permission to contact its destination.

The `ask` and `clauses` CLI commands accept `configured` in place of `HARNESS`; the legacy `MODEL`
positional argument overrides the configured model in these CLI forms. Their explicit `codex MODEL`
and `claude-code MODEL` forms remain available. Synthetic agent runs use the configured adapter with
their explicit agent model; generated gap checks use it with their explicit tool model. Synthetic
clause extraction uses the same explicit tool model.

## What is proved

Each pure core has its `*Proofs` module: the ledger's verdicts, the table reader, the clause
comparison, the gaps the ledger decides, the tests' findings, the generator and the scorer. The
effectful layers (running Lean's environment queries, a model, pytest) are tested.
