<p align="center"> <picture> <source media="(prefers-color-scheme: dark)"
srcset="docs/elenxis-dark.webp"> <img src="docs/elenxis.webp" alt="Elenxis: The proof checks. Does
the spec?" width="600"> </picture> </p>

# Elenxis

**Find out what a Lean specification lets through before you build against it.**

A sort function that always returns `[]` produces a sorted list for every input. Lean can prove
that. Would your sorting specification accept it? In the Elenxis example, the sortedness rule
accepts this function on every list. Adding length preservation exposes the failure on `[0]`.
After `lake build`, run `lake env lean fixtures/MutationReview.lean`.
[Example source](fixtures/MutationReview.lean)

Elenxis connects each requirement to its Lean statement and the evidence behind it. Use it to
challenge a rule with a deliberately broken model, check whether its premises can hold together,
or compare two readings of the same requirement. A configured language model can flag gaps in the
prose. When two readings permit different behavior, a concrete case gives the person who owns the
requirement a decision they can make.

Can three requirements each work in pairs and still leave an input with no valid output?
The [relation audit example](fixtures/RelationReview.lean) checks exactly that case in Lean.
Run `lake env lean fixtures/RelationReview.lean` to see the three requirement IDs and the
certificate that rules out a shared result. The [reference](docs/reference.md#relation-evidence)
shows how to collect the evidence for one requirement.

## Examples

### A one-minute demo (synthetic)

[`examples/age-limit`](examples/age-limit) is a synthetic demonstration, designed for this README.
The requirement, `loans.md`:

```markdown
1. A loan is refused to an applicant under 18.
```

The specification, `Wrong.lean`, formalizes the limit as 16, proves its theorem, and gives a witness
that its hypothesis can hold:

```lean
def decide (age : Nat) : Decision := if age < 16 then .refused else .approved

theorem refuses_minors (age : Nat) (h : age < 16) : decide age = .refused := by
  simp [decide, h]

theorem minor_exists : ∃ age : Nat, ∃ _h : age < 16, True := ⟨15, by decide, trivial⟩
```

**Lean accepts it.** `lake env lean examples/age-limit/Wrong.lean` runs the audit, which needs no
model:

```text
proved: minors: A loan is refused to an applicant under 18.
  AgeLimit.refuses_minors : ∀ (age : Nat), age < 16 → AgeLimit.decide age = AgeLimit.Decision.refused
    axioms: [propext]
  checked inhabitation evidence: AgeLimit.minor_exists for AgeLimit.refuses_minors
    ∃ age _h, True
    axioms: []
1 rows: 1 proved, 0 conditional, 0 unknown nonvacuity, 0 inconsistent premises, 0 not stated (1 judged)
```

**`gaps` finds the mismatch.** With a model configured,
`SPEC_TOOLS_BACKEND=$PWD/examples/backend.json lake env lean examples/age-limit/Wrong.lean` adds:

```text
Requirements check: process adapter claude-code; model claude-opus-5-5; effort medium; destination note: Anthropic, through the Claude Code login
too weak: minors: The statement only covers ages below 16 (age < 16). The clause requires refusal for every applicant under 18, so ages 16 and 17 are not covered.
1 gaps, 0 proposals refused
```

**A person decides.** The finding is a proposal, not a verdict: here the requirement is right and
the formalization wrong, so `Fixed.lean` sets the limit to 18 in the decision and in its theorem.
The same command on it prints `0 gaps, 0 proposals refused`.

The Lean-only runs also check the decision at age 16 in both versions and approval at age 18 in the
corrected version. [Commands for the Lean demonstrations](docs/reference.md#lean-demonstrations)

The outputs above are those of one run each, on Opus (`claude-opus-5-5`) at medium reasoning effort
through Claude Code ([`examples/backend.json`](examples/backend.json)). A model's wording varies
from run to run, and so can its findings; the audit's lines don't.

### Sorting in Lean 4 (synthetic)

With the prompt `Sorting spec in Lean 4`, `spec-tools ask` generated this Lean postcondition in its
`lean` field. Lean accepted the definition.

```lean
import Std

/-- The output is nondecreasing and contains exactly the input elements, with multiplicity. -/
def SortPostcondition (input output : List Nat) : Prop :=
  output.Pairwise (fun a b => a ≤ b) ∧ output.Perm input
```

<details> <summary>Full output from ask</summary>

```text
usage: 1 calls; tokens input 17083, cache write 0, cache read 0, output 79; 5391 ms; codex gpt-6.2-sol
{"lean":"import Std\n\n/-- The output is nondecreasing and contains exactly the input elements, with multiplicity. -/\ndef SortPostcondition (input output : List Nat) : Prop :=\n  output.Pairwise (fun a b => a ≤ b) ∧ output.Perm input\n"}
```

</details>

For `draft-review`, the [requirement](examples/sorting/inventory.json) says that sorting must put
any list of natural numbers in nondecreasing order and preserve every element's multiplicity. Both
drafts below were rejected, with exit status 1.

**Too weak.** This [draft](examples/sorting/too-weak.json) checks only `output.Pairwise (· ≤ ·)`. It
ignores the input.

```text
uncovered: sorting: The draft supplies no external acceptance cases. For example, input [2, 1, 2] should accept [1, 2, 2] and reject [2, 1, 2], [1, 2], and [1, 2, 2, 3].
too weak: sorting: Statement 0 requires nondecreasing output but ignores the input. It accepts [] for input [2, 1, 2]. Require the output to be a permutation of the input so every element's multiplicity is preserved.
2 gaps, 0 proposals refused
usage: 1 calls; tokens input 17280, cache write 0, cache read 0, output 177; 7811 ms; codex gpt-6.2-sol
```

The `uncovered` line is a separate suggestion to add acceptance cases.

**Too strong.** This [draft](examples/sorting/too-strong.json) checks order and permutation and adds
`output.length ≤ 10`.

```text
extra: sorting: Statement 0 requires output.length ≤ 10. Since permutation preserves length, inputs with more than 10 elements admit no valid output, even though the requirement applies to every list of natural numbers.
1 gaps, 0 proposals refused
usage: 1 calls; tokens input 16354, cache write 0, cache read 0, output 82; 5489 ms; codex gpt-6.2-sol
```

To replay these calls after building Elenxis, use the [sorting inputs](examples/sorting) from the
repository root. The diagnostic wording can vary across runs.

```sh
cli=.lake/build/bin/spec-tools
example=examples/sorting
"$cli" ask codex gpt-6.2-sol "$example/proposal.schema.json" "$example/prompt.txt"
"$cli" draft-review codex gpt-6.2-sol "$example/prompt.txt" "$example/inventory.json" "$example/too-weak.json"
"$cli" draft-review codex gpt-6.2-sol "$example/prompt.txt" "$example/inventory.json" "$example/too-strong.json"
```

Run `lake env lean examples/sorting/Countermodels.lean` to check both distinctions without a model.
The first proof shows that the ordered-only predicate admits the empty output for `[2, 1, 2]`. The
second shows that the length cap rejects an eleven-element sorted permutation. The command verifies
both named theorems against the expected direction in the example's score key. The same command
searches a smaller domain of binary inputs and outputs of length at most one. The report states
where the search found no distinction and labels the result outside that domain unknown.

### Worked example: a salon booking call

In a fictional first call about online bookings, the salon owner gives two different no-show limits
for children's haircuts and leaves the unpaid-visit threshold open. The benchmark tests for both
kinds of ambiguity alongside rules deliberately missed by the Lean specification, Python
implementation and tests. The example includes the dialogue, scoring key, measured results and
commands to reproduce them. [Salon's first booking call](examples/owners/salon-call/README.md)

Lean proves that the four-miss rule allows every booking the two-miss rule allows, plus others.
The report asks the owner **“After two missed appointments, can a parent still book a child's
haircut online?”** The answer determines which rule to keep. The signed decision example shows how
a later change to the reviewed text makes an earlier approval stale.
[Compare the rules](examples/owners/salon-call/Interpretations.lean) ·
[Check a signed decision](examples/owners/salon-call/README.md#a-signed-synthetic-decision)

## What Lean checks, and what the model checks

- **Lean decides** whatever the environment settles: whether a named theorem exists and is a
  proposition, which axioms it rests on, whether it has hypotheses without a witness, whether every
  theorem under the specification's root is claimed by some row. These verdicts are computed, and
  the code computing them is proved (the `*Proofs` modules). In
  [`examples/refund`](examples/refund), a theorem whose hypothesis `used = 0 ∧ used > 0` can never
  hold is reported as `inconsistent premises` with a checked contradiction certificate.
- **A model proposes** only what needs reading the prose: a clause no statement covers, a statement
  weaker than its clause, a case the prose leaves undecided, a statement nobody asked for. Its
  answer must validate against a schema and name rows the ledger has; anything else is refused as
  malformed.

A theorem can hold on an empty input type. The audit prints a separate applicability result for each
named theorem. A Lean ledger row can request `.someInput n` for joint feasibility of its first `n`
binders, or `.eachContext c n` for feasibility under every assignment to the first `c` binders. The
latter quantifies universally over those contexts and existentially over the next `n` inputs. Count
implicit parameters and premise proofs too. Binders in the conclusion can be left outside that
prefix. To require at least one realizable context as well, add a separate existential claim. Use
`.exclusion` when the theorem itself states the intended impossibility.

Supply named theorems in `supports` or `refutes`. The audit checks their types and axioms against
the displayed obligation or its negation. Missing or mismatched evidence leaves a claim unresolved.
An omitted claim is unassessed. Requirements mode reports an error for a declared obligation that
lacks accepted support. The [domain audit fixture](fixtures/DomainAudit.lean) shows a model with an
input in one context and a proof that another context has none.

The model never gets the last word on anything Lean can decide, and every finding names the row of
the clause it concerns.

## Quickstart

```bash
lake build                                   # the library and the spec-tools command
lake env lean examples/age-limit/Wrong.lean  # the audit: no model
SPEC_TOOLS_BACKEND=$PWD/examples/backend.json lake env lean examples/age-limit/Wrong.lean
lake test                                    # the tests, which call no model
```

The third line calls Claude Code with its own login; [docs/backends.md](docs/backends.md) configures
Codex or any other harness, provider or local model instead. A `command` adapter runs an executable
you name: it is trusted code, and the launcher is no sandbox.

To generate and check a standalone synthetic Lean fixture, run these commands from the Elenxis
checkout:

```bash
lake exe spec-tools synthetic generate 42 8 /tmp/elenxis-demo
lake -d /tmp/elenxis-demo/s42-n8 build
```

The generated project includes requirements, a specification, executable Lean code, proof
obligations and an audit ledger. It uses the local Elenxis checkout as a Lake dependency. See [the
optional Python export](docs/reference.md#optional-cross-language-target).

For your own specification, write a ledger beside it, one row per clause of the prose, naming the
theorems that state the clause and the witnesses showing their hypotheses can hold, and run
`SpecTools.Audit.run` and `SpecTools.Gaps.runConfigured` from it
([docs/reference.md](docs/reference.md)).

## The life of a contract

```text
prose requirements
  │  spec-tools draft-check      every clause has a planned contract or an external check
  │  spec-tools draft-review     a model reads the complete draft against the prose
  ▼
approved contract (the draft a person accepted)
  │  Gaps.checkDraftContracts    the specification's names are exactly the draft's
  │  Audit.checkApprovedContracts  definitions' types/bodies or theorems' propositions agree
  ▼
Lean specification and its ledger
  │  Audit.run                   proved, vacuous, conditional or unstated, row by row
  │  Gaps.runConfigured          the statements against the prose
  ▼
Lean implementation and proofs of its obligations
```

The checks above the line "approved contract" compare the formalization with the prose; those below
it compare the Lean with the approved formalization. Agreement with the approved formalization is
checked by Lean (names and elaborated definitions or theorem propositions compared; proofs checked
separately); agreement with the human intent is only reviewed, by a model's reading and a person's
decision.

## The tools

- **Audit** (`SpecTools.Audit`): every row's verdict from its theorems' statements, axioms and
  hypotheses.
- **Gaps** (`SpecTools.Gaps`, `SpecTools.GapsRun`): the four gaps between the prose and the
  statements.
- **Mutation review** (`SpecTools.Mutation.review`) checks proposed changes and behavioral models
  against named certificates. The report shows which claims have proofs and which remain
  inconclusive. Supply a schedule to see which checks were skipped. [Reviewing mutations and
  interpretations](docs/reference.md#comparing-mutations-and-interpretations)
- **Adversarial admission** (`SpecTools.Adversarial`): `adversarial_claim` admits a theorem only
  with a witness for its hypotheses and, for each attack, a proof that a cheap wrong implementation
  (a constant, doing nothing) fails the same law.
- **Proof checks** (`spec-tools check proofs|contracts|counterexamples`): build the corresponding
  modules of a generated Lean project. See the [optional cross-language
  target](docs/reference.md#optional-cross-language-target) for Python.
- **Draft review** (`spec-tools draft-check`, `draft-review`): the clauses' planned contracts,
  reviewed before any Lean is written.
- **Clauses** (`spec-tools clauses`): a prose file's clauses extracted twice, blind, and compared.
- **Synthetic evaluation** (`spec-tools synthetic`): generated requirements with planted gaps and a
  key kept apart, scoring how many a run finds and its false alarms.

Each is described in [docs/reference.md](docs/reference.md).

## What this does not guarantee

- A model's judgement can be wrong both ways: it can miss a gap and propose a false one. A clean
  `gaps` report is evidence, not a proof that the specification says what was meant.
- A proved Lean theorem shows its statement holds, never that the statement is the right one.
- Removing guards and running the property tests shows which guards the tests notice; it doesn't
  show the program correct.
- `specified (unproved)` means a contract is well formed and stated, not that anything satisfies it.
- Lean's verdicts are only as good as the ledger: a clause no row names is found only if a model
  reading the prose notices it.

## Results

These historical tables use `legacy_row_match`, which credits a location or its matching quote
against a planted key. A match can have the wrong category or explanation.

Measured with `spec-tools synthetic` on generated requirements, not on production projects. Each
variant is a requirement of 30 rules with its Lean specification, ledger, Python implementation and
property tests, into which the generator plants three *shared blind spots*: clauses the Lean, the
Python and its tests all leave out the same way, so the artifacts agree with each other and only the
prose shows the gap (an exception dropped from all three, an exception written for a rule's twin and
not the rule, a sum checked on one of its two measures). Each finding is scored against a key the
runs never see. Every model call below is Opus (`claude-opus-5-5`) at medium effort.

| Run | Variants | Planted gaps found | False alarms | Time per run (mean) | Tokens per run (mean) |
| --- | --- | --- | --- | --- | --- |
| `gaps` alone | 20, three blind spots each | 60 of 60 | 0 | 126 s for the batch | |
| `gaps` alone, no gap planted (control) | 2 | none to find | 0 | 22 s for the batch | |
| Agent, files only (`baseline`) | 20 | 60 of 60 | 0 | 29 s | 61531 |
| Agent offered the tools (`ledger`) | 20 | 60 of 60 | 6 | 119 s | 161855 |
| Agent handed the tools' reports (`tools`) | 20 | 60 of 60 | 3 | 25 s, the reports apart | 146252, the reports apart |

On these variants Opus finds every planted gap from the files alone, so the tools add no gaps found:
offered the tools, the agent took 4.1 times the time and 2.6 times the tokens. In the `tools` arm
the audit, the tests and `gaps` run before the agent starts, and the time and tokens shown are the
agent's alone. Each false alarm of both arms names a clause beside a planted gap: eight name the
rule whose exception was dropped, reporting its unconditional Lean statement as behaviour the prose
doesn't ask for (the planted gap seen from the rule's side), and one names the exception of a rule
whose sum was planted. The scorer credits only the clause the key names. A test that can tell the
arms apart on Opus needs gaps the bare agent misses.

To replay these historical commands against the original fixture format, use the producer revision.
See [the reference on synthetic experiments](docs/reference.md#the-synthetic-evaluation). Run from
the repository root with an empty `DIR`:

```bash
spec-tools synthetic gvariants 20261107 30 20 0 DIR blind --target python
SPEC_TOOLS_BACKEND=$PWD/examples/backend.json spec-tools synthetic run DIR claude-opus-5-5 claude-opus-5-5
SPEC_TOOLS_BACKEND=$PWD/examples/backend.json spec-tools synthetic run DIR claude-opus-5-5 claude-opus-5-5 tools
SPEC_TOOLS_BACKEND=$PWD/examples/backend.json spec-tools synthetic gapsrun 20261107 30 DIR claude-opus-5-5
```

(`spec-tools` is `.lake/build/bin/spec-tools` after `lake build`.) The limits: the requirements are
generated from templates, so a model may learn their shape; each variant ran once per arm, so the
numbers carry the variance of one run; and the scorer credits a finding by the clause it quotes, or,
for `gaps` alone, by the row it names, so a finding naming the right place for the wrong reason
counts as found.

## Documentation

- [docs/reference.md](docs/reference.md): the ledger, the audit's verdicts, specifying before
  implementing, each tool, the synthetic evaluation's commands, and what is proved.
- [docs/backends.md](docs/backends.md): configuring Claude Code, Codex or a command adapter, the
  reasoning effort, and the trust a command adapter takes.

## Inspiration

The problem this repository works on is the one [Formal
Vibefication](https://proofofkeags.com/research/2026-05-12-formal-vibefication.html) (Keagan
McClelland, 12 May 2026) names as still missing once AI writes the code: machine-assisted
specification, a model that can "help a human author a faithful formal specification — proposing
properties, surfacing implicit assumptions, flagging where the spec under-determines the system".
The article is an inspiration only; its author has not reviewed or endorsed this project.

## License

Elenxis is licensed under the [Apache License, Version 2.0](LICENSE).

Commercial use, modification, redistribution, and proprietary integrations are welcome under the
terms of the license.

See [NOTICE](NOTICE) for attribution information and [TRADEMARKS.md](TRADEMARKS.md) for the Elenxis
trademark policy.
