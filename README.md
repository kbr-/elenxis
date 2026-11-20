<p align="center"><img src="docs/elenxis.webp" alt="Elenxis: The proof checks. Does the spec?"
width="600"></p>

# Elenxis

**Lean's kernel checks a proof against its theorem. Nothing checks the theorem against what you
meant. This does.**

Formal verification can prove that code satisfies a specification. It cannot, by itself, prove that
the specification says what the user intended. `Elenxis` makes the links between natural-language
requirements, Lean statements, proofs and implementation tests explicit and auditable: Lean decides
what it can, a model is asked only for what Lean can't decide, and its answers are proposals a
person judges.

## The problem

A proof is the easy part to trust: Lean's kernel checks it, and a wrong proof doesn't compile. What
nobody checks is the *statement*. A theorem can be proved and still miss its requirement: its
hypotheses can never hold, so it proves anything; it covers one case of its clause; a clause has no
theorem at all; the prose never decided a case the code handles; or a theorem constrains something
nobody asked for. Every one of these compiles, and when a model writes both the specification and
its proof, it can produce any of them.

## A one-minute demo (synthetic)

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

theorem minor_exists : ∃ age : Nat, age < 16 := ⟨15, by decide⟩
```

**Lean accepts it.** `lake env lean examples/age-limit/Wrong.lean` runs the audit, which needs no
model:

```text
proved: minors: A loan is refused to an applicant under 18.
  AgeLimit.refuses_minors : ∀ (age : Nat), age < 16 → AgeLimit.decide age = AgeLimit.Decision.refused
    axioms: [propext]
  AgeLimit.minor_exists : ∃ age, age < 16
    axioms: []
1 rows: 1 proved, 0 conditional, 0 too weak or vacuous, 0 not stated (1 judged)
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

The outputs above are those of one run each, on Opus (`claude-opus-5-5`) at medium reasoning effort
through Claude Code ([`examples/backend.json`](examples/backend.json)). A model's wording varies
from run to run, and so can its findings; the audit's lines don't.

## What Lean checks, and what the model checks

- **Lean decides** whatever the environment settles: whether a named theorem exists and is a
  proposition, which axioms it rests on, whether it has hypotheses without a witness, whether every
  theorem under the specification's root is claimed by some row. These verdicts are computed, and
  the code computing them is proved (the `*Proofs` modules). In
  [`examples/refund`](examples/refund), a theorem whose hypothesis `used = 0 ∧ used > 0` can never
  hold is reported `too weak or vacuous` with no model asked.
- **A model proposes** only what needs reading the prose: a clause no statement covers, a statement
  weaker than its clause, a case the prose leaves undecided, a statement nobody asked for. Its
  answer must validate against a schema and name rows the ledger has; anything else is refused as
  malformed.

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
  │  Audit.checkApprovedContracts  their types and bodies are the approved ones
  ▼
Lean specification and its ledger
  │  Audit.run                   proved, vacuous, conditional or unstated, row by row
  │  Gaps.runConfigured          the statements against the prose
  │  Tests.run                   each guard of the implementation noticed by a test
  ▼
implementation and its tests
```

The checks above the line "approved contract" compare the formalization with the prose; those below
it compare the Lean with the approved formalization. Agreement with the approved formalization is
checked by Lean (names, types and bodies compared, theorems proved); agreement with the human intent
is only reviewed, by a model's reading and a person's decision.

## The tools

- **Audit** (`SpecTools.Audit`): every row's verdict from its theorems' statements, axioms and
  hypotheses.
- **Gaps** (`SpecTools.Gaps`, `SpecTools.GapsRun`): the four gaps between the prose and the
  statements.
- **Adversarial admission** (`SpecTools.Adversarial`): `adversarial_claim` admits a theorem only
  with a witness for its hypotheses and, for each attack, a proof that a cheap wrong implementation
  (a constant, doing nothing) fails the same law.
- **Tests** (`SpecTools.Tests`, `adapters/python_guards.py`): a guard of the implementation whose
  removal no property test notices.
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

Reproduce, from the repository's root (`DIR` any empty directory):

```bash
spec-tools synthetic gvariants 20261107 30 20 0 DIR blind
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
