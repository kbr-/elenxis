import SpecTools.Audit
import SpecTools.GapsRun

/-!
A synthetic demonstration: `loans.md` asks that a loan be refused to an applicant under 18, and this
specification formalizes the limit as 16. Its theorem is proved and its hypothesis has a witness, so
Lean has nothing to object to; `Fixed.lean` is the specification after a person reads the finding.

Run from the repository's root:

    lake env lean examples/age-limit/Wrong.lean   # the audit, no model
    SPEC_TOOLS_BACKEND=$PWD/examples/backend.json lake env lean examples/age-limit/Wrong.lean
                                                  # gaps too, a live model call
-/

namespace AgeLimit

inductive Decision where
  | approved | refused
  deriving DecidableEq

/-- The decision on an applicant of the given age. -/
def decide (age : Nat) : Decision := if age < 16 then .refused else .approved

/-- "A loan is refused to an applicant under 18", formalized with the wrong limit. -/
theorem refuses_minors (age : Nat) (h : age < 16) : decide age = .refused := by
  simp [decide, h]

/-- The hypothesis can hold: a 15-year-old applicant. -/
theorem minor_exists : ∃ age : Nat, ∃ _h : age < 16, True := ⟨15, by decide, trivial⟩

def ledger : List SpecTools.Ledger.Row := [
  { id := "minors", source := "loans.md, 1",
    clause := "A loan is refused to an applicant under 18.",
    theorems := [``refuses_minors], evidence := [⟨``refuses_minors, ``minor_exists, .inhabited⟩] } ]

end AgeLimit

#eval SpecTools.Audit.run AgeLimit.ledger `AgeLimit

-- With `SPEC_TOOLS_BACKEND` naming a backend configuration, the gaps against `loans.md` too.
#eval show Lean.Elab.Command.CommandElabM Unit from do
  if (← IO.getEnv "SPEC_TOOLS_BACKEND").isSome then
    SpecTools.Gaps.runConfigured AgeLimit.ledger (← IO.FS.readFile "examples/age-limit/loans.md")
