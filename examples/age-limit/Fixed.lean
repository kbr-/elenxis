import SpecTools.Audit
import SpecTools.GapsRun

/-!
The specification of `Wrong.lean` after a person read its finding and decided the requirement was
right and the formalization wrong: the limit is 18, in the decision and in its theorem.

Run from the repository's root:

    SPEC_TOOLS_BACKEND=$PWD/examples/backend.json lake env lean examples/age-limit/Fixed.lean
-/

namespace AgeLimit

inductive Decision where
  | approved | refused
  deriving DecidableEq

/-- The decision on an applicant of the given age. -/
def decide (age : Nat) : Decision := if age < 18 then .refused else .approved

/-- "A loan is refused to an applicant under 18." -/
theorem refuses_minors (age : Nat) (h : age < 18) : decide age = .refused := by
  simp [decide, h]

/-- The hypothesis can hold: a 17-year-old applicant. -/
theorem minor_exists : ∃ age : Nat, ∃ _h : age < 18, True := ⟨17, by decide, trivial⟩

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
