import SpecTools.Audit
import SpecTools.GapsRun

/-!
Two clauses of `refund.md`, each stated by a theorem Lean's kernel accepts, and each statement
saying less than its clause. Lean checks a proof against its statement, never the statement against
the requirement: these two gaps are what the audit and `gaps` exist to find.

Run from the repository's root:

    lake env lean examples/refund/Refund.lean
    SPEC_TOOLS_BACKEND=$PWD/examples/backend.json lake env lean examples/refund/Refund.lean
                                            # gaps too, a live model call
-/

namespace Refund

/-- What a customer gets back: what they paid, less what they used. -/
def refund (paid used : Nat) : Nat := paid - used

/-- Clause 1, "a refund never exceeds the amount the customer paid", stated for the customer who
used nothing: it has no hypotheses and is proved, yet says nothing about any other order. -/
theorem refund_le_paid (paid : Nat) : refund paid 0 ≤ paid := by
  simp [refund]

/-- Clause 2, "a customer who used nothing gets back everything they paid", under a hypothesis no
order meets: `used = 0 ∧ used > 0` is false, so the kernel accepts any conclusion. -/
theorem full_refund (paid used : Nat) (h : used = 0 ∧ used > 0) : refund paid used = paid := by
  omega

theorem inconsistent_refund_premises :
    ¬ (∃ _paid : Nat, ∃ used : Nat, ∃ _h : used = 0 ∧ used > 0, True) := by
  intro ⟨_, used, ⟨zero, positive⟩, _⟩
  omega

def ledger : List SpecTools.Ledger.Row := [
  { id := "bounded", source := "refund.md, 1",
    clause := "A refund never exceeds the amount the customer paid.",
    theorems := [``refund_le_paid] },
  { id := "full", source := "refund.md, 2",
    clause := "A customer who used nothing gets back everything they paid.",
    theorems := [``full_refund],
    evidence := [⟨``full_refund, ``inconsistent_refund_premises, .inconsistent⟩] } ]

end Refund

#eval SpecTools.Audit.run Refund.ledger `Refund

-- With `SPEC_TOOLS_BACKEND` naming a backend configuration, the gaps against `refund.md` too.
#eval show Lean.Elab.Command.CommandElabM Unit from do
  if (← IO.getEnv "SPEC_TOOLS_BACKEND").isSome then
    SpecTools.Gaps.runConfigured Refund.ledger (← IO.FS.readFile "examples/refund/refund.md")
