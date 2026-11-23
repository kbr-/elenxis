import SpecTools.FiniteGaps
import Lean.Elab.Command

namespace Loans

structure Req where
  kind : String
  vals : List (String × Nat)

def Req.get (q : Req) (field : String) : Nat := (q.vals.lookup field).getD 0
def rule : Unit := ()
def fires (_ : Unit) (_ : Req) : Bool := true

theorem standardSum (q : Req) (_ : q.kind = "borrow")
    (_ : 5 ≤ q.get "loans" + q.get "holds") : fires rule q = true := rfl

section
local instance : HAdd Nat Nat Nat := ⟨fun _ _ => 0⟩

theorem customSum (q : Req) (_ : q.kind = "borrow")
    (_ : 5 ≤ q.get "loans" + q.get "holds") : fires rule q = true := rfl
end

section
local instance : OfNat Nat 5 := ⟨99⟩

theorem customLiteral (q : Req) (_ : q.kind = "borrow")
    (_ : 5 ≤ q.get "loans") : fires rule q = true := rfl
end

end Loans

open Lean Elab Command SpecTools.FiniteGaps in
#eval show CommandElabM Unit from do
  let standard ← liftTermElabM do statementScope `Loans.standardSum
  unless standard == some (`Loans.rule, ⟨"borrow", ["loans", "holds"], 5, none, none⟩) do
    throwError "the standard generated sum was not recognized"
  let customSum ← liftTermElabM do statementScope `Loans.customSum
  let customLiteral ← liftTermElabM do statementScope `Loans.customLiteral
  unless customSum.isNone && customLiteral.isNone do
    throwError "custom arithmetic was interpreted as standard Nat operations"
