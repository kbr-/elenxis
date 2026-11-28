-- SPDX-License-Identifier: Apache-2.0
import SpecTools.RelationAudit
import SpecTools.RequirementView

namespace RelationReview
open SpecTools.RelationAudit Lean Elab Command

def allowed (_ : Unit) := True
def nowhere (_ : Unit) := False
def input := ()
def one := 1
def ab (_ : Unit) (y : Nat) := y = 0 ∨ y = 1
def bc (_ : Unit) (y : Nat) := y = 1 ∨ y = 2
def ca (_ : Unit) (y : Nat) := y = 2 ∨ y = 0

theorem ab_bc : total allowed (together ab bc) := fun _ _ => ⟨1, Or.inr rfl, Or.inl rfl⟩
theorem oneAccepted : admitsAt allowed (together ab bc) input one := ⟨trivial, Or.inr rfl, Or.inl rfl⟩
theorem bc_ca : total allowed (together bc ca) := fun _ _ => ⟨2, Or.inr rfl, Or.inl rfl⟩
theorem ab_ca : total allowed (together ab ca) := fun _ _ => ⟨0, Or.inl rfl, Or.inr rfl⟩
theorem missing : missingAt allowed (together (together ab bc) ca) input := by
  refine ⟨trivial, ?_⟩
  rintro ⟨y, ⟨hab, hbc⟩, hca⟩
  simp [ab, bc, ca] at *
  omega
theorem noTotal : ¬ total allowed (together (together ab bc) ca) := missing_refutes_total missing
theorem vacuous : total nowhere ab := fun _ h => h.elim
theorem emptyDomain : ¬ inhabited nowhere ab := fun ⟨_, h, _⟩ => h
theorem ambiguous : ¬ uniqueOutputs allowed ab := fun h =>
  Nat.zero_ne_one (h () trivial 0 1 (Or.inl rfl) (Or.inr rfl))

def anySize (_ : Nat) := True
def first (n : Nat) (y : Fin (n + 1)) := y.val = 0
theorem firstExists : total anySize first := fun _ _ => ⟨0, rfl⟩
theorem firstUnique : uniqueOutputs anySize first := fun _ _ _ _ hy hz => Fin.ext (hy.trans hz.symm)

def runCase (names : List (String × Name)) (scope : SpecTools.RelationAudit.Scope) (yes no : List Name)
    (expected : String) (a := ``allowed) : CommandElabM Json := do
  let report ← review ⟨a, names, scope, yes, no⟩
  unless (report.getObjValAs? String "status").toOption == some expected do throwError "{report}"
  return report

run_cmd do
  let a := ("A", ``ab)
  let b := ("B", ``bc)
  let c := ("C", ``ca)
  discard <| runCase [("first", ``first)] .total [``firstExists] [] "established" ``anySize
  discard <| runCase [("first", ``first)] .uniqueOutputs [``firstUnique] [] "established" ``anySize
  discard <| runCase [a,b] (.admitsAt ``input ``one) [``oneAccepted] [] "established"
  for (members, cert) in [([a,b], ``ab_bc), ([b,c], ``bc_ca), ([a,c], ``ab_ca)] do
    discard <| runCase members .total [cert] [] "established"
  let group ← runCase [a,b,c] .total [``ab_bc] [``noTotal] "refuted"
  discard <| runCase [a,b,c] (.missingAt ``input) [``missing] [] "established"
  discard <| runCase [a,b,c] .total [``ab_bc] [] "unresolved"
  discard <| runCase [a] .uniqueOutputs [] [``ambiguous] "refuted"
  discard <| runCase [a] .total [``vacuous] [] "established" ``nowhere
  discard <| runCase [a] .inhabited [] [``emptyDomain] "refuted" ``nowhere
  for id in ["A","B","C","D"] do
    let joined ← ofExcept <| SpecTools.RequirementView.view id [⟨group, some group⟩]
    let dims ← ofExcept <| joined.getObjVal? "dimensions"
    let groups ← ofExcept <| dims.getObjValAs? (List Json) "consistency"
    unless groups.length == (if id == "D" then 0 else 1) do throwError "{joined}"
  IO.println group.compress

end RelationReview

open Lean Elab Command SpecTools.Evidence in
run_cmd do
  let snapshot (boundary : Nat) (wording options : String) := withoutModifyingEnv do
    let helper := `FreshnessFixture.boundary
    let subject := `FreshnessFixture.limit
    for (name, body) in [(helper, mkNatLit boundary), (subject, mkConst helper)] do
      liftCoreM <| addDecl <| .defnDecl {
        name, type := mkConst ``Nat, value := body, levelParams := [],
        hints := .abbrev, safety := .safe }
    return capture (← getEnv) "fixture" (toJson ("v1", wording, options)) [subject]
  let saved ← snapshot 24 "hours before" "inclusive"
  unless freshness saved (← snapshot 24 "hours before" "inclusive") == "current" do
    throwError "Replay changed fingerprint"
  for changed in [← snapshot 23 "hours before" "inclusive", ← snapshot 24 "hours after" "inclusive",
      ← snapshot 24 "hours before" "strict"] do
    unless freshness saved changed == "stale" do throwError "Missed change at the same revision"
  unless freshness none saved == "unknown" && freshness saved none == "unknown" do
    throwError "A missing snapshot acquired a freshness verdict"
