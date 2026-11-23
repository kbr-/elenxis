import SpecTools.Adversarial

open Lean Elab Command SpecTools.Adversarial

set_option specTools.adversarial.root "AdversarialFixture"

namespace AdversarialFixture

abbrev Op := Nat → List Nat → Nat

def meaning (op : Op) : Prop := ∀ state input, op state input = state + input.sum
def weak (op : Op) : Prop := ∀ state, op state [] = state
def correct : Op := fun state input => state + input.sum
def noOp : Op := fun state _ => state

private theorem domain : ∃ _state : Nat, ∃ _input : List Nat, True := ⟨0, [], trivial⟩
theorem weakDomain : ∃ _state : Nat, True := ⟨0, trivial⟩

theorem noOp_rejected : ¬ meaning noOp := by
  intro accepted
  have bad := accepted 0 [1]
  change 0 = 1 at bad
  cases bad

theorem noOp_satisfies_weak : weak noOp := by intro state; rfl

def entry : SemanticEntry := {
  theoremName := `AdversarialFixture.conformance
  law := ``meaning
  implementation := ``correct
  witness := ``domain
  attacks := [{
    description := "Return the original state without processing input"
    mutant := ``noOp
    refutation := ``noOp_rejected }]
}

adversarial_claim entry in
theorem conformance : meaning correct := by intro state input; rfl

theorem correct_empty : weak correct := by intro state; rfl

def supporting : SupportingEntry := {
  theoremName := ``correct_empty
  parent := ``conformance
  law := ``weak
  implementation := ``correct
  witness := ``weakDomain
  mutant := ``noOp
  survival := ``noOp_satisfies_weak
  survivingModel := "An empty-input identity also admits doing nothing on nonempty input"
}

def expectRefusal (label : String) (action : CommandElabM Unit) : CommandElabM Unit := do
  let refused ← try
    action
    pure false
  catch _ => pure true
  unless refused do throwError "Adversarial negative control accepted: {label}"
  IO.println s!"Rejected as required: {label}"

axiom unsupportedRefutation : ¬ meaning noOp

run_cmd do
  let before ← get
  let unrelated ← `(command|
    adversarial_claim entry in
    theorem unrelated : True := True.intro)
  elabCommand unrelated
  let messages ← (← get).messages.toList.mapM fun message => message.data.toString
  set before
  unless messages.any ("Adversarial claim names".isPrefixOf ·) do
    throwError "The wrapper accepted a theorem unrelated to its declared contract"
  checkSemantic entry
  expectRefusal "no attacks" (preflight {entry with attacks := []})
  expectRefusal "wrong hypothesis witness" (preflight {entry with witness := ``weakDomain})
  expectRefusal "weak law with a refutation of a different law"
    (preflight {entry with law := ``weak, witness := ``weakDomain})
  expectRefusal "supporting law presented as semantic conformance"
    (checkSemantic {entry with theoremName := ``noOp_satisfies_weak})
  expectRefusal "unproved refutation"
    (preflight {entry with attacks := [{
      description := "No-op"
      mutant := ``noOp
      refutation := ``unsupportedRefutation }]})
  expectRefusal "missing implementation" (preflight {entry with implementation := `Missing.model})
  checkSupporting supporting [entry]
  expectRefusal "support without its semantic parent" (checkSupporting supporting [])
  expectRefusal "support with an unchecked parent"
    (checkSupporting supporting [{ entry with witness := ``weakDomain }])
  expectRefusal "support with unrelated mutant"
    (checkSupporting {supporting with mutant := ``correct} [entry])
  expectRefusal "an omitted theorem" (audit `AdversarialFixture [entry] [])
  expectRefusal "automatic coverage before a completed audit" enforceCoverage
  audit `AdversarialFixture [entry] [supporting]
  enforceCoverage
  let declarations ← inventory `AdversarialFixture
  unless declarations.size == 6 do
    throwError "Inventory lost or generated a fixture theorem: {declarations.size}"
  IO.println "PASS: typed semantic admission, witnesses and no-op countermodel controls"

end AdversarialFixture
