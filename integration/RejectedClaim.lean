import SpecTools.Adversarial

open SpecTools.Adversarial

def noRefutations : SemanticEntry := {
  theoremName := `rejected
  law := `unusedLaw
  implementation := `unusedImplementation
  witness := `unusedWitness
  attacks := [] }

adversarial_claim noRefutations in
theorem rejected : True := by
  fail "A refused declaration must not elaborate its body"
