import SpecTools.ScoreEvidence

namespace SortingExample
open SpecTools.Score.Evidence

abbrev Sample := List Nat × List Nat

def sortedPermutation (sample : Sample) : Prop :=
  sample.2.Pairwise (· ≤ ·) ∧ sample.2.Perm sample.1

def orderedOnly (sample : Sample) : Prop := sample.2.Pairwise (· ≤ ·)

def capped (sample : Sample) : Prop :=
  sortedPermutation sample ∧ sample.2.length ≤ 10

def droppedInput : Sample := ([2, 1, 2], [])
def longSorted : Sample := (List.range 11, List.range 11)

theorem missingPermutation :
    BoundDistinction "permutation" sortedPermutation orderedOnly .admitsExtra droppedInput := by
  constructor
  change orderedOnly droppedInput ∧ ¬ sortedPermutation droppedInput
  simp [orderedOnly, sortedPermutation, droppedInput]

theorem unnecessaryCap :
    BoundDistinction "length-cap" sortedPermutation capped .rejectsRequired longSorted := by
  constructor
  change sortedPermutation longSorted ∧ ¬ capped longSorted
  have sorted : sortedPermutation longSorted := ⟨by decide, List.Perm.refl _⟩
  have aboveLimit : ¬ longSorted.2.length ≤ 10 := by decide
  exact ⟨sorted, fun restricted => aboveLimit restricted.2⟩

end SortingExample

#score_journal "examples/sorting/score-key.json" "examples/sorting/score-findings.json"
