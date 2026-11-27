-- SPDX-License-Identifier: Apache-2.0
import SpecTools.ScoreEvidence

namespace SortingExample
open SpecTools.Score.Evidence

abbrev Sample := Observation (List Nat) (List Nat) Unit

def sortedPermutation (sample : Sample) : Prop :=
  sample.outcome.Pairwise (· ≤ ·) ∧ sample.outcome.Perm sample.input

def orderedOnly (sample : Sample) : Prop := sample.outcome.Pairwise (· ≤ ·)

def capped (sample : Sample) : Prop :=
  sortedPermutation sample ∧ sample.outcome.length ≤ 10

instance : DecidablePred sortedPermutation := fun sample =>
  inferInstanceAs (Decidable (sample.outcome.Pairwise (· ≤ ·) ∧ sample.outcome.Perm sample.input))
instance : DecidablePred orderedOnly := fun sample =>
  inferInstanceAs (Decidable (sample.outcome.Pairwise (· ≤ ·)))
instance : DecidablePred capped := fun sample =>
  inferInstanceAs (Decidable (sortedPermutation sample ∧ sample.outcome.length ≤ 10))

def returnEmpty (_input : List Nat) : List Nat := []
def droppedInput : Sample := ⟨[2, 1, 2], returnEmpty [2, 1, 2], []⟩
def longSorted : Sample := ⟨List.range 11, List.range 11, []⟩

theorem missingPermutation :
    BoundDistinction "permutation" sortedPermutation orderedOnly .admitsExtra droppedInput := by
  constructor
  change orderedOnly droppedInput ∧ ¬ sortedPermutation droppedInput
  simp [orderedOnly, sortedPermutation, droppedInput, returnEmpty]

theorem unnecessaryCap :
    BoundDistinction "length-cap" sortedPermutation capped .rejectsRequired longSorted := by
  constructor
  change sortedPermutation longSorted ∧ ¬ capped longSorted
  have sorted : sortedPermutation longSorted := ⟨by decide, List.Perm.refl _⟩
  have aboveLimit : ¬ longSorted.outcome.length ≤ 10 := by decide
  exact ⟨sorted, fun restricted => aboveLimit restricted.2⟩

def shortLists : List (List Nat) := [[], [0], [1]]

def shortBinary (values : List Nat) : Prop :=
  values.length ≤ 1 ∧ ∀ value ∈ values, value < 2

theorem shortLists_exact (values : List Nat) : values ∈ shortLists ↔ shortBinary values := by
  cases values with
  | nil => simp [shortLists, shortBinary]
  | cons value rest =>
    cases rest with
    | nil => simp [shortLists, shortBinary]; omega
    | cons value' rest => simp [shortLists, shortBinary]

def shortObservations : List Sample :=
  shortLists.flatMap fun input => shortLists.map fun output => ⟨input, output, []⟩

theorem shortObservations_exact (sample : Sample) :
    sample ∈ shortObservations ↔
      shortBinary sample.input ∧ shortBinary sample.outcome ∧ sample.effects = [] := by
  constructor
  · intro member
    obtain ⟨input, inputMem, outputMembers⟩ := List.mem_flatMap.mp member
    obtain ⟨output, outputMem, rfl⟩ := List.mem_map.mp outputMembers
    exact ⟨(shortLists_exact _).mp inputMem, (shortLists_exact _).mp outputMem, rfl⟩
  · rcases sample with ⟨input, output, effects⟩
    rintro ⟨inScope, outScope, rfl⟩
    exact List.mem_flatMap.mpr ⟨input, (shortLists_exact _).mpr inScope,
      List.mem_map.mpr ⟨output, (shortLists_exact _).mpr outScope, rfl⟩⟩

theorem identicalOutput_agrees :
    compareObservation sortedPermutation orderedOnly (⟨[1], [1], []⟩ : Sample) = none := by
  apply (compareObservation_none_iff _ _ _).mpr
  simp [sortedPermutation, orderedOnly]

theorem cap_absent_in_short_domain :
    searchObservations sortedPermutation capped shortObservations = none := by
  apply (searchObservations_none_iff _ _ _).mpr
  intro sample inDomain
  have length := ((shortObservations_exact _).mp inDomain).2.1.1
  simp [capped, show sample.outcome.length ≤ 10 by omega]

theorem cap_found_in_extended_domain :
    (searchObservations sortedPermutation capped (shortObservations ++ [longSorted])).map
        Counterexample.direction = some .rejectsRequired := by
  rw [searchObservations, List.findSome?_append]
  change (searchObservations sortedPermutation capped shortObservations <|>
      [longSorted].findSome? (compareObservation sortedPermutation capped)).map
        Counterexample.direction = _
  rw [cap_absent_in_short_domain]
  decide

def describeSample (sample : Sample) : String :=
  s!"Input {sample.input} produces output {sample.outcome}."

#eval IO.println <| describeBound missingPermutation `SortingExample.missingPermutation fun sample =>
  describeSample sample ++ " The empty output is ordered and discards the input."
#eval IO.println <| describeBound unnecessaryCap `SortingExample.unnecessaryCap fun sample =>
  describeSample sample ++ " The output is an ordered permutation and exceeds the cap of ten."
#eval IO.println <| describeSearch `SortingExample.cap_absent_in_short_domain
  "binary inputs and outputs of length at most one, with no effects" describeSample
  (searchObservations sortedPermutation capped shortObservations)

end SortingExample

#score_journal "examples/sorting/score-key.json" "examples/sorting/score-findings.json"
