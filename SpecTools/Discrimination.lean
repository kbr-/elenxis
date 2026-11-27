-- SPDX-License-Identifier: Apache-2.0
import Lean.Data.Json

/-! Directional comparison of two contracts on a common typed observation domain. -/

namespace SpecTools.Score.Evidence
open Lean

structure Observation (Input : Type u) (Outcome : Type v) (Effect : Type w) where
  input : Input
  outcome : Outcome
  effects : List Effect := []

def Observation.acceptedBy (contract : Input → Outcome → List Effect → Prop)
    (observation : Observation Input Outcome Effect) : Prop :=
  contract observation.input observation.outcome observation.effects

inductive Direction where
  | admitsExtra
  | rejectsRequired
  deriving DecidableEq, FromJson, ToJson

def Direction.description : Direction → String
  | .admitsExtra => "too weak (candidate admits behavior excluded by the reference)"
  | .rejectsRequired => "too strong (candidate rejects behavior required by the reference)"

def Distinguishes {Input : Type u} (reference candidate : Input → Prop)
    (direction : Direction) (input : Input) : Prop :=
  match direction with
  | .admitsExtra => candidate input ∧ ¬ reference input
  | .rejectsRequired => reference input ∧ ¬ candidate input

structure BoundDistinction {Input : Type u} (property : String) (reference candidate : Input → Prop)
    (direction : Direction) (input : Input) : Prop where
  distinguishes : Distinguishes reference candidate direction input

theorem directions_disjoint {Input : Type u} {reference candidate : Input → Prop} {input : Input}
    (extra : Distinguishes reference candidate .admitsExtra input)
    (missing : Distinguishes reference candidate .rejectsRequired input) : False :=
  extra.2 missing.1

structure TooWeak {α : Type u} (reference candidate : α → Prop) where
  observation : α
  evidence : Distinguishes reference candidate .admitsExtra observation

structure TooStrong {α : Type u} (reference candidate : α → Prop) where
  observation : α
  evidence : Distinguishes reference candidate .rejectsRequired observation

inductive Counterexample {α : Type u} (reference candidate : α → Prop) where
  | tooWeak (witness : TooWeak reference candidate)
  | tooStrong (witness : TooStrong reference candidate)

def Counterexample.direction {reference candidate : α → Prop} :
    Counterexample reference candidate → Direction
  | .tooWeak _ => .admitsExtra
  | .tooStrong _ => .rejectsRequired

def Counterexample.observation {reference candidate : α → Prop} : Counterexample reference candidate → α
  | .tooWeak witness => witness.observation
  | .tooStrong witness => witness.observation

theorem Counterexample.sound {reference candidate : α → Prop}
    (witness : Counterexample reference candidate) :
    Distinguishes reference candidate witness.direction witness.observation := by
  cases witness with
  | tooWeak w => exact w.evidence
  | tooStrong w => exact w.evidence

/-- A supplied observation produces evidence only in the direction in which its contracts differ. -/
def compareObservation (reference candidate : α → Prop) [DecidablePred reference]
    [DecidablePred candidate] (sample : α) : Option (Counterexample reference candidate) :=
  if accepted : reference sample then
    if offered : candidate sample then none else some (.tooStrong ⟨sample, accepted, offered⟩)
  else
    if offered : candidate sample then some (.tooWeak ⟨sample, offered, accepted⟩) else none

theorem compareObservation_none_iff (reference candidate : α → Prop) [DecidablePred reference]
    [DecidablePred candidate] (sample : α) :
    compareObservation reference candidate sample = none ↔ (reference sample ↔ candidate sample) := by
  by_cases accepted : reference sample <;> by_cases offered : candidate sample <;>
    simp [compareObservation, accepted, offered]

theorem compareObservation_preserves_sample (reference candidate : α → Prop)
    [DecidablePred reference] [DecidablePred candidate] (sample : α)
    (witness : Counterexample reference candidate)
    (found : compareObservation reference candidate sample = some witness) :
    witness.observation = sample := by
  unfold compareObservation at found
  split at found <;> split at found <;> cases found <;> rfl

/-- Search the supplied observations in order, retaining the first checked discrepancy. -/
def searchObservations (reference candidate : α → Prop) [DecidablePred reference]
    [DecidablePred candidate] (samples : List α) : Option (Counterexample reference candidate) :=
  samples.findSome? (compareObservation reference candidate)

theorem searchObservations_none_iff (reference candidate : α → Prop) [DecidablePred reference]
    [DecidablePred candidate] (samples : List α) :
    searchObservations reference candidate samples = none ↔
      ∀ sample ∈ samples, reference sample ↔ candidate sample := by
  simp only [searchObservations, List.findSome?_eq_none_iff, compareObservation_none_iff]

theorem searchObservations_mem (reference candidate : α → Prop) [DecidablePred reference]
    [DecidablePred candidate] (samples : List α) (witness : Counterexample reference candidate)
    (found : searchObservations reference candidate samples = some witness) :
    witness.observation ∈ samples := by
  obtain ⟨sample, member, localFound⟩ := List.exists_of_findSome?_eq_some found
  simpa only [compareObservation_preserves_sample reference candidate sample witness localFound]
    using member

structure Enumeration (α : Type u) where
  samples : List α
  complete : ∀ sample, sample ∈ samples

theorem searchExhaustive_none_iff (reference candidate : α → Prop) [DecidablePred reference]
    [DecidablePred candidate] (domain : Enumeration α) :
    searchObservations reference candidate domain.samples = none ↔
      ∀ sample, reference sample ↔ candidate sample := by
  rw [searchObservations_none_iff]
  exact ⟨fun agrees sample => agrees sample (domain.complete sample),
    fun agrees sample _ => agrees sample⟩

def describeWitness (identifier : String) (direction : Direction) (scenario : String) : String :=
  s!"{identifier}: {direction.description}\n{scenario}"

def describeBound {reference candidate : α → Prop} {property : String} {direction : Direction}
    {sample : α} (_evidence : BoundDistinction property reference candidate direction sample)
    (identifier : Name) (scenario : α → String) : String :=
  describeWitness identifier.toString direction (scenario sample)

def describeSearch {reference candidate : α → Prop} (identifier : Name) (domain : String)
    (scenario : α → String) : Option (Counterexample reference candidate) → String
  | none => s!"No distinction in {domain}. Beyond this domain: unknown."
  | some witness => describeWitness identifier.toString witness.direction (scenario witness.observation)

end SpecTools.Score.Evidence
