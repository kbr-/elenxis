import SpecTools.Score

/-!
The scorer's guarantees: every plant is found or missed, never both; findings on a variant planting
nothing are all false alarms; and a report quoting each planted clause finds all with none false.
-/

namespace SpecTools.Score
open SpecTools.Synthetic

theorem filter_split {α} (p : α → Bool) (l : List α) :
    (l.filter p).length + (l.filter (fun x => !p x)).length = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih => cases h : p x <;> simp [h] <;> omega

/-- Found and missed partition the key. -/
theorem found_missed (key : List Plant) (fs : List Finding) :
    (score key fs).found.length + (score key fs).missed.length = key.length := by
  simp only [score, List.length_map]
  exact filter_split _ key

/-- On a variant planting nothing, every finding is a false alarm and nothing is found. -/
theorem score_no_plants (fs : List Finding) :
    score [] fs = { found := [], missed := [], falseAlarms := fs.length } := by
  simp [score]

/-- A report quoting exactly the planted clauses finds every plant and raises no false alarm. -/
theorem score_exact (key : List Plant) :
    (score key (key.map fun p => ({ clause := p.clause, kind := p.kind } : Finding))).missed = [] ∧
    (score key (key.map fun p => ({ clause := p.clause, kind := p.kind } : Finding))).falseAlarms = 0 := by
  simp only [score]
  constructor
  · rw [List.map_eq_nil_iff, List.filter_eq_nil_iff]
    intro p hp
    have : (key.map fun p => ({ clause := p.clause, kind := p.kind } : Finding)).any (names · p) :=
      List.any_eq_true.mpr ⟨_, List.mem_map.mpr ⟨p, hp, rfl⟩, by simp [names]⟩
    simp [this]
  · rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro f hf
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hf
    have : key.any (names { clause := p.clause, kind := p.kind }) :=
      List.any_eq_true.mpr ⟨p, hp, by simp [names]⟩
    simp [this]

/-- The bar holds exactly when the ledger finds more blind spots and its false alarms stay within
the baseline's plus one a variant. -/
theorem barMet_iff (lb bb la ba n : Nat) :
    barMet lb bb la ba n = true ↔ bb < lb ∧ la ≤ ba + n := by
  simp [barMet]

/-- The bar's two ends at their values, and a tie in blind spots failing it whatever the alarms. -/
example : barMet 8 6 6 3 3 = true := by decide
example : barMet 8 6 7 3 3 = false := by decide
example : barMet 6 6 0 3 3 = false := by decide

end SpecTools.Score
