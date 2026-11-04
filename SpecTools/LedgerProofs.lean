import SpecTools.Ledger

/-!
The audit's verdicts, proved over all facts and rows: a missing name, an unaccepted axiom, a
hypothesis without a witness and an unclaimed theorem each show; a second run with nothing changed
re-judges nothing, and a changed row is re-judged while unchanged ones aren't.
-/

namespace SpecTools.Ledger
open Lean

theorem firstMissing_none {facts : Facts} {names : List Name} (h : firstMissing facts names = none) :
    ∀ n ∈ names, (facts n).isSome := by
  induction names with
  | nil => simp
  | cons m ms ih =>
    simp only [firstMissing] at h
    split at h
    · cases h
    · rename_i hm
      intro n hn
      rcases List.mem_cons.mp hn with rfl | hn
      · cases hf : facts n <;> simp_all
      · exact ih h n hn

theorem firstMissing_some {facts : Facts} {names : List Name} {n : Name}
    (h : firstMissing facts names = some n) : n ∈ names ∧ facts n = none := by
  induction names with
  | nil => simp [firstMissing] at h
  | cons m ms ih =>
    simp only [firstMissing] at h
    split at h
    · rename_i hm
      cases h
      exact ⟨List.mem_cons_self, by simpa using hm⟩
    · exact ⟨List.mem_cons_of_mem _ (ih h).1, (ih h).2⟩

/-- A row naming something that is no theorem is refused, naming it. -/
theorem verdict_missing (facts : Facts) (row : Row) (n : Name) (hn : n ∈ row.theorems ++ row.witnesses)
    (h : facts n = none) : ∃ m, verdict facts row = .missing m ∧ m ∈ row.theorems ++ row.witnesses ∧
      facts m = none := by
  unfold verdict
  split
  · rename_i m hm
    exact ⟨m, rfl, firstMissing_some hm⟩
  · rename_i hm
    have := firstMissing_none hm n hn
    simp [h] at this

/-- A proved verdict means: every name is a theorem, there is at least one, none rests on an
unaccepted axiom, and a hypothesis comes with a witness. -/
theorem verdict_proved (facts : Facts) (row : Row) (h : verdict facts row = .proved) :
    (∀ n ∈ row.theorems ++ row.witnesses, (facts n).isSome) ∧ row.theorems ≠ [] ∧
      unaccepted facts (row.theorems ++ row.witnesses) = [] ∧
      (row.theorems.any (fun n => (facts n).any (·.hypotheses)) → row.witnesses ≠ []) := by
  unfold verdict at h
  split at h
  · cases h
  · rename_i hm
    refine ⟨firstMissing_none hm, ?_⟩
    split at h
    · cases h
    · rename_i hne
      split at h
      · cases h
      · rename_i hu
        refine ⟨by simpa using hne, hu, ?_⟩
        split at h
        · cases h
        · rename_i hw
          intro hany hnil
          apply hw
          simp [hnil, hany]

/-- An axiom outside the accepted three makes the row conditional. -/
theorem verdict_conditional (facts : Facts) (row : Row) (hall : firstMissing facts (row.theorems ++ row.witnesses) = none)
    (hne : row.theorems ≠ []) (a : Name) (as : List Name)
    (hu : unaccepted facts (row.theorems ++ row.witnesses) = a :: as) :
    verdict facts row = .conditional (a :: as) := by
  have : row.theorems.isEmpty = false := by simpa using hne
  simp [verdict, hall, this, hu]

/-- Hypotheses with no witness make the row too weak or vacuous. -/
theorem verdict_vacuous (facts : Facts) (row : Row) (hall : firstMissing facts row.theorems = none)
    (hne : row.theorems ≠ []) (hw : row.witnesses = [])
    (hu : unaccepted facts row.theorems = [])
    (hyp : row.theorems.any (fun n => (facts n).any (·.hypotheses)) = true) :
    verdict facts row = .tooWeakOrVacuous := by
  have : row.theorems.isEmpty = false := by simpa using hne
  simp [verdict, hw, hall, this, hu, hyp]

/-- A written theorem is reported exactly when no row claims it. -/
theorem mem_unclaimed (rows : List Row) (written : List Name) (n : Name) :
    n ∈ unclaimed rows written ↔ n ∈ written ∧ ∀ r ∈ rows, n ∉ r.theorems ++ r.witnesses := by
  simp [unclaimed]

/-- A second run after storing a run's digests re-judges no row. -/
theorem toRejudge_after_store (facts : Facts) (rows : List Row) (hids : (rows.map (·.id)).Nodup) :
    toRejudge (digests facts rows) facts rows = [] := by
  rw [toRejudge, List.filter_eq_nil_iff]
  intro r hr
  simp only [bne_iff_ne, ne_eq, Decidable.not_not]
  induction rows with
  | nil => simp at hr
  | cons s ss ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hids
    simp only [digests, List.map_cons, List.lookup_cons]
    rcases List.mem_cons.mp hr with rfl | hr
    · simp
    · have hne : (r.id == s.id) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro he
        exact hids.1 ⟨r, hr, he⟩
      simp only [hne]
      exact ih hids.2 hr

/-- Only rows whose digest moved are re-judged: a row whose stored digest equals its current one is
not, and one whose digest changed is. -/
theorem mem_toRejudge (stored : List (String × UInt64)) (facts : Facts) (rows : List Row) (r : Row) :
    r ∈ toRejudge stored facts rows ↔ r ∈ rows ∧ stored.lookup r.id ≠ some (digest facts r) := by
  simp [toRejudge]

end SpecTools.Ledger
