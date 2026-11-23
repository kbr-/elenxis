import SpecTools.Gaps

/-!
`gaps`' guarantees: checked inconsistent premises are reported with no proposal; a proposal naming
a row the ledger lacks is refused, never printed; each accepted proposal is printed under its kind.
-/

namespace SpecTools.Gaps
open Lean SpecTools.Ledger

/-- Checked inconsistent premises are reported even when the model proposes nothing. -/
theorem contradiction_without_model (facts : Facts) (rows : List Row) (r : Row) (hr : r ∈ rows)
    (checked : CheckedEvidence) (hv : verdict facts r checked = .inconsistentPremises) :
    ∃ g ∈ (gather facts rows [] checked).byKind .tooWeak, g.row = r.id := by
  refine ⟨⟨.tooWeak, r.id, "checked evidence proves a theorem's premises inconsistent"⟩, ?_, rfl⟩
  simp only [gather, List.filterMap_nil, List.append_nil, List.mem_filter, decided,
    List.mem_filterMap]
  exact ⟨⟨r, hr, by rw [hv]; rfl⟩, by decide⟩

/-- A proposal naming a row the ledger lacks is refused. -/
theorem accept_unknown_row (rows : List Row) (p : Proposal) (h : ∀ r ∈ rows, r.id ≠ p.row) :
    ∃ e, accept rows p = .error e := by
  unfold accept
  split
  · exact ⟨_, rfl⟩
  · have : rows.any (·.id == p.row) = false := by
      simpa using fun r hr => h r hr
    simp [this]

/-- An accepted proposal is printed under its own kind. -/
theorem accepted_printed (facts : Facts) (rows : List Row) (ps : List Proposal) (p : Proposal)
    (g : Gap) (hp : p ∈ ps) (hg : accept rows p = .ok g) :
    g ∈ (gather facts rows ps).byKind g.kind := by
  simp only [gather, List.mem_filter, beq_self_eq_true, and_true]
  apply List.mem_append_right
  exact List.mem_filterMap.mpr ⟨p, hp, by simp [hg, Except.toOption]⟩

/-- Witness: a row whose verdict is too weak or vacuous. -/
example : (verdict (fun n => if n == `t then some { statement := "", axioms := [], hypotheses := true } else none)
    { id := "r", clause := "c", theorems := [`t] } == .tooWeakOrVacuous) = true := by decide

/-- Witness: a proposal naming a row the ledger lacks. -/
example : ∀ r ∈ [({ id := "r", clause := "c" } : Row)], r.id ≠ "s" := by decide

theorem mergeReadings_wrong_count (rows : List Row) (count : Nat)
    (readings : List (List Proposal)) (wrong : readings.length ≠ count) :
    ∃ message, mergeReadings rows count readings = .error message := by
  have refused : (decide (count = 0) || readings.length != count) = true := by simp [wrong]
  unfold mergeReadings
  rw [ite_eq_left refused]
  exact ⟨_, rfl⟩

theorem mergeReadings_majority (rows : List Row) (count : Nat)
    (readings : List (List Proposal)) (parsed : List (List Gap)) (result : List Gap)
    (parses : readings.mapM (List.mapM (accept rows)) = .ok parsed)
    (merged : mergeReadings rows count readings = .ok result) :
    ∀ key, (∃ gap ∈ result, gap.key = key) ↔
      (∃ gap ∈ parsed.flatten, gap.key = key) ∧ count < 2 * votes key parsed := by
  unfold mergeReadings at merged
  split at merged
  · cases merged
  · rw [parses] at merged
    have resultEq := Except.ok.inj merged
    rw [← resultEq]
    intro key
    constructor
    · rintro ⟨gap, member, same⟩
      obtain ⟨candidate, _, emitted⟩ := List.mem_filterMap.mp member
      split at emitted
      · rename_i majority
        have sameCandidate : gap.key = candidate := by simpa using List.find?_some emitted
        refine ⟨⟨gap, List.mem_of_find?_eq_some emitted, same⟩, ?_⟩
        rw [← same, sameCandidate]
        exact (majority_iff count candidate parsed).mp majority
      · simp at emitted
    · rintro ⟨⟨gap, source, same⟩, majority⟩
      have inKeys : key ∈ (parsed.flatten.map Gap.key).eraseDups :=
        List.mem_eraseDups.mpr (List.mem_map.mpr ⟨gap, source, same⟩)
      have allowed := (majority_iff count key parsed).mpr majority
      cases found : parsed.flatten.find? (fun g => g.key == key) with
      | none => exact False.elim ((List.find?_eq_none.mp found) gap source (by simp [same]))
      | some representative =>
        exact ⟨representative, List.mem_filterMap.mpr ⟨key, inKeys, by simp [allowed, found]⟩,
          by simpa using List.find?_some found⟩

end SpecTools.Gaps
