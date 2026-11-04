import SpecTools.Gaps

/-!
`gaps`' guarantees: a row too weak or vacuous is reported with no proposal at all; a proposal naming
a row the ledger lacks is refused, never printed; each accepted proposal is printed under its kind.
-/

namespace SpecTools.Gaps
open Lean SpecTools.Ledger

/-- A too-weak row is reported even when the model proposes nothing. -/
theorem tooWeak_without_model (facts : Facts) (rows : List Row) (r : Row) (hr : r ∈ rows)
    (hv : verdict facts r = .tooWeakOrVacuous) :
    ∃ g ∈ (gather facts rows []).byKind .tooWeak, g.row = r.id := by
  refine ⟨⟨.tooWeak, r.id, "its theorems have hypotheses and no witness shows they can hold"⟩, ?_, rfl⟩
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
example : (verdict (fun n => if n == `t then some ⟨"", [], true⟩ else none)
    { id := "r", clause := "c", theorems := [`t] } == .tooWeakOrVacuous) = true := by decide

/-- Witness: a proposal naming a row the ledger lacks. -/
example : ∀ r ∈ [({ id := "r", clause := "c" } : Row)], r.id ≠ "s" := by decide

end SpecTools.Gaps
