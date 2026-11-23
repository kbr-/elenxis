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

end SpecTools.Gaps

section ConfirmationControls
open SpecTools.Gaps SpecTools.Ledger

private def readingRow : Row := { id := "limit", clause := "Refuse at the limit." }
private def weakReading : Proposal := ⟨"too weak", "limit", "A boundary case is missing."⟩
private def extraReading : Proposal := ⟨"extra", "limit", "An extra premise is required."⟩

#guard (mergeReadings [readingRow] 3 [[weakReading, weakReading], [extraReading], []]).toOption ==
  some []
#guard ((mergeReadings [readingRow] 3 [[weakReading], [weakReading], []]).toOption.map
  (List.map Gap.key)) == some [("limit", .tooWeak)]
#guard (mergeReadings [readingRow] 5 [[weakReading], [weakReading], [], [], []]).toOption == some []
#guard ((mergeReadings [readingRow] 5 [[weakReading], [weakReading], [weakReading], [], []]).toOption.map
  (List.map Gap.key)) == some [("limit", .tooWeak)]
#guard !(mergeReadings [readingRow] 3 [[weakReading], [weakReading]]).isOk

end ConfirmationControls
