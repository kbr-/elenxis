-- SPDX-License-Identifier: Apache-2.0
import SpecTools.Synthetic

/-!
The generator's guarantees: a variant planting nothing is the fixture itself, with an empty key; an
edit of a missing file, or whose text doesn't occur exactly once, is refused rather than applied in
part.
-/

namespace SpecTools.Synthetic

theorem applyEdits_nil (files : List (String × String)) : applyEdits files [] = .ok files := rfl

/-- An edit of a file the fixture lacks is refused. -/
theorem applyEdit_no_file (files : List (String × String)) (e : Edit) (h : files.lookup e.file = none) :
    ∃ msg, applyEdit files e = .error msg := ⟨s!"no file {e.file}", by simp [applyEdit, h]⟩

/-- An edit whose text doesn't occur exactly once is refused. -/
theorem applyEdit_not_once (files : List (String × String)) (e : Edit) (text : String)
    (h : files.lookup e.file = some text) (hn : occurrences e.old text ≠ 1) :
    ∃ msg, applyEdit files e = .error msg :=
  ⟨s!"{e.file}: the edit's text occurs {occurrences e.old text} times, not once",
    by simp [applyEdit, h, hn]⟩

theorem pick_zero (s n : Nat) : pick s n 0 = [] := by
  unfold pick
  cases List.range n <;> rfl

/-- The first `empty` variants of a batch are the fixture, with an empty key. -/
theorem variant_empty (catalogue : List Plant) (fixture : List (String × String)) (seed index empty : Nat)
    (h : index < empty) : variant catalogue fixture seed index empty = .ok { files := fixture, key := [] } := by
  unfold variant
  generalize next (seed + index * 7919) = s
  simp only [h, ite_true, pick_zero, List.map_nil, List.flatMap_nil, applyEdits]
  rfl

end SpecTools.Synthetic
