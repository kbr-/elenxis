import SpecTools.Tests

/-!
`tests`' findings: a guard no test fails is reported, one some test fails isn't; a test a row names
is reported missing exactly when the test file doesn't define it.
-/

namespace SpecTools.Tests
open SpecTools.Ledger

theorem weak_reported (rows : List Row) (defined : List String) (gs : List GuardResult)
    (g : GuardResult) (hg : g ∈ gs) (h : g.failed = []) :
    Finding.weakTest g.line g.guard ∈ findings rows defined gs := by
  simp only [findings, List.mem_append, List.mem_map, List.mem_filter]
  exact .inr ⟨g, ⟨hg, by simp [h]⟩, rfl⟩

theorem killed_not_reported (rows : List Row) (defined : List String) (gs : List GuardResult)
    (g : GuardResult) (h : g.failed ≠ []) (hu : ∀ g' ∈ gs, g'.line = g.line → g'.guard = g.guard → g' = g) :
    Finding.weakTest g.line g.guard ∉ findings rows defined gs := by
  simp only [findings, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filter, not_or]
  refine ⟨?_, ?_⟩
  · rintro ⟨r, _, t, _, ht⟩
    cases ht
  · rintro ⟨g', ⟨hg', he⟩, heq⟩
    simp only [Finding.weakTest.injEq] at heq
    have := hu g' hg' heq.1 heq.2
    subst this
    simp_all

theorem missing_iff (rows : List Row) (defined : List String) (gs : List GuardResult) (r : Row)
    (t : String) (hr : r ∈ rows) (ht : t ∈ r.externalCheckNames) :
    Finding.missingTest r.id t ∈ findings rows defined gs ↔ t ∉ defined := by
  constructor
  · intro h
    simp only [findings, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filter] at h
    rcases h with ⟨r', _, t', ⟨_, hnd⟩, he⟩ | ⟨_, _, he⟩
    · simp only [Finding.missingTest.injEq] at he
      rw [← he.2]
      simpa using hnd
    · cases he
  · intro hnd
    simp only [findings, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filter]
    exact .inl ⟨r, hr, t, ⟨ht, by simpa using hnd⟩, rfl⟩

/-- Witness: a guard result some test fails. -/
example : ({ line := 1, guard := "g", failed := ["t"] } : GuardResult).failed ≠ [] := by decide

end SpecTools.Tests
