import SpecTools.Generated

/-!
What the generated fixture's tests rely on, proved for every seed and size: no two rules read the
same (kind, measure) pair, so a test setting its rule's measures on an empty request fires that rule
and no other.
-/

namespace SpecTools.Generated

private theorem not_mem_of_contains_false {l : List (String × String)} {p : String × String}
    (h : l.contains p = false) : p ∉ l := by
  intro hm
  have : l.contains p = true := List.contains_iff_mem.mpr hm
  simp_all

/-- A sum's second measure differs from the first and is new for the kind. -/
theorem secondMeasure_spec (used : List (String × String)) (kind m m2 : String)
    (h : secondMeasure used kind m = some m2) : m2 ≠ m ∧ used.contains (kind, m2) = false := by
  have hm := List.mem_of_mem_head? h
  simp only [List.mem_filter, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at hm
  exact hm.2

/-- A rule made on a new pair reads distinct pairs, none already used. -/
theorem makeRule_pairs (s i : Nat) (used : List (String × String)) (kind m : String)
    (hm : used.contains (kind, m) = false) :
    (makeRule s i used kind m).pairs.Nodup ∧ ∀ p ∈ (makeRule s i used kind m).pairs, p ∉ used := by
  have hs : ∀ m2, (if i % 7 == 6 then secondMeasure used kind m else none) = some m2 →
      m2 ≠ m ∧ used.contains (kind, m2) = false := by
    intro m2 h
    split at h
    · exact secondMeasure_spec used kind m m2 h
    · simp at h
  simp only [makeRule, Rule.pairs]
  generalize (if i % 7 == 6 then secondMeasure used kind m else none) = second at hs ⊢
  cases second with
  | none =>
    refine ⟨by simp [List.nodup_cons], ?_⟩
    simpa using not_mem_of_contains_false hm
  | some m2 =>
    obtain ⟨hne, hm2⟩ := hs m2 rfl
    refine ⟨?_, ?_⟩
    · simp [List.nodup_cons]
      exact fun h => hne h.symm
    · intro p hp
      simp at hp
      rcases hp with rfl | rfl
      · exact not_mem_of_contains_false hm
      · exact not_mem_of_contains_false hm2

/-- A head's pairs, distinct and new, joined to a tail's, distinct and new beside the head's. -/
private theorem join (a b used : List (String × String)) (ha : a.Nodup) (hau : ∀ p ∈ a, p ∉ used)
    (hb : b.Nodup) (hbu : ∀ p ∈ b, p ∉ used ++ a) :
    (a ++ b).Nodup ∧ ∀ p ∈ a ++ b, p ∉ used := by
  refine ⟨?_, ?_⟩
  · simp only [List.Nodup, List.pairwise_append]
    refine ⟨ha, hb, ?_⟩
    intro x hx y hy hxy
    subst hxy
    exact hbu x hy (List.mem_append_right _ hx)
  · intro p hp
    rcases List.mem_append.mp hp with h | h
    · exact hau p h
    · exact fun hu => hbu p h (List.mem_append_left _ hu)

/-- The invariant of `rules.go`: the pairs of what it returns are distinct and none is in `used`. -/
theorem go_pairs (s i k : Nat) (used : List (String × String)) (order : List Nat) :
    ((rules.go s i k used order).flatMap Rule.pairs).Nodup ∧
      ∀ p ∈ (rules.go s i k used order).flatMap Rule.pairs, p ∉ used := by
  induction order generalizing s i k used with
  | nil => simp [rules.go]
  | cons j rest ih =>
    unfold rules.go
    by_cases hk : k = 0
    · simp [hk]
    · simp only [hk, ite_false]
      by_cases hc : used.contains pairsAll[j]! = true
      · simp only [hc, ite_true]
        exact ih _ _ _ _
      · simp only [hc]
        have hc' : used.contains (pairsAll[j]!.1, pairsAll[j]!.2) = false := by simpa using hc
        obtain ⟨hn, hu⟩ := makeRule_pairs s i used _ _ hc'
        obtain ⟨ihn, ihu⟩ := ih (Synthetic.next (Synthetic.next (Synthetic.next s))) (i + 1) (k - 1)
          (used ++ (makeRule s i used pairsAll[j]!.1 pairsAll[j]!.2).pairs)
        exact join _ _ used hn hu ihn ihu

/-- The invariant of `drawPlants`: no drawn plant touches a rule in `touched`, and no two drawn
plants touch a common rule. -/
theorem drawPlants_disjoint (rs : List Rule) (extra : Rule) (shapes : List String) (s k : Nat)
    (touched : List Nat) :
    (∀ p ∈ drawPlants rs extra shapes s k touched, ∀ x ∈ p.touches, x ∉ touched) ∧
      (drawPlants rs extra shapes s k touched).Pairwise
        (fun p q => ∀ x ∈ p.touches, x ∉ q.touches) := by
  induction k generalizing s touched with
  | zero => simp [drawPlants]
  | succ k ih =>
    unfold drawPlants
    dsimp only
    split
    · exact ih _ _
    · rename_i q qs hfree
      -- Whichever free candidate the draw takes, the invariant holds.
      let s2 := Synthetic.next (Synthetic.next s)
      suffices key : ∀ p ∈ q :: qs,
          (∀ p' ∈ p :: drawPlants rs extra shapes s2 k (touched ++ p.touches),
            ∀ x ∈ p'.touches, x ∉ touched) ∧
          (p :: drawPlants rs extra shapes s2 k (touched ++ p.touches)).Pairwise
            (fun p q => ∀ x ∈ p.touches, x ∉ q.touches) from
        key _ (List.getElem_mem _)
      intro p hp
      rw [← hfree] at hp
      have hpt : ∀ x ∈ p.touches, x ∉ touched := by
        have := (List.mem_filter.mp hp).2
        intro x hx hxt
        have hx' := List.all_eq_true.mp this x hx
        simp at hx'
        exact hx' hxt
      obtain ⟨ih1, ih2⟩ := ih (Synthetic.next (Synthetic.next s)) (touched ++ p.touches)
      refine ⟨?_, ?_⟩
      · intro p' hp' x hx hxt
        rcases List.mem_cons.mp hp' with rfl | h
        · exact hpt x hx hxt
        · exact ih1 p' h x hx (List.mem_append_left _ hxt)
      · refine List.Pairwise.cons ?_ ih2
        intro p' hp' x hx hxp'
        exact ih1 p' hp' x hxp' (List.mem_append_right _ hx)

/-- No two plants of a generated variant touch a common rule. -/
theorem gvariant_plants_disjoint (rs : List Rule) (extra : Rule) (seed index empty : Nat)
    (shapes : List String) (perVariant : Option Nat) :
    (gvariant rs extra seed index empty shapes perVariant).2.Pairwise
      (fun p q => ∀ x ∈ p.touches, x ∉ q.touches) :=
  (drawPlants_disjoint _ _ _ _ _ _).2

/-- No two rules of a generated requirement read the same (kind, measure) pair. -/
theorem rules_pairs_nodup (seed n : Nat) : ((rules seed n).flatMap Rule.pairs).Nodup :=
  (go_pairs _ _ _ _ _).1

end SpecTools.Generated
