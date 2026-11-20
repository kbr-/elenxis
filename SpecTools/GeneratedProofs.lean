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
theorem secondMeasure_spec (v : Vocab) (used : List (String × String)) (kind m m2 : String)
    (h : secondMeasure v used kind m = some m2) : m2 ≠ m ∧ used.contains (kind, m2) = false := by
  have hm := List.mem_of_mem_head? h
  simp only [List.mem_filter, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at hm
  exact hm.2

/-- A rule made on a new pair reads distinct pairs, none already used. -/
theorem makeRule_pairs (v : Vocab) (s i : Nat) (used : List (String × String)) (kind m : String)
    (hm : used.contains (kind, m) = false) :
    (makeRule v s i used kind m).pairs.Nodup ∧
      ∀ p ∈ (makeRule v s i used kind m).pairs, p ∉ used := by
  have hs : ∀ m2, (if i % 7 == 6 then secondMeasure v used kind m else none) = some m2 →
      m2 ≠ m ∧ used.contains (kind, m2) = false := by
    intro m2 h
    split at h
    · exact secondMeasure_spec v used kind m m2 h
    · simp at h
  simp only [makeRule, Rule.pairs]
  generalize (if i % 7 == 6 then secondMeasure v used kind m else none) = second at hs ⊢
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
theorem go_pairs (v : Vocab) (s i k : Nat) (used : List (String × String)) (order : List Nat) :
    ((rules.go v s i k used order).flatMap Rule.pairs).Nodup ∧
      ∀ p ∈ (rules.go v s i k used order).flatMap Rule.pairs, p ∉ used := by
  induction order generalizing s i k used with
  | nil => simp [rules.go]
  | cons j rest ih =>
    unfold rules.go
    by_cases hk : k = 0
    · simp [hk]
    · simp only [hk, ite_false]
      by_cases hc : used.contains (pairsAll v)[j]! = true
      · simp only [hc, ite_true]
        exact ih _ _ _ _
      · simp only [hc]
        have hc' : used.contains ((pairsAll v)[j]!.1, (pairsAll v)[j]!.2) = false := by
          simpa using hc
        obtain ⟨hn, hu⟩ := makeRule_pairs v s i used _ _ hc'
        obtain ⟨ihn, ihu⟩ := ih (Synthetic.next (Synthetic.next (Synthetic.next s))) (i + 1) (k - 1)
          (used ++ (makeRule v s i used (pairsAll v)[j]!.1 (pairsAll v)[j]!.2).pairs)
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

/-- `gaps`' row scoring on a hand case: rule 3's exception row found, a gap on rule 5 a false alarm,
a gap whose row names no rule a false alarm, and a row naming the rule twice counted once found. -/
example : rowScore [{ id := 3, kind := "pay", measures := ["fines"], bound := 9, flag := none },
    { id := 5, kind := "lend", measures := ["loans"], bound := 4, flag := none }]
    ["The limit on the fines for a pay request doesn't apply to a staff member."]
    ["r3-exempt", "r3", "r5", "loans"] = (1, 2) := by native_decide

/-- No two rules of a generated requirement read the same (kind, measure) pair, in any domain. -/
theorem rules_pairs_nodup (seed n : Nat) (v : Vocab := .library) :
    ((rules seed n v).flatMap Rule.pairs).Nodup :=
  (go_pairs _ _ _ _ _ _).1

/-- Each owner's domain gives its 15 rules at the owners' tests' seed. -/
example : Vocab.all.all fun v => (rules 20261120 15 v).length == 15 := by native_decide

/-- A rule's presentation is one of those offered. -/
theorem presentationOf_mem {offered : List Presentation} (h : offered ≠ []) (seed index id : Nat) :
    presentationOf offered seed index id ∈ offered := by
  unfold presentationOf Synthetic.draw
  have hl : 0 < offered.length := List.length_pos_iff.mpr h
  rw [← List.getElem_eq_getD (h := Nat.mod_lt _ hl)]
  exact List.getElem_mem _

/-- Rules added to a variant leave the others' presentations as they were, and each rule's entry is
its own draw. -/
theorem drawn_append (offered : List Presentation) (seed index : Nat) (rs rs' : List Rule) :
    drawn offered seed index (rs ++ rs') =
      drawn offered seed index rs ++ drawn offered seed index rs' := by
  simp [drawn]

theorem drawn_entry (offered : List Presentation) (seed index : Nat) (rs : List Rule)
    (r : Rule) (h : r ∈ rs) :
    (r.id, presentationOf offered seed index r.id) ∈ drawn offered seed index rs :=
  List.mem_map.mpr ⟨r, h, rfl⟩

private theorem go_ids (l : List (Nat × Presentation)) :
    (pairFolded.go l).map (·.1) = l.map (·.1) := by
  induction l with
  | nil => rfl
  | cons x rest ih =>
    obtain ⟨id, p⟩ := x
    by_cases hp : p = .folded <;> simp [pairFolded.go, hp, ih]

private theorem go_count (l : List (Nat × Presentation)) (h : 0 < l.countP (·.2 == .folded)) :
    (pairFolded.go l).countP (·.2 == .folded) + 1 = l.countP (·.2 == .folded) := by
  induction l with
  | nil => simp at h
  | cons x rest ih =>
    obtain ⟨id, p⟩ := x
    by_cases hp : p = .folded
    · simp [pairFolded.go, hp]
    · simp [pairFolded.go, hp] at h ⊢
      exact ih (by simpa using h)

/-- Pairing keeps every rule, in order. -/
theorem pairFolded_ids (ps : List (Nat × Presentation)) :
    (pairFolded ps).map (·.1) = ps.map (·.1) := by
  unfold pairFolded
  split
  · rfl
  · rw [List.map_reverse, go_ids, List.map_reverse, List.reverse_reverse]

/-- After pairing, the folded rules are even in number, so each has a partner. -/
theorem pairFolded_even (ps : List (Nat × Presentation)) :
    (pairFolded ps).countP (·.2 == .folded) % 2 = 0 := by
  unfold pairFolded
  split
  · next h => simpa using h
  · next h =>
    have hpos : 0 < ps.reverse.countP (·.2 == .folded) := by
      rw [List.countP_reverse]; simp at h; omega
    have := go_count ps.reverse hpos
    simp only [List.countP_reverse] at this hpos ⊢
    simp at h
    omega

/-- On the batches' fixture (seed 20261107, 30 rules), the first variant draws each of the six
presentations for some rule, and the deciding test's weighting draws each of its three. -/
example : Presentation.all.all fun p =>
    (presentations Presentation.all 20261107 0 (rules 20261107 30)).any (·.2 == p) := by
  native_decide
example : Presentation.hard.all fun p =>
    (presentations Presentation.hard 20261107 0 (rules 20261107 30)).any (·.2 == p) := by
  native_decide

/-- Two variants of one batch present some rule differently. -/
example : presentations Presentation.all 20261107 0 (rules 20261107 30) ≠
    presentations Presentation.all 20261107 1 (rules 20261107 30) := by
  native_decide

end SpecTools.Generated
