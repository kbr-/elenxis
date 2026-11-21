import SpecTools.Owners
import SpecTools.GeneratedProofs
import SpecTools.Score

/-!
What the owners' tests rely on: no two flaws fall on one rule, no shared blind spot on a flawed
rule, each flaw where it can be committed, and the fidelity check's comparison.
-/

namespace SpecTools.Owners
open SpecTools.Generated

/-- The invariant of `drawFlaws`: the flawed rules are distinct and none is in `taken`. -/
theorem drawFlaws_rules (rs : List Rule) (s : Nat) (fs : List Flaw) (taken : List Nat) :
    ((drawFlaws rs s fs taken).map (·.rule)).Nodup ∧
      ∀ i ∈ drawFlaws rs s fs taken, i.rule ∉ taken := by
  induction fs generalizing s taken with
  | nil => simp [drawFlaws]
  | cons f fs ih =>
    unfold drawFlaws
    split
    · exact ih _ _
    · rename_i q qs hfree
      let r := (q :: qs)[Synthetic.draw s (qs.length + 1)]'(Nat.mod_lt _ (Nat.succ_pos _))
      have hr : r ∈ rs.filter fun r => f.fits r && !taken.contains r.id := by
        rw [hfree]; exact List.getElem_mem _
      have hnot : r.id ∉ taken := by
        have := (List.mem_filter.mp hr).2
        simp at this
        exact this.2
      obtain ⟨ihn, ihu⟩ := ih (Synthetic.next s) (taken ++ [r.id])
      refine ⟨?_, ?_⟩
      · simp only [List.map_cons, List.nodup_cons]
        exact ⟨fun h => by
          obtain ⟨i, hi, he⟩ := List.mem_map.mp h
          exact ihu i hi (List.mem_append_right _ (List.mem_singleton.mpr he)), ihn⟩
      · intro i hi
        rcases List.mem_cons.mp hi with rfl | h
        · exact hnot
        · exact fun ht => ihu i h (List.mem_append_left _ ht)

/-- No two flaws of a test fall on one rule. -/
theorem imperfections_distinct (seed : Nat) (rs : List Rule) (kinds : List Flaw) :
    ((imperfections seed rs kinds).map (·.rule)).Nodup :=
  (drawFlaws_rules _ _ _ _).1

/-- A plant the owners' draw takes at a step touches no rule already touched. -/
theorem drawOwnerPlants_step (rs : List Rule) (extra : Rule) (touched : List Nat)
    (open_ : List (List GPlant))
    (hopen : ∀ ps ∈ open_, ∃ shape, ps = freePlants rs extra shape touched) (i j : Nat)
    (p : GPlant) (hp : (open_.getD i [])[j]? = some p) : ∀ x ∈ p.touches, x ∉ touched := by
  have hmem : p ∈ open_.getD i [] := List.mem_of_getElem? hp
  rw [List.getD_eq_getElem?_getD] at hmem
  cases hi : open_[i]? with
  | none => simp [hi] at hmem
  | some ps =>
    simp only [hi, Option.getD_some] at hmem
    obtain ⟨shape, rfl⟩ := hopen ps (List.mem_of_getElem? hi)
    have := (List.mem_filter.mp hmem).2
    intro x hx hxt
    have hx' := List.all_eq_true.mp this x hx
    simp at hx'
    exact hx' hxt

/-- The owners' draw touches no rule of `touched`, and no two of its plants share a rule. -/
theorem drawOwnerPlants_disjoint (rs : List Rule) (extra : Rule) (s k : Nat)
    (touched : List Nat) :
    (∀ p ∈ drawOwnerPlants rs extra s k touched, ∀ x ∈ p.touches, x ∉ touched) ∧
      (drawOwnerPlants rs extra s k touched).Pairwise
        (fun p q => ∀ x ∈ p.touches, x ∉ q.touches) := by
  induction k generalizing s touched with
  | zero => simp [drawOwnerPlants]
  | succ k ih =>
    unfold drawOwnerPlants
    dsimp only
    split
    · simp
    · rename_i p hp
      have hpt := drawOwnerPlants_step rs extra touched _ (by
        intro ps hps
        obtain ⟨hps, -⟩ := List.mem_filter.mp hps
        obtain ⟨shape, -, rfl⟩ := List.mem_map.mp hps
        exact ⟨shape, rfl⟩) _ _ p hp
      obtain ⟨ih1, ih2⟩ := ih (Synthetic.next (Synthetic.next s)) (touched ++ p.touches)
      refine ⟨?_, ?_⟩
      · intro p' hp' x hx hxt
        rcases List.mem_cons.mp hp' with rfl | h
        · exact hpt x hx hxt
        · exact ih1 p' h x hx (List.mem_append_left _ hxt)
      · refine List.Pairwise.cons ?_ ih2
        intro p' hp' x hx hxp'
        exact ih1 p' hp' x hxp' (List.mem_append_right _ hx)

/-- No shared blind spot of an owners' variant touches a flawed rule. -/
theorem ownerVariant_avoids_flaws (rs : List Rule) (extra : Rule) (flawed : List Nat)
    (seed index empty : Nat) :
    ∀ p ∈ (ownerVariant rs extra flawed seed index empty).2, ∀ x ∈ p.touches, x ∉ flawed :=
  (drawOwnerPlants_disjoint _ _ _ _ _).1

/-- No two shared blind spots of an owners' variant touch one rule. -/
theorem ownerVariant_plants_disjoint (rs : List Rule) (extra : Rule) (flawed : List Nat)
    (seed index empty : Nat) :
    (ownerVariant rs extra flawed seed index empty).2.Pairwise
      (fun p q => ∀ x ∈ p.touches, x ∉ q.touches) :=
  (drawOwnerPlants_disjoint _ _ _ _ _).2

/-- The writing chosen has a score, and no writing scores higher. -/
theorem bestIndex_best (scores : List (Option Nat)) (i : Nat) (h : bestIndex scores = some i) :
    ∃ s, scores[i]? = some (some s) ∧ ∀ (j t : Nat), scores[j]? = some (some t) → t ≤ s := by
  unfold bestIndex at h
  cases hm : (scores.filterMap id).max? with
  | none => simp [hm] at h
  | some m =>
    simp only [hm, Option.bind_eq_bind, Option.bind_some] at h
    obtain ⟨hi, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.mp h
    refine ⟨m, ?_, ?_⟩
    · simp at hp
      simp [List.getElem?_eq_getElem hi, hp]
    · intro j t ht
      have hmem : t ∈ scores.filterMap id := by
        rw [List.mem_filterMap]
        exact ⟨some t, List.mem_of_getElem? ht, rfl⟩
      exact (List.max?_eq_some_iff.mp hm).2 t hmem

/-- The first of equal best is chosen, and writings without a score are passed over. -/
example : bestIndex [some 70, none, some 85, some 85] = some 2 := by decide
example : bestIndex [none, none] = none := by decide

/-- The fidelity check is a permutation of the normalized reads. -/
theorem faithful_iff (exp got : List Read) :
    faithful exp got = true ↔ (exp.map Read.norm).Perm (got.map Read.norm) := by
  unfold faithful
  exact List.isPerm_iff

/-- The owners' domains with their tests' seeds. -/
def ownerSeeds : List (Vocab × Nat) :=
  [(Vocab.salon, 20261120), (Vocab.tailor, 20261121), (Vocab.bakery, 20261122)]

/-- At each owner's seed each of its domain's flaw kinds falls on one rule, no other kind on any,
and a forgotten exception on a rule with an exception; across the three domains every kind is
some domain's. -/
example : Flaw.all.all (fun f => ownerSeeds.any fun (v, _) => v.flawKinds.contains f) &&
    ownerSeeds.all fun (v, seed) =>
      let rs := ownerRules seed ruleCount v
      let fl := imperfections seed rs v.flawKinds
      Flaw.all.all (fun f => (fl.filter (·.flaw == f)).length ==
        (if v.flawKinds.contains f then 1 else 0)) &&
        fl.all fun i => i.flaw != .forgotten ||
          (rs.find? (·.id == i.rule)).any (·.flag.isSome) := by native_decide

/-- Each catalogue's (kind, measure) pairs are distinct, and its words are its domain's; at each
domain's seed the drawn rules come from distinct entries (their pairs distinct), each limit a
natural number in its entry's range, and a rule with two limits given a natural second number;
each exemption is one of its entry's statuses. -/
example : ownerSeeds.all fun (v, seed) =>
      let cat := v.catalogue
      let pairs := cat.flatMap fun e => e.measures.map (e.kind, ·)
      let rs := ownerRules seed ruleCount v
      pairs.Nodup && cat.all (fun e => v.kinds.contains e.kind && e.lo ≤ e.hi &&
          e.measures.all v.measures.contains && e.flags.all v.flags.contains) &&
        rs.length == ruleCount && (rs.flatMap Rule.pairs).Nodup &&
        rs.all (fun r => natural r.bound && natural (secondLimit r.bound) &&
          secondLimit r.bound ≥ r.bound + 2) &&
        rs.all fun r => cat.any fun e => e.kind == r.kind && e.measures == r.measures &&
          e.lo ≤ r.bound && r.bound ≤ e.hi && r.flag.all e.flags.contains := by native_decide

/-- No owners' blind spot changes the prose view, which the owner's text replaces: a plant there
would plant nothing. At each owner's seed every variant's views keep each rule's prose as stated. -/
example : ownerSeeds.all fun (v, seed) =>
      let all := ownerRules seed (ruleCount + 1) v
      let rs := all.take ruleCount
      let flawed := (imperfections seed rs v.flawKinds).map (·.rule)
      (List.range 12).all fun i =>
        let vs := (ownerVariant rs (all.getLastD default) flawed seed i 2).1
        vs.length == rs.length &&
          (vs.zip rs).all fun (w, r) => w.prose.map Rule.id == some r.id &&
            w.prose.map Rule.bound == some r.bound && w.prose.map Rule.flag == some r.flag := by
  native_decide

/-- Every owners' blind spot plants something the agent reads: applied alone to the plain views,
it changes the artifacts' files other than the prose (`loans.md`, which the owner's text
replaces). Checked for each plant of each variant at each owner's seed. -/
example : ownerSeeds.all fun (v, seed) =>
      let all := ownerRules seed (ruleCount + 1) v
      let rs := all.take ruleCount
      let flawed := (imperfections seed rs v.flawKinds).map (·.rule)
      let plain := rs.map View.plain
      let artifacts (vs : List View) := (files vs).filter (·.1 != "loans.md")
      (List.range 12).all fun i =>
        (ownerVariant rs (all.getLastD default) flawed seed i 2).2.all fun p =>
          artifacts (p.apply plain) != artifacts plain := by
  native_decide

/-- At each owner's seed, every variant of its batch past the empty ones gets its three shared
blind spots, none on a flawed rule, the batch's extra rule drawn as `owners-variants` draws it. -/
example : ownerSeeds.all fun (v, seed) =>
      let all := ownerRules seed (ruleCount + 1) v
      let rs := all.take ruleCount
      let flawed := (imperfections seed rs v.flawKinds).map (·.rule)
      (List.range 12).all fun i =>
        let ps := (ownerVariant rs (all.getLastD default) flawed seed i 2).2
        ps.length == (if i < 2 then 0 else 3) &&
          ps.all fun p => p.touches.all (!flawed.contains ·) := by native_decide

/-- A loose limit reads with no number and the loose mark; a forgotten exception with no
exemption; an unflawed rule as stated. -/
example : expectedRead ⟨0, "perm", ["no_shows"], 3, some "regular"⟩ (some .loose) =
    ⟨"perm", ["no_shows"], none, some "regular", .loose⟩ := by native_decide
example : expectedRead ⟨0, "perm", ["no_shows"], 3, some "regular"⟩ (some .forgotten) =
    ⟨"perm", ["no_shows"], some 3, none, .stated⟩ := by native_decide
example : expectedRead ⟨0, "perm", ["no_shows"], 3, none⟩ none =
    ⟨"perm", ["no_shows"], some 3, none, .stated⟩ := by native_decide
example : expectedRead ⟨0, "perm", ["no_shows"], 3, some "vip"⟩ (some .twoLimits) =
    ⟨"perm", ["no_shows"], none, some "vip", .conflicting⟩ := by native_decide
example : expectedRead ⟨0, "perm", ["no_shows"], 3, none⟩ (some .openBoundary) =
    ⟨"perm", ["no_shows"], none, none, .loose⟩ := by native_decide

/-- A sum's measures read in either order, and a loose limit's number ignored, are faithful; a
stated limit's number differing is not. -/
example :
    let exp := expected [⟨0, "perm", ["no_shows", "complaints"], 3, none⟩,
      ⟨1, "colour", ["rebookings"], 5, none⟩] [⟨1, .loose⟩]
    faithful exp [⟨"colour", ["rebookings"], some 9, none, .loose⟩,
        ⟨"perm", ["complaints", "no_shows"], some 3, none, .stated⟩] &&
      !faithful exp [⟨"colour", ["rebookings"], some 9, none, .loose⟩,
        ⟨"perm", ["complaints", "no_shows"], some 4, none, .stated⟩] := by native_decide

/-- A finding naming a flawed rule's row finds the flaw, whatever its quote, when the flaw's row
reads back as its rule (which the evaluation below checks for every flaw drawn). -/
theorem flaw_found (rs : List Rule) (i : Imperfection) (f : Score.Finding) (fr : String)
    (hr : f.row = some fr) (h : rowRule fr = some i.rule)
    (hk : rowRule (flawRow i) = some i.rule) :
    Score.names f (flawPlant rs i) = true := by
  simp [Score.names, flawPlant, hr, hk, h]

/-- A finding naming a rule no plant and no flaw is on is a false alarm. -/
theorem other_row_alarm (key : List Synthetic.Plant) (f : Score.Finding)
    (h : key.all fun p => !Score.names f p) :
    (Score.score key [f]).falseAlarms = 1 := by
  have h' : key.any (Score.names f) = false := by
    simpa [List.all_eq_true, List.any_eq_false] using h
  show (List.filter (fun f => !key.any (Score.names f)) [f]).length = 1
  simp [h']

/-- Every flaw drawn at the owners' seeds has a row that reads back as its rule, both kinds of row
(`rK`, `rK-exempt`) among them. -/
example : ownerSeeds.all
    fun (v, seed) => (imperfections seed (ownerRules seed ruleCount v) v.flawKinds).all
      fun i => rowRule (flawRow i) == some i.rule := by native_decide

/-- On a hand key, a finding on the flaw's row finds the flaw, one on the blind spot's row finds
that, and one on another rule is the one false alarm. -/
example :
    let rs : List Rule := [⟨1, "perm", ["no_shows"], 3, some "regular"⟩,
      ⟨2, "colour", ["complaints"], 5, none⟩, ⟨4, "bridal", ["rebookings"], 2, none⟩]
    let key := [flawPlant rs ⟨1, .forgotten⟩,
      { kind := "shared blind spot", clause := "", edits := [], row := some "r2" }]
    let fs : List Score.Finding := [⟨"q", "k", some "r1-exempt"⟩, ⟨"q", "k", some "r2"⟩,
      ⟨"q", "k", some "r4"⟩]
    let s := Score.score key fs
    s.found == ["imperfection: forgotten exception", "shared blind spot"] && s.falseAlarms == 1 := by
  native_decide

private def has (s t : String) : Bool := (s.splitOn t).length > 1

/-- The writer's prompt holds each rule and each flaw's instruction and nothing of the artifacts
(no row, theorem or Lean name); the reviewer's holds no rule. -/
example :
    let v := Vocab.salon
    let rs := ownerRules 20261120 ruleCount v
    let fl := imperfections 20261120 rs v.flawKinds
    let w := writerPrompt v .prose rs fl ""
    let c := writerPrompt v .conversation rs fl ""
    let rv := reviewerPrompt v .prose "some text"
    rs.all (fun r => has w (ownerRuleText r) && has c (ownerRuleText r)) &&
      fl.all (fun i => (rs.find? (·.id == i.rule)).any fun r =>
        has w (flawInstruction r (some i.flaw))) &&
      !["fires_", "wit_", "theorem", "r0-exempt", "ledger"].any (has w ·) &&
      has c "Developer:" && has c "proposes concrete" &&
      has w "one rough list" && has w "first number that's refused" && has w "misspellings" &&
      !rs.any (fun r => has rv (ownerRuleText r)) && !has rv "# What you want" := by native_decide

end SpecTools.Owners
