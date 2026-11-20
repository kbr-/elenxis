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
theorem imperfections_distinct (seed : Nat) (rs : List Rule) :
    ((imperfections seed rs).map (·.rule)).Nodup :=
  (drawFlaws_rules _ _ _ _).1

/-- No shared blind spot of an owners' variant touches a flawed rule. -/
theorem ownerVariant_avoids_flaws (rs : List Rule) (extra : Rule) (flawed : List Nat)
    (seed index empty : Nat) :
    ∀ p ∈ (ownerVariant rs extra flawed seed index empty).2, ∀ x ∈ p.touches, x ∉ flawed :=
  (drawPlants_disjoint _ _ _ _ _ _).1

/-- The fidelity check is a permutation of the normalized reads. -/
theorem faithful_iff (exp got : List Read) :
    faithful exp got = true ↔ (exp.map Read.norm).Perm (got.map Read.norm) := by
  unfold faithful
  exact List.isPerm_iff

/-- At each owner's seed every flaw kind falls on two rules, and a forgotten exception on a rule
with an exception. -/
example : [(Vocab.salon, 20261120), (Vocab.tailor, 20261121), (Vocab.bakery, 20261122)].all
    fun (v, seed) =>
      let rs := rules seed 15 v
      let fl := imperfections seed rs
      Flaw.all.all (fun f => (fl.filter (·.flaw == f)).length == 2) &&
        fl.all fun i => i.flaw != .forgotten ||
          (rs.find? (·.id == i.rule)).any (·.flag.isSome) := by native_decide

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
example : [(Vocab.salon, 20261120), (Vocab.tailor, 20261121), (Vocab.bakery, 20261122)].all
    fun (v, seed) => (imperfections seed (rules seed 15 v)).all
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
    let rs := rules 20261120 15 v
    let fl := imperfections 20261120 rs
    let w := writerPrompt v .prose rs fl ""
    let c := writerPrompt v .conversation rs fl ""
    let rv := reviewerPrompt v .prose "some text"
    rs.all (fun r => has w (ownerRuleText r) && has c (ownerRuleText r)) &&
      fl.all (fun i => (rs.find? (·.id == i.rule)).any fun r =>
        has w (flawInstruction r (some i.flaw))) &&
      !["fires_", "wit_", "theorem", "r0-exempt", "ledger"].any (has w ·) &&
      has c "Developer:" && has c "proposes concrete" &&
      !rs.any (fun r => has rv (ownerRuleText r)) && !has rv "# What you want" := by native_decide

end SpecTools.Owners
