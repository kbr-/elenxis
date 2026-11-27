-- SPDX-License-Identifier: Apache-2.0
import SpecTools.Score

/-!
The scorer's guarantees: every plant is found or missed, never both; findings on a variant planting
nothing are all false alarms; and a report quoting each planted clause finds all with none false.
-/

namespace SpecTools.Score
open SpecTools.Synthetic SpecTools.Clauses

theorem filter_split {α} (p : α → Bool) (l : List α) :
    (l.filter p).length + (l.filter (fun x => !p x)).length = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih => cases h : p x <;> simp [h] <;> omega

/-- Found and missed partition the key. -/
theorem found_missed (key : List Plant) (fs : List Finding) :
    (score key fs).found.length + (score key fs).missed.length = key.length := by
  simp only [score, List.length_map]
  exact filter_split _ key

/-- On a variant planting nothing, every finding is a false alarm and nothing is found. -/
theorem score_no_plants (fs : List Finding) :
    score [] fs = { found := [], missed := [], falseAlarms := fs.length } := by
  simp [score]

/-- A report quoting exactly the planted clauses finds every plant and raises no false alarm. -/
theorem score_exact (key : List Plant) :
    (score key (key.map fun p => ({ clause := p.clause, kind := p.kind } : Finding))).missed = [] ∧
    (score key (key.map fun p => ({ clause := p.clause, kind := p.kind } : Finding))).falseAlarms = 0 := by
  simp only [score]
  constructor
  · rw [List.map_eq_nil_iff, List.filter_eq_nil_iff]
    intro p hp
    have : (key.map fun p => ({ clause := p.clause, kind := p.kind } : Finding)).any (names · p) :=
      List.any_eq_true.mpr ⟨_, List.mem_map.mpr ⟨p, hp, rfl⟩, by simp [names, quoteNames]⟩
    simp [this]
  · rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro f hf
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hf
    have : key.any (names { clause := p.clause, kind := p.kind }) :=
      List.any_eq_true.mpr ⟨p, hp, by simp [names, quoteNames]⟩
    simp [this]

/-- A finding names a plant exactly when its quote equals the clause, or holds at most two sentences
one of which is the clause. -/
theorem quoteNames_iff (f : Finding) (p : Plant) :
    quoteNames f p = true ↔ normalize f.clause = normalize p.clause ∨
      ((sentences f.clause).length ≤ 2 ∧ normalize p.clause ∈ sentences f.clause) := by
  simp [quoteNames]

/-- A finding without a row, such as one saved before rows were asked for, is judged by its quote,
so `rescore` of those results is unchanged. -/
theorem names_without_row (f : Finding) (p : Plant) (h : f.row = none) :
    names f p = quoteNames f p := by
  simp [names, h]

/-- A finding naming its plant's rule row finds it, whatever it quotes. -/
theorem names_by_row (f : Finding) (p : Plant) (fr pr : String) (k : Nat) (hf : f.row = some fr)
    (hp : p.row = some pr) (hpk : Generated.rowRule pr = some k) (hfk : Generated.rowRule fr = some k) :
    names f p = true := by
  simp [names, hf, hp, hpk, hfk]

/-- A finding naming another rule's row doesn't name the plant, whatever it quotes. -/
theorem names_other_row (f : Finding) (p : Plant) (fr pr : String) (hf : f.row = some fr)
    (hp : p.row = some pr) (hne : Generated.rowRule fr ≠ Generated.rowRule pr) :
    names f p = false := by
  simp [names, hf, hp, hne]

/-- A finding naming no plant is a false alarm. -/
theorem score_false_alarm (key : List Plant) (f : Finding) (h : ∀ p ∈ key, names f p = false) :
    (score key [f]).falseAlarms = 1 := by
  simp only [score, List.filter_cons, List.filter_nil]
  have : key.any (names f) = false := by
    rw [List.any_eq_false]; intro p hp; simp [h p hp]
  simp [this]

/-- Split by presentation: a found plant under its rule's presentation, a false alarm under the
presentation of the rule it names, and the rows it names nowhere under "no row". -/
example : byPresentation [(3, .spread), (4, .exampleOnly)]
    [{ kind := "shared blind spot", clause := "x", edits := [], row := some "r3" },
     { kind := "shared blind spot", clause := "y", edits := [], row := some "r4" }]
    [⟨"q", "uncovered", some "r3-exempt"⟩, ⟨"q", "uncovered", some "r9"⟩] =
    [("spread", 1, 1, 0), ("example only", 1, 0, 0), ("no row", 0, 0, 1)] := by native_decide

/-- On rows: the exemption's row names its rule, and a row of another rule names nothing planted. -/
example : names ⟨"Desk staff never pay fines.", "uncovered", some "r3-exempt"⟩
    { kind := "shared blind spot", clause := "x", edits := [], row := some "r3" } = true := by
  native_decide
example : (score [{ kind := "shared blind spot", clause := "x", edits := [], row := some "r3" }]
    [⟨"x", "uncovered", some "r4"⟩]).falseAlarms = 1 := by native_decide

private def rule : Plant :=
  { kind := "shared blind spot", clause := "A restore request is refused when the holds reach 14.",
    edits := [] }
private def exception : Plant :=
  { kind := "shared blind spot", edits := [],
    clause := "The limit on the holds for a restore request doesn't apply to a senior member." }

/-- A rule quoted with its exception names each of the two clauses, as quoted by the tools arm. -/
example : names ⟨rule.clause ++ " " ++ exception.clause, "uncovered", none⟩ exception = true := by
  native_decide
example : names ⟨rule.clause ++ " " ++ exception.clause, "uncovered", none⟩ rule = true := by
  native_decide
/-- A quote of three sentences names neither, so quoting the prose finds nothing. -/
example : names ⟨"A pay request is refused when the fines reach 3. " ++ rule.clause ++ " " ++
    exception.clause, "uncovered", none⟩ exception = false := by native_decide
/-- Two sentences neither of which is the clause name nothing. -/
example : names ⟨"A pay request is refused when the fines reach 3. A lend request is refused \
    when the loans reach 4.", "uncovered", none⟩ exception = false := by native_decide
/-- A clause's words inside a longer sentence are not the clause. -/
example : names ⟨"The limit on the holds for a restore request doesn't apply to a senior member \
    or a staff member.", "uncovered", none⟩ exception = false := by native_decide

/-- The bar holds exactly when the ledger finds more blind spots and its false alarms stay within
the baseline's plus one a variant. -/
theorem barMet_iff (lb bb la ba n : Nat) :
    barMet lb bb la ba n = true ↔ bb < lb ∧ la ≤ ba + n := by
  simp [barMet]

/-- The bar's two ends at their values, and a tie in blind spots failing it whatever the alarms. -/
example : barMet 8 6 6 3 3 = true := by decide
example : barMet 8 6 7 3 3 = false := by decide
example : barMet 6 6 0 3 3 = false := by decide

end SpecTools.Score
