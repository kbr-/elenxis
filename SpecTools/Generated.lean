import SpecTools.Synthetic

/-!
The generated synthetic test: a requirement of N rules drawn from a seed, and its four artifacts
(the prose, the Lean model with its ledger, the Python and its property tests) rendered from one
rule list, so the complete fixture agrees by construction. A plant changes how one artifact renders
one rule, so plants compose and stay exact at any N. Pure.

A rule refuses a request kind when one measure, or two measures summed, reaches its bound, unless
the request carries the rule's flag. No two rules share a kind and a measure, so a request setting
one measure fires one rule only, which lets each test build its case on an empty request.
-/

namespace SpecTools.Generated
open SpecTools.Synthetic

def kinds : List String := ["borrow", "renew", "hold", "reserve", "extend", "transfer", "return",
  "pay", "order", "cancel", "lend", "recall", "copy", "print", "scan", "book", "join", "leave",
  "upgrade", "refund", "deliver", "exchange", "import", "export", "archive", "restore", "appeal",
  "waive", "suspend", "reinstate"]
def measures : List String := ["loans", "fines", "holds", "renewals", "days_late", "reservations",
  "transfers", "items", "pages", "requests", "warnings", "visits", "orders", "credits", "debts",
  "strikes"]
def flags : List String := ["premium", "staff", "verified", "student", "senior", "partner",
  "trusted", "urgent"]

structure Rule where
  id : Nat
  kind : String
  measures : List String
  bound : Nat
  flag : Option String
  deriving Repr, DecidableEq, Inhabited

/-- The (kind, measure) pairs a rule reads. -/
def Rule.pairs (r : Rule) : List (String × String) := r.measures.map fun m => (r.kind, m)

/-- A sum's second measure: the next measure of the kind not yet used and not the first, if any. -/
def secondMeasure (used : List (String × String)) (kind m : String) : Option String :=
  (measures.filter fun m2 => m2 != m && !used.contains (kind, m2)).head?

/-- Rule `i` on the pair `(kind, m)` from state `s`; every seventh a sum of two measures. -/
def makeRule (s i : Nat) (used : List (String × String)) (kind m : String) : Rule :=
  let s1 := next s
  let s2 := next s1
  let s3 := next s2
  let second := if i % 7 == 6 then secondMeasure used kind m else none
  let ms := match second with | some m2 => [m, m2] | none => [m]
  let flag := if draw s2 2 == 0 then some flags[draw s3 flags.length]! else none
  { id := i, kind, measures := ms, bound := 2 + draw s1 29, flag }

def pairsAll : List (String × String) := kinds.flatMap fun k => measures.map fun m => (k, m)

/-- `n` rules from `seed`: a (kind, measure) pair each, never reused; every seventh a sum of two
measures, about half with a flag, bounds from 2 to 30. -/
def rules (seed n : Nat) : List Rule :=
  go seed 0 n [] (pick seed pairsAll.length pairsAll.length)
where
  /-- Structural on the remaining order: each pair is taken or skipped once. -/
  go (s i k : Nat) (used : List (String × String)) : List Nat → List Rule
    | [] => []
    | j :: rest =>
      if k = 0 then [] else
      let pr := pairsAll[j]!
      if used.contains pr then go s i k used rest else
      let rule := makeRule s i used pr.1 pr.2
      rule :: go (next (next (next s))) (i + 1) (k - 1) (used ++ rule.pairs) rest

/-- How each artifact renders one rule: the prose, the Lean model, the Python and the tests may
each hold a different version, and the ledger's rows may be changed. A plant edits a view. -/
structure View where
  prose : Option Rule
  model : Rule
  python : Rule
  test : Option Rule
  /-- The theorem's version of the rule (a bound, a hypothesis). -/
  theorem_ : Rule
  /-- A contradictory hypothesis added to the rule's theorem. -/
  vacuous : Bool := false
  /-- The row names another rule's theorem in place of its own. -/
  borrowsTheorem : Option Nat := none
  /-- The test's name differs from the one the row gives. -/
  testRenamed : Bool := false
  /-- The test's case stays below the bound, so it never reaches the guard. -/
  testBelow : Bool := false
  /-- The rule's theorem and witness aren't written (its row borrows another's). -/
  omitTheorem : Bool := false
  deriving Repr, Inhabited

def View.plain (r : Rule) : View :=
  { prose := some r, model := r, python := r, test := some r, theorem_ := r }

def words (m : String) : String := m.replace "_" " "

def what (r : Rule) : String := match r.measures with
  | [m] => s!"the {words m}"
  | ms => " and ".intercalate (ms.map fun m => s!"the {words m}") ++ " together"

/-! Prose: a sentence per rule and one per exception. -/

/-- "a" or "an" before a word, by its first letter. -/
def article (w : String) : String := if "aeiou".contains (w.front) then "an" else "a"

def ruleSentence (r : Rule) : String :=
  s!"{(article r.kind).capitalize} {r.kind} request is refused when {what r} reach {r.bound}."
def flagSentence (r : Rule) (f : String) : String :=
  s!"The limit on {what r} for {article r.kind} {r.kind} request doesn't apply to {article f} {f} member."

def prose (vs : List View) : String :=
  "# Requests\n\n" ++ "\n\n".intercalate (vs.filterMap fun v => v.prose.map fun r =>
    ruleSentence r ++ match r.flag with | some f => " " ++ flagSentence r f | none => "") ++ "\n"

/-! The Lean model: the rules as data, `refused` their disjunction, a theorem per clause. -/

def leanRule (r : Rule) : String :=
  let flag := match r.flag with | some f => s!"some \"{f}\"" | none => "none"
  s!"def r{r.id} : Rule := ⟨\"{r.kind}\", {repr r.measures}, {r.bound}, {flag}⟩"

def total (r : Rule) : String := " + ".intercalate (r.measures.map fun m => s!"q.get \"{m}\"")

def leanTheorems (v : View) : String :=
  let t := v.theorem_
  let flagHyp := match t.flag with | some f => s!" (hf : q.get \"{f}\" = 0)" | none => ""
  let vac := if v.vacuous then s!" (hv : q.get \"{t.measures.head!}\" < {t.bound})" else ""
  -- `omega` closes what `simp` leaves: a bound the theorem states above the rule's, or a
  -- contradicting hypothesis.
  let ruleThm := s!"theorem fires_r{t.id} (q : Req) (hk : q.kind = \"{t.kind}\") (hb : {t.bound} ≤ {total t}){flagHyp}{vac} :\n    fires r{t.id} q = true := by\n  simp [fires, r{t.id}, hk{if t.flag.isSome then ", hf" else ""}]\n  all_goals omega"
  -- The witness meets every hypothesis of the rule's theorem: its kind, its bound and the flag unset.
  let witFlag := match t.flag with | some f => s!" ∧ (w{t.id}).get \"{f}\" = 0" | none => ""
  let wit := s!"theorem wit_r{t.id} : (w{t.id}).kind = \"{t.kind}\" ∧ {t.bound} ≤ {(total t).replace "q.get" s!"(w{t.id}).get"}{witFlag} := by decide"
  let witDef := s!"def w{t.id} : Req := ⟨\"{t.kind}\", [{", ".intercalate (t.measures.map fun m => s!"(\"{m}\", {t.bound})")}]⟩"
  let exc := match v.model.flag with
    | some f => s!"\ntheorem exempt_r{t.id} (q : Req) (hf : 1 ≤ q.get \"{f}\") : fires r{t.id} q = false := by\n  have : q.get \"{f}\" ≠ 0 := by omega\n  simp [fires, r{t.id}, this]\ndef x{t.id} : Req := ⟨\"{t.kind}\", [(\"{f}\", 1)]⟩\ntheorem wit_x{t.id} : 1 ≤ (x{t.id}).get \"{f}\" := by decide"
    | none => ""
  (if v.omitTheorem then "" else "\n".intercalate [ruleThm, witDef, wit]) ++ exc

def rowId (r : Rule) : String := s!"r{r.id}"

def leanRows (vs : List View) : String :=
  let row (v : View) : List String :=
    let r := v.prose.getD v.model
    let j := v.borrowsTheorem.getD r.id
    -- A theorem left out with none borrowed leaves the row naming none: the audit's "not stated".
    let named := if v.omitTheorem && v.borrowsTheorem.isNone then "theorems := [], witnesses := []"
      else s!"theorems := [``fires_r{j}, ``refused_of], witnesses := [``wit_r{j}]"
    let base := s!"  \{ id := \"{rowId r}\", clause := {(ruleSentence r).quote},\n    {named} }"
    match r.flag, v.model.flag with
    | some f, some _ => [base, s!"  \{ id := \"{rowId r}-exempt\", clause := {(flagSentence r f).quote},\n    theorems := [``exempt_r{r.id}], witnesses := [``wit_x{r.id}] }"]
    | _, _ => [base]
  ",\n".intercalate (vs.flatMap row)

def leanFile (vs : List View) : String :=
  "\n".intercalate [
    "import SpecTools.Audit", "import SpecTools.GapsRun", "import SpecTools.Tests", "",
    "/-! The generated synthetic fixture's Lean model: the rules as data, a request refused when one",
    "fires, a theorem per clause with a witness that its hypotheses hold, and the ledger. -/", "",
    "namespace Loans", "open SpecTools.Ledger", "",
    "structure Req where", "  kind : String", "  vals : List (String × Nat)", "",
    "def Req.get (q : Req) (k : String) : Nat := (q.vals.lookup k).getD 0", "",
    "structure Rule where", "  kind : String", "  measures : List String", "  bound : Nat",
    "  flag : Option String", "  deriving DecidableEq", "",
    "def fires (r : Rule) (q : Req) : Bool :=",
    "  q.kind == r.kind && decide (r.bound ≤ (r.measures.map q.get).sum) &&",
    "    (match r.flag with | some f => q.get f == 0 | none => true)", ""] ++ "\n" ++
  "\n".intercalate (vs.map fun v => leanRule v.model) ++ "\n\n" ++
  s!"def rules : List Rule := [{", ".intercalate (vs.map fun v => s!"r{v.model.id}")}]\n\n" ++
  "def refused (q : Req) : Bool := rules.any (fires · q)\n\n" ++
  "theorem refused_of (r : Rule) (q : Req) (h : r ∈ rules) (hf : fires r q = true) :\n" ++
  "    refused q = true := List.any_eq_true.mpr ⟨r, h, hf⟩\n\n" ++
  "\n\n".intercalate (vs.map leanTheorems) ++ "\n\n" ++
  "def pythonTest (id : String) : List String := [\"test_\" ++ id.replace \"-\" \"_\"]\n\n" ++
  s!"def rows : List Row := [\n{leanRows vs}\n]\n\n" ++
  "def ledger : List Row := rows.map fun r => { r with tests := pythonTest r.id }\n\n" ++
  "end Loans\n\n#eval SpecTools.Audit.run Loans.ledger `Loans\n\n" ++
  "def fixtureDir : IO String := return (← IO.getEnv \"SPEC_TOOLS_DIR\").getD \"fixtures/loans\"\n" ++
  "def adapterPath : IO String :=\n  return (← IO.getEnv \"SPEC_TOOLS_ADAPTER\").getD \"../../adapters/python_guards.py\"\n\n" ++
  "#eval show IO Unit from do\n  if (← IO.getEnv \"SPEC_TOOLS_TESTS\").isSome then\n" ++
  "    SpecTools.Tests.run Loans.ledger (← adapterPath) \"loans.py\" \"test_loans.py\"\n      (cwd := some (← fixtureDir))\n\n" ++
  "#eval show Lean.Elab.Command.CommandElabM Unit from do\n  if let some model ← IO.getEnv \"SPEC_TOOLS_GAPS\" then\n" ++
  "    SpecTools.Gaps.run Loans.ledger (← IO.FS.readFile (System.FilePath.mk (← fixtureDir) / \"loans.md\"))\n" ++
  "      { (← SpecTools.Model.configuredBackend) with model }\n"

/-! The Python: an `if` per rule, so each rule is a guard the adapter can remove. -/

def pyCond (r : Rule) : String :=
  let sum := " + ".intercalate (r.measures.map fun m => s!"req.get(\"{m}\")")
  let flag := match r.flag with | some f => s!" and not req.get(\"{f}\")" | none => ""
  s!"req.kind == \"{r.kind}\" and {sum} >= {r.bound}{flag}"

def pythonFile (vs : List View) : String :=
  "\"\"\"The generated synthetic fixture's Python: a request is refused (None) when a rule fires.\"\"\"\n\n" ++
  "from __future__ import annotations\n\nfrom dataclasses import dataclass, field\n\n\n" ++
  "@dataclass(frozen=True)\nclass Req:\n    kind: str\n    vals: dict[str, int] = field(default_factory=dict)\n\n" ++
  "    def get(self, k: str) -> int:\n        return self.vals.get(k, 0)\n\n\n" ++
  "def handle(req: Req) -> Req | None:\n" ++
  String.join (vs.map fun v => s!"    if {pyCond v.python}:\n        return None\n") ++
  "    return req\n"

/-! The tests: per rule, its case refused at and over the bound, accepted below it; per flag, the
flagged case accepted. Each sets only its rule's measures, which no other rule of its kind uses. -/

def pyTests (vs : List View) : String :=
  let one (v : View) : String := match v.test with
    | none => ""
    | some r =>
      let name := if v.testRenamed then s!"test_r{r.id}_case" else s!"test_r{r.id}"
      let vals (x : String) := "{" ++ ", ".intercalate (r.measures.zipIdx.map fun (m, i) =>
        s!"\"{m}\": {if i == 0 then x else "0"}") ++ "}"
      let reach := if v.testBelow then s!"st.integers(0, {r.bound - 1})" else s!"st.integers({r.bound}, {r.bound + 40})"
      let assertion := if v.testBelow then "is not None" else "is None"
      -- A sum's bound split across its two measures, at it and one below it, so a test reaches
      -- every term: with either term dropped the split at the bound falls below it.
      let split (total : Nat) : String := match r.measures with
        | [m1, m2] => s!"\{\"{m1}\": {total - total / 2}, \"{m2}\": {total / 2}}"
        | _ => ""
      let splitCases := match r.measures with
        | [_, _] =>
          let atBound := if v.testBelow then "is not None" else "is None"
          s!"    assert handle(Req(\"{r.kind}\", {split (if v.testBelow then r.bound - 1 else r.bound)})) {atBound}\n    assert handle(Req(\"{r.kind}\", {split (r.bound - 1)})) is not None\n"
        | _ => ""
      let base := s!"@given({reach})\ndef {name}(v):  # r{r.id}\n    assert handle(Req(\"{r.kind}\", {vals "v"})) {assertion}\n    assert handle(Req(\"{r.kind}\", {vals (toString (r.bound - 1))})) is not None\n{splitCases}"
      let exempt := match r.flag with
        | some f => s!"\n\n@given(st.integers({r.bound}, {r.bound + 40}))\ndef test_r{r.id}_exempt(v):  # r{r.id}-exempt\n    vals = {vals "v"}\n    vals[\"{f}\"] = 1\n    assert handle(Req(\"{r.kind}\", vals)) is not None\n"
        | none => ""
      base ++ exempt
  "\"\"\"Property tests of the generated fixture, one per clause, named by its ledger row.\"\"\"\n\n" ++
  "from hypothesis import given, settings, strategies as st\n\nfrom loans import Req, handle\n\n" ++
  "settings.register_profile(\"fixture\", database=None, max_examples=20)\nsettings.load_profile(\"fixture\")\n\n\n" ++
  "\n\n".intercalate ((vs.map one).filter (· ≠ "")) ++ "\n"

def files (vs : List View) : List (String × String) :=
  [("loans.md", prose vs), ("Loans.lean", leanFile vs), ("loans.py", pythonFile vs),
   ("test_loans.py", pyTests vs)]

/-! Plants: each changes the views of one rule (the plant entry of the theory), and names in its
key the prose clause a finder must name. -/

/-- A plant: its kind, the clause its key names, the rules it touches (no other plant of the variant
may touch them), and its change. -/
structure GPlant where
  kind : String
  clause : String
  touches : List Nat
  apply : List View → List View

instance : Inhabited GPlant := ⟨{ kind := "", clause := "", touches := [], apply := id }⟩

def onRule (id : Nat) (f : View → View) (vs : List View) : List View :=
  vs.map fun v => if v.model.id == id then f v else v

/-- The ten shapes a plant takes: the seven kinds, then the three shapes of a shared blind spot. -/
def shapes : List String := ["uncovered", "too weak", "vacuous", "extra", "undecided",
  "missing test", "weak test", "exception dropped", "twin exception", "sum on one measure"]

/-- The shapes of a shared blind spot. -/
def blindShapes : List String := shapes.drop 7

/-- The plants of shape `shape` the rules `rs` allow, with `extra` the rule beyond the list. -/
def candidates (rs : List Rule) (extra : Rule) (shape : String) : List GPlant :=
  let n := rs.length
  -- A plant changes one clause, the one its key names: the extra rule carries no exception, and
  -- undecided removes a rule with none, so no second clause changes with it.
  let extra := { extra with flag := none }
  let blind := "shared blind spot"
  match shape with
  | "uncovered" => rs.map fun r =>
      let j := (r.id + 1) % n
      { kind := "uncovered", clause := ruleSentence r, touches := [r.id, j],
        apply := onRule r.id fun v => { v with omitTheorem := true, borrowsTheorem := some j } }
  | "too weak" => rs.map fun r =>
      { kind := "too weak", clause := ruleSentence r, touches := [r.id],
        apply := onRule r.id fun v => { v with theorem_ := { r with bound := r.bound + 1 } } }
  | "vacuous" => rs.map fun r =>
      { kind := "vacuous", clause := ruleSentence r, touches := [r.id],
        apply := onRule r.id fun v => { v with vacuous := true } }
  | "extra" =>
    [{ kind := "extra", clause := ruleSentence extra, touches := [extra.id],
       apply := fun vs => vs ++ [{ (View.plain extra) with prose := none }] }]
  | "undecided" => (rs.filter (·.flag.isNone)).map fun r =>
      { kind := "undecided", clause := ruleSentence r, touches := [r.id],
        apply := onRule r.id fun v => { v with prose := none } }
  | "missing test" => rs.map fun r =>
      { kind := "missing test", clause := ruleSentence r, touches := [r.id],
        apply := onRule r.id fun v => { v with testRenamed := true } }
  | "weak test" => rs.map fun r =>
      { kind := "weak test", clause := ruleSentence r, touches := [r.id],
        apply := onRule r.id fun v => { v with testBelow := true } }
  | "exception dropped" => rs.filterMap fun r => r.flag.map fun f =>
      let r' := { r with flag := none }
      { kind := blind, clause := flagSentence r f, touches := [r.id],
        apply := onRule r.id fun v =>
          { v with model := r', python := r', test := some r', theorem_ := r' } }
  | "twin exception" => rs.filterMap fun r =>
      -- The prose gives r the exception of a flagged twin (another kind on the same measure).
      if r.flag.isSome then none else
      (rs.find? fun t => t.flag.isSome && t.kind != r.kind && t.measures.head? == r.measures.head?).bind
        fun t => t.flag.map fun f =>
          { kind := blind, clause := flagSentence r f, touches := [r.id, t.id],
            apply := onRule r.id fun v => { v with prose := some { r with flag := some f } } }
  | "sum on one measure" => rs.filterMap fun r =>
      match r.measures with
      | m :: _ :: _ =>
        let r' := { r with measures := [m] }
        some { kind := blind, clause := ruleSentence r, touches := [r.id],
               apply := onRule r.id fun v =>
                 { v with model := r', python := r', test := some r', theorem_ := r' } }
      | _ => none
  | _ => []

/-! Scoring `gaps` by row: a gap names a ledger row (`rK` or `rK-exempt`), a plant a clause; both
map to a rule's number. -/

/-- The rule a ledger row's identifier names: the digits after `r`. -/
def rowRule (row : String) : Option Nat :=
  if row.startsWith "r" then ((row.drop 1).takeWhile Char.isDigit).toNat? else none

/-- The rule a prose clause speaks of: the one whose kind and first measure it names, which no other
rule shares (`rules_pairs_nodup`). -/
def clauseRule (rs : List Rule) (clause : String) : Option Nat :=
  let has (s : String) := (clause.splitOn s).length > 1
  (rs.find? fun r => has s!" {r.kind} request" &&
    match r.measures with | m :: _ => has s!"the {words m}" | [] => false).map (·.id)

/-- `gaps`' rows against a variant's plants: the plants whose rule some gap names (found), and the
gaps naming no plant's rule (false alarms). -/
def rowScore (rs : List Rule) (plantClauses : List String) (gapRows : List String) : Nat × Nat :=
  let plantRules := plantClauses.filterMap (clauseRule rs)
  let named := gapRows.filterMap rowRule
  ((plantRules.filter (named.contains ·)).length,
   (gapRows.filter fun g => match rowRule g with
     | some k => !plantRules.contains k | none => true).length)

/-- `left` plants drawn from state `s`, in drawing order, none touching a rule in `touched` or one an
earlier plant touched; a draw finding no free candidate plants nothing. -/
def drawPlants (rs : List Rule) (extra : Rule) (shapes : List String) :
    Nat → Nat → List Nat → List GPlant
  | _, 0, _ => []
  | s, k + 1, touched =>
    let s1 := next s
    let s2 := next s1
    let shape := shapes[draw s1 shapes.length]!
    match (candidates rs extra shape).filter fun p => p.touches.all (!touched.contains ·) with
    | [] => drawPlants rs extra shapes s2 k touched
    | q :: qs =>
      let p := (q :: qs)[draw s2 (qs.length + 1)]'(Nat.mod_lt _ (Nat.succ_pos _))
      p :: drawPlants rs extra shapes s2 k (touched ++ p.touches)

/-- Variant `index` of a batch from `seed` over the rules `rs`: the first `empty` variants plant
nothing, the others `perVariant` plants, or one to three, each shape drawn from `shapes` and its
rule from the shape's candidates untouched by an earlier plant of the variant. -/
def gvariant (rs : List Rule) (extra : Rule) (seed index empty : Nat)
    (shapes : List String := shapes) (perVariant : Option Nat := none) : List View × List GPlant :=
  let s := next (seed + index * 7919)
  let count := if index < empty then 0 else perVariant.getD (1 + draw s 3)
  let plants := drawPlants rs extra shapes s count []
  (plants.foldl (fun vs p => p.apply vs) (rs.map View.plain), plants)

end SpecTools.Generated
