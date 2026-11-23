import SpecTools.Synthetic
import SpecTools.FiniteGaps

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

/-- A domain's words: its request kinds, the counts a rule reads (each one where more is worse),
and the customer statuses an exception names. -/
structure Vocab where
  name : String
  kinds : List String
  measures : List String
  flags : List String
  deriving Repr, Inhabited

/-- A plausible rule of an owner's domain: the request it turns away, the count or counts it reads,
a realistic range for its limit, and the customer statuses that could plausibly be exempt. -/
structure Entry where
  kind : String
  measures : List String
  lo : Nat
  hi : Nat
  flags : List String
  deriving Repr, Inhabited

/-- The library's words, the generator's first domain. -/
def Vocab.library : Vocab :=
  ⟨"library", Generated.kinds, Generated.measures, Generated.flags⟩

/-- A hair salon's bookings. -/
def Vocab.salon : Vocab := ⟨"salon",
  ["booking", "rebooking", "colour", "highlights", "perm", "bridal", "home visit", "kids cut",
    "gift card", "evening slot"],
  ["no_shows", "late_cancellations", "unpaid_visits", "open_bookings", "missed_patch_tests",
    "complaints", "rebookings", "deposits_owed"],
  ["regular", "staff", "vip", "family"]⟩

/-- A tailor's alteration orders. -/
def Vocab.tailor : Vocab := ⟨"tailor",
  ["hemming", "taking in", "letting out", "zip repair", "suit alteration", "wedding dress",
    "rush job", "collection", "delivery", "remake"],
  ["open_orders", "uncollected_items", "unpaid_orders", "days_overdue", "garments", "rush_jobs",
    "fittings", "remakes"],
  ["regular", "trade", "staff", "wedding"]⟩

/-- A home bakery's cake orders. -/
def Vocab.bakery : Vocab := ⟨"bakery",
  ["birthday cake", "wedding cake", "cupcakes", "custom cake", "delivery", "same day order",
    "tasting", "large order", "cookie box", "rush order"],
  ["orders_this_week", "late_pickups", "unpaid_deposits", "cancelled_orders", "tiers", "dozens",
    "allergy_changes", "complaints"],
  ["regular", "wholesale", "staff", "charity"]⟩

def Vocab.all : List Vocab := [.library, .salon, .tailor, .bakery]

/-- The rules an owner of the domain could plausibly have: limits a small business sets, on counts
it keeps (the library's generator draws its own, and has none here). -/
def Vocab.catalogue (v : Vocab) : List Entry :=
  match v.name with
  | "salon" => [
      ⟨"booking", ["no_shows"], 2, 4, ["regular", "family"]⟩,
      ⟨"booking", ["unpaid_visits"], 1, 3, ["family"]⟩,
      ⟨"booking", ["open_bookings"], 3, 6, ["staff", "vip"]⟩,
      ⟨"colour", ["missed_patch_tests"], 1, 1, []⟩,
      ⟨"colour", ["complaints"], 2, 4, ["regular"]⟩,
      ⟨"bridal", ["no_shows"], 1, 2, ["family"]⟩,
      ⟨"highlights", ["open_bookings"], 2, 3, ["vip"]⟩,
      ⟨"perm", ["complaints"], 2, 3, ["vip"]⟩,
      ⟨"bridal", ["deposits_owed"], 1, 2, ["family"]⟩,
      ⟨"home visit", ["unpaid_visits"], 1, 2, ["regular"]⟩,
      ⟨"home visit", ["late_cancellations"], 1, 3, []⟩,
      ⟨"kids cut", ["no_shows"], 2, 3, ["family"]⟩,
      ⟨"evening slot", ["late_cancellations"], 2, 4, ["regular"]⟩,
      ⟨"evening slot", ["no_shows"], 1, 2, ["staff"]⟩,
      ⟨"rebooking", ["rebookings"], 3, 5, ["regular"]⟩,
      ⟨"booking", ["late_cancellations"], 2, 4, ["regular"]⟩]
  | "tailor" => [
      ⟨"rush job", ["open_orders"], 3, 6, ["regular", "trade"]⟩,
      ⟨"rush job", ["rush_jobs"], 2, 4, ["trade"]⟩,
      ⟨"suit alteration", ["unpaid_orders"], 1, 2, ["regular"]⟩,
      ⟨"suit alteration", ["open_orders"], 2, 4, ["trade"]⟩,
      ⟨"wedding dress", ["fittings"], 3, 5, ["regular"]⟩,
      ⟨"wedding dress", ["unpaid_orders"], 1, 1, []⟩,
      ⟨"delivery", ["unpaid_orders"], 1, 3, ["trade"]⟩,
      ⟨"delivery", ["days_overdue"], 7, 21, ["trade"]⟩,
      ⟨"collection", ["uncollected_items"], 3, 6, ["trade"]⟩,
      ⟨"hemming", ["uncollected_items"], 4, 8, ["regular"]⟩,
      ⟨"remake", ["remakes"], 2, 3, ["regular"]⟩,
      ⟨"remake", ["days_overdue"], 10, 30, []⟩,
      ⟨"taking in", ["garments"], 5, 10, ["trade"]⟩,
      ⟨"letting out", ["garments"], 4, 8, ["trade"]⟩,
      ⟨"zip repair", ["days_overdue"], 14, 30, ["regular"]⟩,
      ⟨"hemming", ["unpaid_orders"], 2, 3, ["regular"]⟩]
  | "bakery" => [
      ⟨"same day order", ["orders_this_week"], 6, 12, ["regular"]⟩,
      ⟨"same day order", ["allergy_changes"], 1, 2, []⟩,
      ⟨"rush order", ["orders_this_week"], 8, 15, ["wholesale"]⟩,
      ⟨"wedding cake", ["tiers"], 4, 6, []⟩,
      ⟨"wedding cake", ["unpaid_deposits"], 1, 1, ["charity"]⟩,
      ⟨"custom cake", ["unpaid_deposits"], 1, 2, ["regular"]⟩,
      ⟨"custom cake", ["allergy_changes"], 2, 4, []⟩,
      ⟨"birthday cake", ["late_pickups"], 2, 4, ["regular"]⟩,
      ⟨"birthday cake", ["complaints"], 2, 3, ["staff"]⟩,
      ⟨"cookie box", ["dozens"], 6, 12, ["wholesale"]⟩,
      ⟨"cupcakes", ["dozens"], 8, 15, ["wholesale"]⟩,
      ⟨"delivery", ["dozens"], 4, 10, ["wholesale"]⟩,
      ⟨"delivery", ["cancelled_orders"], 2, 4, ["regular"]⟩,
      ⟨"tasting", ["cancelled_orders"], 2, 3, ["charity"]⟩,
      ⟨"tasting", ["unpaid_deposits"], 1, 2, ["regular"]⟩,
      ⟨"large order", ["orders_this_week"], 10, 20, ["wholesale"]⟩]
  | _ => []

def Vocab.named (name : String) : Option Vocab := Vocab.all.find? (·.name == name)

structure Rule where
  id : Nat
  kind : String
  measures : List String
  bound : Nat
  flag : Option String
  deriving Repr, DecidableEq, Inhabited

def Rule.scope (rule : Rule) : FiniteGaps.Scope :=
  ⟨rule.kind, rule.measures, rule.bound, rule.flag, none⟩

/-- The (kind, measure) pairs a rule reads. -/
def Rule.pairs (r : Rule) : List (String × String) := r.measures.map fun m => (r.kind, m)

/-- A sum's second measure: the next measure of the kind not yet used and not the first, if any. -/
def secondMeasure (v : Vocab) (used : List (String × String)) (kind m : String) : Option String :=
  (v.measures.filter fun m2 => m2 != m && !used.contains (kind, m2)).head?

/-- Rule `i` on the pair `(kind, m)` from state `s`; every seventh a sum of two measures. -/
def makeRule (v : Vocab) (s i : Nat) (used : List (String × String)) (kind m : String) : Rule :=
  let s1 := next s
  let s2 := next s1
  let s3 := next s2
  let second := if i % 7 == 6 then secondMeasure v used kind m else none
  let ms := match second with | some m2 => [m, m2] | none => [m]
  let flag := if draw s2 2 == 0 then some v.flags[draw s3 v.flags.length]! else none
  { id := i, kind, measures := ms, bound := 2 + draw s1 29, flag }

def pairsAll (v : Vocab) : List (String × String) :=
  v.kinds.flatMap fun k => v.measures.map fun m => (k, m)

/-- `n` rules from `seed` over a domain's words: a (kind, measure) pair each, never reused; every
seventh a sum of two measures, about half with a flag, bounds from 2 to 30. -/
def rules (seed n : Nat) (v : Vocab := .library) : List Rule :=
  go v seed 0 n [] (pick seed (pairsAll v).length (pairsAll v).length)
where
  /-- Structural on the remaining order: each pair is taken or skipped once. -/
  go (v : Vocab) (s i k : Nat) (used : List (String × String)) : List Nat → List Rule
    | [] => []
    | j :: rest =>
      if k = 0 then [] else
      let pr := (pairsAll v)[j]!
      if used.contains pr then go v s i k used rest else
      let rule := makeRule v s i used pr.1 pr.2
      rule :: go v (next (next (next s))) (i + 1) (k - 1) (used ++ rule.pairs) rest

/-- A number an owner keeps in their head: a small count, a round one, a dozen, or whole weeks of
days. -/
def natural (n : Nat) : Bool :=
  n ≤ 10 || n % 5 == 0 || [12, 14, 21, 28].contains n

/-- The natural numbers from `lo` to `hi`, or `lo` alone when there is none. -/
def naturalIn (lo hi : Nat) : List Nat :=
  match ((List.range (hi + 1 - lo)).map (lo + ·)).filter natural with
  | [] => [lo]
  | ns => ns

/-- `n` rules of an owner's domain from `seed`: distinct catalogue entries in a drawn order, rule
`i` taking the `i`-th, its limit drawn among the natural numbers of the entry's range and, one time
in three, an exemption from its statuses. -/
def ownerRules (seed n : Nat) (v : Vocab) : List Rule :=
  let cat := v.catalogue
  (pick seed cat.length n).zipIdx.map fun (j, i) =>
    let e := cat.getD j default
    let s1 := next (seed + (i + 1) * 104729)
    let s2 := next s1
    let s3 := next s2
    let flag := if e.flags.isEmpty || draw s2 3 != 0 then none
      else some (e.flags.getD (draw s3 e.flags.length) "")
    let ns := naturalIn e.lo e.hi
    { id := i, kind := e.kind, measures := e.measures, bound := ns.getD (draw s1 ns.length) e.lo,
      flag }

/-- A domain's `n` rules from `seed`: an owner's domain draws from its catalogue, the library from
its own generator. -/
def rulesOf (seed n : Nat) (v : Vocab) : List Rule :=
  if v.catalogue.isEmpty then rules seed n v else ownerRules seed n v

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
  let vac := if v.vacuous then s!" (hv : {total t} < {t.bound})" else ""
  -- `omega` closes what `simp` leaves: a bound the theorem states above the rule's, or a
  -- contradicting hypothesis.
  let ruleThm := s!"theorem fires_r{t.id} (q : Req) (hk : q.kind = \"{t.kind}\") (hb : {t.bound} ≤ {total t}){flagHyp}{vac} :\n    fires r{t.id} q = true := by\n  simp [fires, r{t.id}, hk{if t.flag.isSome then ", hf" else ""}]\n  all_goals omega"
  -- The witness meets every hypothesis of the rule's theorem: its kind, its bound and the flag unset.
  let witFlag := match t.flag with | some f => s!"∃ _hf : q.get \"{f}\" = 0, " | none => ""
  let premises := s!"∃ q : Req, ∃ _hk : q.kind = \"{t.kind}\", ∃ _hb : {t.bound} ≤ {total t}, {witFlag}"
  let flagProof := if t.flag.isSome then ", by decide" else ""
  let wit := s!"theorem wit_r{t.id} :\n    {premises}True :=\n  ⟨w{t.id}, by decide, by decide{flagProof}, trivial⟩"
  let empty := s!"theorem empty_r{t.id} :\n    ¬ ({premises}∃ _hv : {total t} < {t.bound}, True) := by\n  intro ⟨_, _, lo, {if t.flag.isSome then "_, " else ""}hi, _⟩\n  exact (Nat.not_lt_of_ge lo) hi"
  let witDef := s!"def w{t.id} : Req := ⟨\"{t.kind}\", [{", ".intercalate (t.measures.map fun m => s!"(\"{m}\", {t.bound})")}]⟩"
  let model := v.model
  let request := s!"(⟨\"{model.kind}\", [{", ".intercalate
    (model.measures.map fun m => s!"(\"{m}\", {model.bound})")}]⟩ : Req)"
  let refusedWitness := s!"theorem wit_refused_r{t.id} :\n    ∃ r : Rule, ∃ q : Req, ∃ _h : r ∈ rules, ∃ _hf : fires r q = true, True :=\n  ⟨r{t.id}, {request}, by decide, by decide, trivial⟩"
  let exc := match v.model.flag with
    | some f => s!"\ntheorem exempt_r{t.id} (q : Req) (hf : 1 ≤ q.get \"{f}\") : fires r{t.id} q = false := by\n  have : q.get \"{f}\" ≠ 0 := by omega\n  simp [fires, r{t.id}, this]\ndef x{t.id} : Req := ⟨\"{t.kind}\", [(\"{f}\", 1)]⟩\ntheorem wit_x{t.id} : ∃ q : Req, ∃ _hf : 1 ≤ q.get \"{f}\", True :=\n  ⟨x{t.id}, by decide, trivial⟩"
    | none => ""
  (if v.omitTheorem then "" else
    "\n".intercalate ([ruleThm, refusedWitness] ++ if v.vacuous then [empty] else [witDef, wit])) ++ exc

def rowId (r : Rule) : String := s!"r{r.id}"

def leanRows (vs : List View) : String :=
  let row (v : View) : List String :=
    let r := v.prose.getD v.model
    let j := v.borrowsTheorem.getD r.id
    -- A theorem left out with none borrowed leaves the row naming none: the audit's "not stated".
    let named := if v.omitTheorem && v.borrowsTheorem.isNone then "theorems := []"
      else
        let subject := v.borrowsTheorem.bind
          (fun id => vs.find? (fun candidate => candidate.model.id == id))
        let vacuous := (subject.getD v).vacuous
        let certificate := if vacuous then s!"⟨``fires_r{j}, ``empty_r{j}, .inconsistent⟩"
          else s!"⟨``fires_r{j}, ``wit_r{j}, .inhabited⟩"
        s!"theorems := [``fires_r{j}, ``refused_of], evidence := [{certificate}, ⟨``refused_of, ``wit_refused_r{j}, .inhabited⟩]"
    let base := s!"  \{ id := \"{rowId r}\", clause := {(ruleSentence r).quote},\n    {named} }"
    match r.flag, v.model.flag with
    | some f, some _ => [base, s!"  \{ id := \"{rowId r}-exempt\", clause := {(flagSentence r f).quote},\n    theorems := [``exempt_r{r.id}], evidence := [⟨``exempt_r{r.id}, ``wit_x{r.id}, .inhabited⟩] }"]
    | _, _ => [base]
  ",\n".intercalate (vs.flatMap row)

/-- The common Lean declarations used by both fixture layouts. -/
def leanModel (rules : List Rule) : String :=
  "\n".intercalate [
    "structure Req where", "  kind : String", "  vals : List (String × Nat)", "",
    "def Req.get (q : Req) (k : String) : Nat := (q.vals.lookup k).getD 0", "",
    "structure Rule where", "  kind : String", "  measures : List String", "  bound : Nat",
    "  flag : Option String", "  deriving DecidableEq", "",
    "def fires (r : Rule) (q : Req) : Bool :=",
    "  q.kind == r.kind && decide (r.bound ≤ (r.measures.map q.get).sum) &&",
    "    (match r.flag with | some f => q.get f == 0 | none => true)", ""] ++ "\n" ++
  "\n".intercalate (rules.map leanRule) ++ "\n\n" ++
  s!"def rules : List Rule := [{", ".intercalate (rules.map fun r => s!"r{r.id}")}]\n\n"

def leanImplementation : String :=
  "def refused (q : Req) : Bool := rules.any (fires · q)\n\n" ++
  "theorem refused_of (r : Rule) (q : Req) (h : r ∈ rules) (hf : fires r q = true) :\n" ++
  "    refused q = true := List.any_eq_true.mpr ⟨r, h, hf⟩\n\n"

/-- A generated project uses the local Elenxis library without a network dependency. -/
def leanFiles (views : List View) (root toolchain : String) : List (String × String) :=
  let rules := views.map (·.model)
  let config := "name = \"GeneratedLoans\"\ndefaultTargets = [\"Ledger\", \"Counterexamples\"]\n\n" ++
    s!"[[require]]\nname = \"Elenxis\"\npath = {root.quote}\n\n" ++
    String.join (["Spec", "Implementation", "ProofObligations", "Ledger", "Counterexamples"].map fun name =>
      s!"[[lean_lib]]\nname = {name.quote}\n\n")
  [("requirements.md", prose views),
   ("Spec.lean", "namespace Loans\n\n" ++ leanModel rules ++
     "def requiresRefusal (q : Req) : Prop := ∃ r, r ∈ rules ∧ fires r q = true\n\nend Loans\n"),
   ("Implementation.lean", "import Spec\n\nnamespace Loans\n\n" ++
     "def refused (q : Req) : Bool := rules.any (fires · q)\n\nend Loans\n"),
   ("ProofObligations.lean", "import Implementation\n\nnamespace Loans\n\n" ++
     "theorem refused_iff (q : Req) : refused q = true ↔ requiresRefusal q :=\n" ++
     "  List.any_eq_true\n\n" ++
     "theorem refused_of (r : Rule) (q : Req) (h : r ∈ rules) (hf : fires r q = true) :\n" ++
     "    refused q = true := (refused_iff q).mpr ⟨r, h, hf⟩\n\n" ++
     "\n\n".intercalate (views.map leanTheorems) ++ "\n\nend Loans\n"),
   ("Ledger.lean", "import SpecTools.Audit\nimport ProofObligations\n\n" ++
     "namespace Loans\nopen SpecTools.Ledger\n\n" ++
     s!"def ledger : List Row := [\n{leanRows views}\n] ++\n" ++
     "  [{ id := \"implementation\", clause := \"Executable refusal agrees with the Lean specification\",\n" ++
     "     theorems := [``refused_iff] }]\n\nend Loans\n\n" ++
     "#eval SpecTools.Audit.run Loans.ledger `ProofObligations\n"),
   ("Counterexamples.lean", "import Spec\n\nnamespace Loans\n\n" ++
     (rules.head?.map fun rule =>
       s!"def atBound : Req := ⟨{rule.kind.quote}, [({(rule.measures.headD "").quote}, {rule.bound})]⟩\n\n" ++
       s!"theorem raisedBoundCounterexample : fires r{rule.id} atBound = true ∧\n" ++
       s!"    fires \{ r{rule.id} with bound := {rule.bound + 1} } atBound = false := by decide\n\n").getD
       "" ++ "end Loans\n"),
   ("lakefile.toml", config),
   ("lean-toolchain", toolchain)]

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
  -- Every artifact holds the limit one higher than the prose: they agree with one another.
  | "limit moved" => rs.map fun r =>
      let r' := { r with bound := r.bound + 1 }
      { kind := blind, clause := ruleSentence r, touches := [r.id],
        apply := onRule r.id fun v =>
          { v with model := r', python := r', test := some r', theorem_ := r' } }
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

/-! Presentations: how a person's prose states a rule, for the prose a model writes from the rule
list (the person-prose test). -/

inductive Presentation where
  /-- One sentence, as `prose` writes it. -/
  | plain
  /-- The limit in one section, its exception in another. -/
  | spread
  /-- The exception names a group, defined once elsewhere. -/
  | definedTerm
  /-- Shown only through a worked case. -/
  | exampleOnly
  /-- Stated twice in different words, meaning the same. -/
  | twoWordings
  /-- Two rules in one sentence. -/
  | folded
  deriving Repr, DecidableEq, Inhabited

def Presentation.name : Presentation → String
  | .plain => "plain"
  | .spread => "spread"
  | .definedTerm => "defined term"
  | .exampleOnly => "example only"
  | .twoWordings => "two wordings"
  | .folded => "folded"

def Presentation.all : List Presentation :=
  [.plain, .spread, .definedTerm, .exampleOnly, .twoWordings, .folded]

/-- The presentations the deciding test weights toward, if Opus finds every blind spot. -/
def Presentation.hard : List Presentation := [.spread, .definedTerm, .exampleOnly]

/-- Rule `id`'s presentation in variant `index` of a batch from `seed`, drawn from `offered`, or
plain when nothing is offered: a function of these alone, so a variant's other rules and plants
change nothing. -/
def presentationOf (offered : List Presentation) (seed index id : Nat) : Presentation :=
  offered.getD (draw (next (next (seed + index * 7919) + (id + 1) * 104729)) offered.length) .plain

/-- Each rule's drawn presentation in a variant, by rule number. -/
def drawn (offered : List Presentation) (seed index : Nat) (rs : List Rule) :
    List (Nat × Presentation) :=
  rs.map fun r => (r.id, presentationOf offered seed index r.id)

/-- The last folded entry made plain when the folded ones are odd in number, the rest unchanged. -/
def pairFolded (ps : List (Nat × Presentation)) : List (Nat × Presentation) :=
  if (ps.countP (·.2 == .folded)) % 2 == 0 then ps
  else (go ps.reverse).reverse
where
  go : List (Nat × Presentation) → List (Nat × Presentation)
    | [] => []
    | (id, p) :: rest => if p == .folded then (id, .plain) :: rest else (id, p) :: go rest

/-- Each rule's presentation in a variant, by rule number: as drawn, the folded ones paired. -/
def presentations (offered : List Presentation) (seed index : Nat) (rs : List Rule) :
    List (Nat × Presentation) :=
  pairFolded (drawn offered seed index rs)

end SpecTools.Generated
