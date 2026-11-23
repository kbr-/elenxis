import SpecTools.Generated
import SpecTools.Clauses

/-!
The synthetic test's scorer: a run's findings (each a clause quoted from the prose or the ledger, a
kind, and the ledger row it concerns) against a variant's key. A plant is found when some finding
names it, by row where both have one and by quote otherwise; a finding naming no plant is a false
alarm. Clauses compare by `Clauses.normalize`. Pure.
-/

namespace SpecTools.Score
open SpecTools.Synthetic SpecTools.Clauses

def legacyMetric : String := "legacy_row_match"

def legacyHeader : String :=
  s!"Score metric: {legacyMetric}\nFormal distinction: unknown\nHuman judgment: unknown"

/-- A finding: the clause it quotes, its kind, and the ledger row it names, which answers saved
before rows were asked for lack. -/
structure Finding where
  clause : String
  kind : String
  row : Option String := none
  deriving Repr, DecidableEq, Inhabited

/-- A quote's sentences, normalized, the empty ones dropped. The generated prose holds no decimal
point, so a period ends a sentence. -/
def sentences (s : String) : List String :=
  ((s.splitOn ".").map normalize).filter (· ≠ "")

/-- A finding names a plant's clause: its quote is the clause, or holds at most two sentences (a
clause with the one beside it, such as a rule with its exception) one of which is the clause. A
quote of more sentences names a plant only by equality, so quoting the whole prose names nothing. -/
def quoteNames (f : Finding) (p : Plant) : Bool :=
  normalize f.clause == normalize p.clause ||
    ((sentences f.clause).length ≤ 2 && (sentences f.clause).contains (normalize p.clause))

/-- The legacy metric matches a plant by row when both have one: the rows name one rule (`rK` and
`rK-exempt` alike), whatever the quote, since a person's sentence never equals a generated clause.
Without both rows, by its quote. -/
def names (f : Finding) (p : Plant) : Bool :=
  match f.row, p.row with
  | some fr, some pr => (Generated.rowRule pr).isSome && Generated.rowRule fr == Generated.rowRule pr
  | _, _ => quoteNames f p

structure Score where
  /-- Plants found, by kind. -/
  found : List String
  /-- Plants missed, by kind. -/
  missed : List String
  falseAlarms : Nat
  deriving Repr, DecidableEq, Inhabited

def score (key : List Plant) (findings : List Finding) : Score where
  found := (key.filter fun p => findings.any (names · p)).map (·.kind)
  missed := (key.filter fun p => !findings.any (names · p)).map (·.kind)
  falseAlarms := (findings.filter fun f => !key.any (names f)).length

/-- The presentation a row's rule took in the variant, by name; "no row" for a row naming no rule of
`shown`, or none. -/
def presentationOfRow (shown : List (Nat × Generated.Presentation)) (row : Option String) : String :=
  match row.bind Generated.rowRule >>= fun k => List.lookup k shown with
  | some (p : Generated.Presentation) => p.name
  | none => "no row"

/-- A run's score split by presentation: for each presentation some plant or false alarm took, the
plants, those found and the false alarms, a plant and a finding each counted under its row's
rule's presentation. -/
def byPresentation (shown : List (Nat × Generated.Presentation)) (key : List Plant)
    (findings : List Finding) : List (String × Nat × Nat × Nat) :=
  let alarms := findings.filter fun f => !key.any (names f)
  ((Generated.Presentation.all.map (·.name)) ++ ["no row"]).filterMap fun n =>
    let planted := key.filter (presentationOfRow shown ·.row == n)
    let found := planted.filter fun p => findings.any (names · p)
    let al := alarms.filter (presentationOfRow shown ·.row == n)
    if planted.isEmpty && al.isEmpty then none else some (n, planted.length, found.length, al.length)

/-- The bar over `n` variants both arms ran: the ledger's arm finds more shared blind spots than
the baseline's (`ledgerBlind` against `baseBlind`, totals over the same variants, so their averages
compare as their sums), at no more false alarms per variant on average than the baseline's plus
one (`ledgerAlarms / n ≤ baseAlarms / n + 1`, which over `n` variants is
`ledgerAlarms ≤ baseAlarms + n`). -/
def barMet (ledgerBlind baseBlind ledgerAlarms baseAlarms n : Nat) : Bool :=
  baseBlind < ledgerBlind && ledgerAlarms ≤ baseAlarms + n

def barText (ledgerBlind baseBlind ledgerAlarms baseAlarms n : Nat) : String :=
  let verdict := if barMet ledgerBlind baseBlind ledgerAlarms baseAlarms n then "met" else "not met"
  s!"{verdict} (shared blind spots {ledgerBlind} against {baseBlind}; false alarms \
    {ledgerAlarms} against at most {baseAlarms} + {n} over {n} variants)"

end SpecTools.Score
