import SpecTools.Synthetic
import SpecTools.Clauses

/-!
The synthetic test's scorer: a run's findings (each a clause quoted from the prose or the ledger,
and a kind) against a variant's key. A plant is found when some finding quotes its clause; a finding
quoting no planted clause is a false alarm. Clauses compare by `Clauses.normalize`. Pure.
-/

namespace SpecTools.Score
open SpecTools.Synthetic SpecTools.Clauses

structure Finding where
  clause : String
  kind : String
  deriving Repr, DecidableEq, Inhabited

/-- A finding names a plant's clause. -/
def names (f : Finding) (p : Plant) : Bool := normalize f.clause == normalize p.clause

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
