import SpecTools.Discrimination

namespace RefundObservationExample
open SpecTools.Score.Evidence

abbrev PaymentObservation := Observation Nat (Option Nat) Nat

def checksReturnOnly (sample : PaymentObservation) : Prop :=
  sample.outcome.all (· ≤ sample.input) = true

def creditsBounded (sample : PaymentObservation) : Prop :=
  checksReturnOnly sample ∧ sample.effects.sum ≤ sample.input

def duplicatePayment : PaymentObservation := ⟨10, some 10, [10, 10]⟩

theorem duplicateCredit :
    BoundDistinction "total refund" creditsBounded checksReturnOnly .admitsExtra duplicatePayment := by
  constructor
  change checksReturnOnly duplicatePayment ∧ ¬ creditsBounded duplicatePayment
  unfold creditsBounded checksReturnOnly
  decide

#eval IO.println <| describeBound duplicateCredit `RefundObservationExample.duplicateCredit fun sample =>
  let returned := (sample.outcome.map toString).getD "no amount"
  s!"A payment of {sample.input} returns {returned} and issues credits {sample.effects}, totaling {sample.effects.sum}."

end RefundObservationExample
