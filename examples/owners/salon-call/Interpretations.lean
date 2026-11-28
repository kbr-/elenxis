-- SPDX-License-Identifier: Apache-2.0
import SpecTools.ScoreEvidence
import SpecTools.Mutation

namespace SalonCall
open SpecTools.Score.Evidence

def twoNoShowReading (noShows : Nat) : Prop := noShows < 2
def fourNoShowReading (noShows : Nat) : Prop := noShows < 4

theorem interpretationsDiffer :
    BoundDistinction "children's online booking" twoNoShowReading fourNoShowReading
      .admitsExtra 2 := by
  constructor
  change 2 < 4 ∧ ¬ 2 < 2
  decide

theorem fourIsStrictlyWeaker : Relation.strictlyWeaker.Holds twoNoShowReading fourNoShowReading :=
  ⟨fun _ h => Nat.lt_trans h (by decide : 2 < 4), ⟨2, interpretationsDiffer.distinguishes⟩⟩

open SpecTools.Mutation in
#eval show Lean.Elab.Command.CommandElabM Unit from do
  let report ← review [{
    id := "two-or-four", requirement := "children's online booking", revision := "salon-call-dialogue",
    origin := "competing clauses in text.md", original := ``twoNoShowReading,
    candidate := .named ``fourNoShowReading, attempts := [⟨.relation .strictlyWeaker, some ``fourIsStrictlyWeaker⟩],
    scenario := "A parent books online after two missed appointments. The first rule refuses the booking; the second allows it.",
    proposedProperty := "Should this parent have to call after two missed appointments, or only after four?" }]
  IO.println report.compress

#eval IO.println <| describeBound interpretationsDiffer `SalonCall.interpretationsDiffer fun noShows =>
  s!"After {noShows} no-shows, the four-no-show reading permits an online booking for a child."

end SalonCall

#check SalonCall.interpretationsDiffer
