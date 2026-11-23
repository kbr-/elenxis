import SpecTools.ScoreEvidence

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

#eval IO.println <| describeBound interpretationsDiffer `SalonCall.interpretationsDiffer fun noShows =>
  s!"After {noShows} no-shows, the four-no-show reading permits an online booking for a child."

end SalonCall

#check SalonCall.interpretationsDiffer
