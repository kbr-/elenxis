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

end SalonCall

#check SalonCall.interpretationsDiffer
