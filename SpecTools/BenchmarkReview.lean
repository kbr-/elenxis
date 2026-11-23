import SpecTools.Benchmark

namespace SpecTools.Benchmark.Review
open Lean

structure ArmReview where
  arm : Arm
  response : Json
  accepted : Bool
  deriving FromJson

structure PairReview where
  id : String
  hasDefect : Bool
  arms : List ArmReview
  deriving FromJson

structure Cost where
  currency : String
  minorUnits : Nat
  deriving FromJson, ToJson

structure ReviewFile where
  version : Nat
  reviewer : String
  synthetic : Bool
  pairs : List PairReview
  reviewMillis : Option Nat := none
  ownerMillis : Option Nat := none
  humanCost : Option Cost := none
  deriving FromJson

/-- A counted success contains both a reported diagnosis and an independently identified defect. -/
structure Mark where
  diagnosis : Bool
  defect : Bool
  accepted : Bool

def Mark.hit (mark : Mark) : Bool := mark.diagnosis && mark.defect && mark.accepted

theorem hit_iff (mark : Mark) :
    mark.hit = true ↔ mark.diagnosis = true ∧ mark.defect = true ∧ mark.accepted = true := by
  simp [Mark.hit, Bool.and_eq_true, and_assoc]

theorem hits_bounded (marks : List Mark) :
    marks.countP Mark.hit ≤ marks.countP Mark.diagnosis ∧
      marks.countP Mark.hit ≤ marks.countP Mark.defect := by
  induction marks with
  | nil => simp
  | cons mark rest ih =>
    obtain ⟨hd, hr⟩ := ih
    cases mark with
    | mk diagnosis defect accepted =>
      cases diagnosis <;> cases defect <;> cases accepted <;>
        simp [Mark.hit] <;> omega

private def ratio (hits denominator : Nat) : Json :=
  if denominator == 0 then "unknown"
  else Json.mkObj [("numerator", toJson hits), ("denominator", toJson denominator)]

private structure SavedArm where
  arm : Arm
  response : Json
  score : Json
  deriving FromJson

private structure SavedPair where
  id : String
  arms : List SavedArm
  deriving FromJson

private structure SavedSummary where
  arm : Arm
  notAttempted : Nat
  deriving FromJson

private def bothArms (arms : List Arm) : Bool :=
  arms.length == 2 && arms.contains .baseline && arms.contains .elenxis

private def marksFor (arm : Arm) (paired : List (SavedPair × PairReview)) :
    Except String (List Mark) := paired.mapM fun (saved, review) => do
  let some reading := saved.arms.find? (·.arm == arm)
    | throw s!"Missing saved arm in {saved.id}"
  let some judgment := review.arms.find? (·.arm == arm)
    | throw s!"Missing reviewed arm in {saved.id}"
  unless judgment.response == reading.response do
    throw s!"Review response differs from the saved response in {saved.id}"
  let predicted ← if (reading.score.getObjVal? "failure").isOk then pure false else do
    let diagnoses ← reading.score.getObjValAs? Nat "diagnoses"
    unless diagnoses ≤ 1 && reading.response != Json.null do
      throw s!"Invalid diagnosis count or response in {saved.id}"
    pure (diagnoses == 1)
  if judgment.accepted && !(predicted && review.hasDefect) then
    throw s!"Accepted diagnosis needs a reported diagnosis and a defect in {saved.id}"
  return ⟨predicted, review.hasDefect, judgment.accepted⟩

private def measure (arm : Arm) (marks : List Mark) (complete : Bool) : Json :=
  let hits := marks.countP Mark.hit
  Json.mkObj [("arm", toJson arm),
    ("precision", if complete then ratio hits (marks.countP Mark.diagnosis) else "unknown"),
    ("recall", if complete then ratio hits (marks.countP Mark.defect) else "unknown"),
    ("reviewedPairs", toJson marks.length)]

/-- Join an attributed review to a completed journal. Provider-limited samples remain partial. -/
def report (journal : String) (review : ReviewFile) : Except String Json := do
  unless review.version == 1 && !review.reviewer.trimAscii.isEmpty do
    throw "Expected a version 1 review with an attributed reviewer"
  if review.humanCost.any (·.currency.trimAscii.isEmpty) then
    throw "Human cost needs a currency"
  let rows ← (journal.splitOn "\n").filter (!·.trimAscii.isEmpty) |>.mapM Json.parse
  let some metadata := rows.head? | throw "Empty benchmark journal"
  let some summary := rows.getLast? | throw "Missing benchmark summary"
  unless (metadata.getObjValAs? String "type").toOption == some "metadata" &&
      (metadata.getObjValAs? Nat "version").toOption == some 1 &&
      (summary.getObjValAs? String "type").toOption == some "summary" do
    throw "Expected a version 1 benchmark journal ending in its summary"
  let summaries ← summary.getObjValAs? (List SavedSummary) "arms"
  unless bothArms (summaries.map (·.arm)) &&
      (summaries.map (·.notAttempted)).eraseDups.length == 1 do
    throw "Benchmark summary must describe both arms and agree on missing pairs"
  let saved ← (rows.drop 1).dropLast |>.mapM fun row => do
    unless (row.getObjValAs? String "type").toOption == some "pair" do
      throw "Unexpected benchmark journal entry"
    fromJson? (α := SavedPair) row
  let ids := saved.map (·.id)
  let reviewedIds := review.pairs.map (·.id)
  unless ids.eraseDups == ids && reviewedIds.eraseDups == reviewedIds &&
      ids.length == reviewedIds.length && ids.all reviewedIds.contains do
    throw "Review must cover each saved case exactly once"
  let paired ← saved.mapM fun pair => do
    let some entry := review.pairs.find? (·.id == pair.id)
      | throw s!"Missing review for {pair.id}"
    unless bothArms (pair.arms.map (·.arm)) && bothArms (entry.arms.map (·.arm)) do
      throw s!"Expected one review for each arm in {pair.id}"
    return (pair, entry)
  let complete := summaries.all (·.notAttempted == 0)
  let baseline ← marksFor .baseline paired
  let elenxis ← marksFor .elenxis paired
  let observed {α : Type} [ToJson α] (value : Option α) : Json :=
    value.map toJson |>.getD "unknown"
  return Json.mkObj [("version", toJson (1 : Nat)), ("reviewer", toJson review.reviewer),
    ("synthetic", toJson review.synthetic), ("complete", toJson complete),
    ("reviewMillis", observed review.reviewMillis), ("ownerMillis", observed review.ownerMillis),
    ("humanCost", observed review.humanCost),
    ("arms", toJson [measure .baseline baseline complete, measure .elenxis elenxis complete])]

def run (journalFile reviewFile : String) : IO UInt32 := do
  let journal ← IO.FS.readFile journalFile
  let payload ← IO.FS.readFile reviewFile
  match (Json.parse payload >>= fromJson? >>= report journal) with
  | .ok result => IO.println result.compress; return 0
  | .error error => IO.eprintln error; return 2

end SpecTools.Benchmark.Review
