import SpecTools.Discrimination
import SpecTools.ScoreObservations
import SpecTools.BackendConfig

namespace SpecTools.Benchmark
open Lean SpecTools.Model SpecTools.Score.Observations SpecTools.Score.Evidence

structure Case where
  id : String
  family : String
  prose : String
  candidate : String
  rule : Nat
  property : String
  referenceLimit : Nat
  candidateLimit : Nat
  deriving FromJson

structure KeyedCase where
  id : String
  key : KeyFile
  deriving FromJson

inductive Arm where
  | baseline
  | elenxis
  deriving DecidableEq, ToJson

private def disposition : List String := ["too weak", "extra", "no defect", "unknown"]

private def schema : Json :=
  let array (type : String) :=
    Json.mkObj [("type", "array"), ("items", Json.mkObj [("type", toJson type)])]
  Json.mkObj [("type", "object"), ("additionalProperties", toJson false),
    ("required", toJson ["category", "rules", "properties", "observations", "questions", "reason"]),
    ("properties", Json.mkObj [
      ("category", Json.mkObj [("type", "string"), ("enum", toJson disposition)]),
      ("rules", array "integer"), ("properties", array "string"), ("observations", array "integer"),
      ("questions", array "string"), ("reason", Json.mkObj [("type", "string")])])]

structure Answer where
  category : String
  rules : List Nat
  properties : List String
  observations : List Nat
  questions : List String
  reason : String
  deriving FromJson

private def difference (fixture : Case) (noShows : Nat) :
    Option (Counterexample (· < fixture.referenceLimit) (· < fixture.candidateLimit)) :=
  compareObservation (· < fixture.referenceLimit) (· < fixture.candidateLimit) noShows

private def scenario (noShows : Nat) : String :=
  s!"A customer requests online booking after {noShows} no-shows."

private def assistance (fixture : Case) : String :=
  let atBoundary := min fixture.referenceLimit fixture.candidateLimit
  match difference fixture atBoundary with
  | none => "Lean searched the smaller cutoff and found no distinction at that observation."
  | some witness =>
    let path := match witness.direction with
      | .admitsExtra => "Only the candidate admits this booking."
      | .rejectsRequired => "Only the reference admits this booking."
    scenario atBoundary ++ " " ++ path

def question (fixture : Case) (arm : Arm) (timeoutMs : Nat) : Question :=
  let common := s!"Compare the owner's requirements with the candidate contract.\n\n" ++
    s!"Owner's requirements:\n{fixture.prose}\n\nCandidate contract:\n{fixture.candidate}\n\n" ++
    s!"The booking rule's public identifier is {fixture.rule} and its property is {fixture.property.quote}. " ++
    "Choose too weak for extra permitted behavior, extra for an unnecessary restriction, no defect " ++
    "if the formulations agree, or unknown when you cannot decide. Give the affected rule number " ++
    "and property, plus a natural-number no-show count that distinguishes the contracts if available. " ++
    "Use empty arrays where no value applies. Ask the owner only for information needed to decide."
  let prompt := match arm with
    | .baseline => common
    | .elenxis => common ++ "\n\nLean comparison of the modeled readings:\n" ++ assistance fixture
  { prompt, schema, timeoutMs }

theorem same_budget (fixture : Case) (cap : Nat) :
    (question fixture .baseline cap).timeoutMs = (question fixture .elenxis cap).timeoutMs := rfl

private def directionCategory : Direction → String
  | .admitsExtra => "too weak"
  | .rejectsRequired => "extra"

private def finding (answer : Answer) : Option EvidenceFinding := do
  let kind ← SpecTools.Gaps.Kind.parse answer.category
  let location := answer.rules.head?.map (⟨·, .main⟩)
  return ⟨"diagnosis", location, answer.properties.head?, some kind⟩

private def verified (fixture : Case) (answer : Answer) :
    Option (Counterexample (· < fixture.referenceLimit) (· < fixture.candidateLimit)) := do
  let observation ← answer.observations.head?
  let witness ← difference fixture observation
  if answer.rules == [fixture.rule] && answer.properties == [fixture.property] &&
      answer.category == directionCategory witness.direction then
    return witness
  none

private def check (fixture : Case) (key : KeyFile) (answer : Answer) : Except String Json := do
  unless disposition.contains answer.category && answer.rules.length ≤ 1 &&
      answer.properties.length ≤ 1 && answer.observations.length ≤ 1 do
    throw "one diagnosis and at most one observation are allowed per reading"
  let reported := finding answer
  let primary ← report key ⟨1, reported.toList⟩
  let formal := (verified fixture answer).map fun witness => Json.mkObj [
    ("direction", toJson witness.direction), ("observation", toJson witness.observation),
    ("theorem", "SpecTools.Score.Evidence.Counterexample.sound"),
    ("scenario", toJson (scenario witness.observation))]
  return (primary.setObjVal! "distinguished" (formal.getD (toJson "unknown")))
    |>.setObjVal! "diagnosis" (toJson answer.category)
    |>.setObjVal! "intactFalseAlarm" (toJson (key.plants.isEmpty && reported.isSome))
    |>.setObjVal! "abstained" (toJson (answer.category == "unknown"))
    |>.setObjVal! "ownerQuestions" (toJson answer.questions.length)
    |>.setObjVal! "plantedLocations" (toJson ((key.plants.map (·.location)).eraseDups.length))
    |>.setObjVal! "plantedCategories" (toJson key.plants.length)
    |>.setObjVal! "diagnoses" (toJson (if reported.isSome then (1 : Nat) else 0))

private def pairedComplete (cases : List Case) (keys : List KeyedCase) : Bool :=
  let ids := cases.map (·.id)
  let keyIds := keys.map (·.id)
  !ids.isEmpty && ids.eraseDups == ids && keyIds.eraseDups == keyIds &&
    ids.all keyIds.contains && keyIds.all ids.contains

private def failureKind : Failure → String
  | .exited _ _ output =>
    if (output.splitOn "hit your usage limit").length > 1 then "usage limit" else "process exit"
  | .refused .. => "refused"
  | .timedOut .. => "timeout"
  | .malformed .. => "invalid model answer"

private def failureReport (error : Failure) : Json :=
  let report := Json.mkObj [("failure", toJson (failureKind error))]
  match error with
  | .exited _ code _ => report.setObjVal! "exitCode" (toJson code.toNat)
  | .timedOut _ millis => report.setObjVal! "timeoutMillis" (toJson millis)
  | _ => report

private def runArm (fixture : Case) (key : KeyFile) (backend : Backend) (arm : Arm)
    (timeoutMs : Nat) : IO Json := do
  let toolStart ← IO.monoMsNow
  let request := question fixture arm timeoutMs
  let bytes := request.prompt.utf8ByteSize
  let toolMs := (← IO.monoMsNow) - toolStart
  let scratch ← IO.FS.createTempDir
  let (result, usage) ← try askWithUsage liveRunner [backend] backend request scratch
    finally IO.FS.removeDirAll scratch
  let checkStart ← IO.monoMsNow
  let (response, checks) := match result with
    | .error error => (Json.null, failureReport error)
    | .ok outcome =>
      let checked := fromJson? outcome.answer >>= check fixture key
      (outcome.answer, match checked with
        | .ok report => report
        | .error message => Json.mkObj [("failure", toJson message)])
  let checkMs := (← IO.monoMsNow) - checkStart
  return Json.mkObj [("arm", toJson arm), ("response", response), ("score", checks),
    ("modelUsage", Usage.asJson usage), ("preparedMillis", toJson toolMs),
    ("checkingMillis", toJson checkMs), ("promptBytes", toJson bytes)]

private def metric (key : String) (score : Json) : Nat :=
  (score.getObjValAs? Nat key).toOption.getD 0

private def measure (arm : Arm) (keys : List KeyedCase) (rows : List Json) : Json :=
  let scores := rows.filterMap (fun row => (row.getObjVal? "score").toOption)
  let count (name : String) := (scores.map (metric name)).sum
  let countWhere (name : String) := scores.countP fun score =>
    (score.getObjValAs? Bool name).toOption.getD false
  let countArray (name : String) := (scores.map fun score =>
    ((score.getObjValAs? (Array Json) name).toOption.getD #[]).size).sum
  let distinctionCount := scores.countP fun score =>
    ((score.getObjVal? "distinguished").bind (·.getObjVal? "direction")).isOk
  let locations := (keys.map fun key => ((key.key.plants.map (·.location)).eraseDups).length).sum
  let categories := (keys.map (·.key.plants.length)).sum
  Json.mkObj [("arm", toJson arm),
    ("located", toJson (countArray "located")), ("plantedLocations", toJson locations),
    ("classified", toJson (countArray "classified")), ("plantedCategories", toJson categories),
    ("failed", toJson (scores.countP (fun score => (score.getObjVal? "failure").isOk))),
    ("notAttempted", toJson (keys.length - rows.length)),
    ("formalDistinctions", toJson distinctionCount), ("diagnoses", toJson (count "diagnoses")),
    ("abstentions", toJson (countWhere "abstained")), ("intactFalseAlarms", toJson (countWhere "intactFalseAlarm")),
    ("ownerQuestions", toJson (count "ownerQuestions")),
    ("preparedMillis", toJson ((rows.map (metric "preparedMillis")).sum)),
    ("checkingMillis", toJson ((rows.map (metric "checkingMillis")).sum)),
    ("modelUsage", Usage.asJson (Usage.total (rows.filterMap fun row =>
      (row.getObjVal? "modelUsage").toOption.bind Usage.fromJson?)))]

private def diagnosis (row : Json) : String :=
  ((row.getObjVal? "score").bind (·.getObjValAs? String "diagnosis")).toOption.getD "failed"

private def stoppedByQuota (row : Json) : Bool :=
  ((row.getObjVal? "score").bind (·.getObjValAs? String "failure")).toOption == some "usage limit"

private def readInput [FromJson α] (path : String) : IO α :=
  IO.FS.readFile path >>= fun text => IO.ofExcept (Json.parse text >>= fromJson?)

def run (input keyPath output : String) (timeoutMs : Nat) : IO UInt32 := do
  let cases : List Case ← readInput input
  let keys : List KeyedCase ← readInput keyPath
  unless pairedComplete cases keys && timeoutMs > 0 do
    throw (IO.userError "benchmark needs one key per distinct case and a positive timeout")
  for key in keys do
    let _ ← IO.ofExcept (report key.key ⟨1, []⟩)
  let backend ← configuredBackend
  if ← (System.FilePath.mk output).pathExists then
    throw (IO.userError "benchmark output already exists; supply a fresh filename")
  let out ← IO.FS.Handle.mk output .write
  out.putStrLn (Json.mkObj [("version", 1), ("type", "metadata"),
    ("backend", toJson backend.name), ("effort", toJson backend.effort),
    ("timeoutMillisPerArm", toJson timeoutMs), ("humanPrecision", "unknown"),
    ("humanRecall", "unknown"), ("ownerTime", "unknown"), ("humanCost", "unknown")]).compress
  out.flush
  let mut failed := false
  let mut paired := []
  for fixture in cases do
    let some keyed := keys.find? (·.id == fixture.id)
      | throw (IO.userError "benchmark key disappeared after validation")
    let baseline ← IO.asTask (runArm fixture keyed.key backend .baseline timeoutMs)
    let elenxis ← runArm fixture keyed.key backend .elenxis timeoutMs
    let baseline ← IO.ofExcept baseline.get
    let arms := [baseline, elenxis]
    let errors := arms.any fun arm =>
      ((arm.getObjVal? "score").bind (·.getObjVal? "failure")).isOk
    failed := failed || errors
    paired := (fixture.family, baseline, elenxis) :: paired
    out.putStrLn (Json.mkObj [("type", "pair"), ("id", toJson fixture.id),
      ("family", toJson fixture.family), ("arms", toJson arms)]).compress
    out.flush
    IO.println s!"{fixture.id}: paired responses saved{if errors then " with failures" else ""}"
    if arms.any stoppedByQuota then
      IO.eprintln "Benchmark stopped after the provider reported its usage limit."
      break
  let pairs := paired.reverse
  let families := (pairs.map (·.1)).eraseDups
  let variations := families.map fun family =>
    let rows := pairs.filter (·.1 == family)
    Json.mkObj [("family", toJson family),
      ("baseline", toJson (rows.map fun row => diagnosis row.2.1)),
      ("elenxis", toJson (rows.map fun row => diagnosis row.2.2))]
  out.putStrLn (Json.mkObj [("type", "summary"), ("paraphrases", toJson variations),
    ("arms", toJson [measure .baseline keys (pairs.map (·.2.1)), measure .elenxis keys (pairs.map (·.2.2))])]).compress
  out.flush
  return if failed then 1 else 0

end SpecTools.Benchmark
