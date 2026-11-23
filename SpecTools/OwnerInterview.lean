import SpecTools.Owners

namespace SpecTools.OwnerInterview

open Lean SpecTools.Model SpecTools.Generated

inductive Speaker where
  | developer
  | owner
  deriving DecidableEq

def Speaker.name : Speaker → String
  | .developer => "Developer"
  | .owner => "Owner"

def Speaker.forTurn (completed : Nat) : Speaker :=
  if completed % 2 == 0 then .developer else .owner

def ownerBrief (vocab : Vocab) (rules : List Rule)
    (flaws : List Owners.Imperfection) : String :=
  Owners.persona vocab ++ "\n\n" ++ "\n".intercalate (rules.map fun rule =>
    s!"- {Owners.ownerRuleText rule} How you remember it: \
      {Owners.flawInstruction rule ((flaws.find? (·.rule == rule.id)).map (·.flaw))}.")

def prompt (speaker : Speaker) (brief transcript : String) (turnsLeft : Nat) : String :=
  let instructions := match speaker with
    | .developer => "You're a freelance developer calling back someone who asked about a site. \
        Respond to the last thing they said. Learn how they handle requests today. You know \
        only what they say on this call."
    | .owner => "You're answering a call from someone who might make your website. Say what you \
        would say to them now. You have these private facts. Let them come out as the call \
        needs them and keep the things you are unsure of unresolved.\n\n" ++ brief
  s!"{instructions}\n\nWrite just your next spoken turn, without a speaker label. Answer with \
    its words in `line`. Set `ended` only if your words end the call. There are at most \
    {turnsLeft} turns left.\n\nCall so far:\n{transcript}"

theorem developerPrompt_ignores_brief (a b transcript : String) (turnsLeft : Nat) :
    prompt .developer a transcript turnsLeft = prompt .developer b transcript turnsLeft := rfl

structure Line where
  words : String
  ended : Bool
  deriving Inhabited

private def schema : Json :=
  Json.mkObj [("type", toJson "object"),
    ("properties", Json.mkObj [
      ("line", Json.mkObj [("type", toJson "string")]),
      ("ended", Json.mkObj [("type", toJson "boolean")])]),
    ("required", toJson ["line", "ended"]), ("additionalProperties", toJson false)]

private def lineOf (json : Json) : Except String Line := do
  let raw ← json.getObjValAs? String "line"
  let words := (raw.replace "\r" " " |>.replace "\n" " ").trimAscii.toString
  if words.isEmpty then throw "a spoken turn cannot be empty"
  pure ⟨words, ← json.getObjValAs? Bool "ended"⟩

private def savedLines (journal : String) : Except String (Array Line) := do
  let mut lines := #[]
  for line in journal.splitOn "\n" do
    unless line.trimAscii.isEmpty do
      let row ← Json.parse line
      if (row.getObjVal? "error").isOk then continue
      let speaker ← row.getObjValAs? String "speaker"
      unless speaker == (Speaker.forTurn lines.size).name && !(lines.back?.any (·.ended)) do
        throw "the interview journal has invalid turn order"
      lines := lines.push (← lineOf row)
  return lines

example :
    (savedLines "{\"speaker\":\"Owner\",\"line\":\"Hello\",\"ended\":false}").isOk = false := by
  native_decide

example :
    ((savedLines ("{\"speaker\":\"Developer\",\"line\":\"Hello\",\"ended\":false}\n" ++
      "{\"speaker\":\"Owner\",\"error\":\"connection closed\"}\n" ++
      "{\"speaker\":\"Owner\",\"line\":\"Is that Robin?\",\"ended\":false}")).toOption.map
      Array.size) = some 2 := by
  native_decide

private def render (lines : Array Line) : String :=
  "\n\n".intercalate (lines.toList.zipIdx.map fun (line, index) =>
    s!"{(Speaker.forTurn index).name}: {line.words}")

/-- Collect one response per model call and flush its receipt before advancing to the other
speaker. A failed call leaves the journal ready to continue from the same turn. -/
def collect (runner : Runner) (backend : Backend) (vocab : Vocab)
    (rules : List Rule) (flaws : List Owners.Imperfection)
    (dir : System.FilePath) (limit timeoutMs : Nat) : IO UInt32 := do
  let brief := ownerBrief vocab rules flaws
  let config := dir / "interview.json"
  let journal := dir / "turns.jsonl"
  let identity := (Json.mkObj [("brief", toJson brief), ("backend", toJson backend.describe)]).compress
  if ← config.pathExists then
    unless (← IO.FS.readFile config) == identity do
      throw (IO.userError "interview brief or backend differs from the saved run")
  else
    if ← journal.pathExists then
      throw (IO.userError "the existing interview journal has no saved brief")
    IO.FS.createDirAll dir
    IO.FS.writeFile config identity
  let mut lines ← if ← journal.pathExists then IO.ofExcept (savedLines (← IO.FS.readFile journal))
    else pure #[]
  if lines.size > limit then
    throw (IO.userError "TURNS is below the number of saved turns")
  let out ← IO.FS.Handle.mk journal .append
  for _ in List.range (limit - lines.size) do
    if lines.back?.any (·.ended) then break
    let speaker := Speaker.forTurn lines.size
    let scratch ← IO.FS.createTempDir
    let result ← try
        Usage.askRecorded "owner-interview-turn" runner [backend] backend
          { prompt := prompt speaker brief (render lines) (limit - lines.size), schema, timeoutMs }
          scratch
      finally IO.FS.removeDirAll scratch
    let (answer, usage) := result
    let parsed := (answer.mapError Failure.describe).bind (fun reply => lineOf reply.answer)
    let receipt := [("speaker", toJson speaker.name), ("usage", Usage.asJson usage)]
    match parsed with
    | .error why =>
      out.putStrLn (Json.mkObj (receipt ++ [("error", toJson why)])).compress
      out.flush
      IO.eprintln s!"interview stopped at {speaker.name}: {why}"
      return 1
    | .ok line =>
      out.putStrLn (Json.mkObj (receipt ++ [("line", toJson line.words),
        ("ended", toJson line.ended)])).compress
      out.flush
      lines := lines.push line
      IO.println s!"interview: {lines.size} turns saved"
  IO.FS.writeFile (dir / "draft.md") (render lines ++ "\n")
  return 0

end SpecTools.OwnerInterview
