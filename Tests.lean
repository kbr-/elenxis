import SpecTools

open Lean SpecTools SpecTools.Model

def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

def claude : Backend := { harness := .claudeCode, model := "m", dataGoesTo := "Anthropic" }
def codex : Backend := { harness := .codex, model := "m", dataGoesTo := "OpenAI" }

def answerSchema : Json :=
  Json.mkObj [("type", "object"), ("required", Json.arr #["answer"]),
    ("additionalProperties", false),
    ("properties", Json.mkObj [("answer", Json.mkObj [("type", "integer")])])]

def question (schema : Json := answerSchema) (prompt : String := "q") : Question :=
  { prompt, schema, timeoutMs := 1000 }

def ran (code : UInt32) (stdout : String) (stderr : String := "")
    (readBack : List (String × String) := []) (millis : Nat := 1) : Option Ran :=
  some { exitCode := code, stdout, stderr, readBack, millis }

/-- A runner that records the invocation it got and returns a scripted result. -/
def scripted (result : Option Ran) (seen : IO.Ref (List Invocation)) : Runner :=
  fun inv _ _ => do seen.modify (· ++ [inv]); return result

def claudeReport (structured : String) (isError := false) : String :=
  s!"\{\"type\":\"result\",\"is_error\":{isError},\"structured_output\":{structured}," ++
    "\"usage\":{\"input_tokens\":10,\"output_tokens\":5}}"

def run (runner : Runner) (backend : Backend) (q : Question := question) :
    IO (Except Failure Outcome) :=
  ask runner [claude, codex] backend q "/scratch"

def isMalformed : Except Failure Outcome → Bool
  | .error (.malformed _ _) => true
  | _ => false

def testSchema : IO Unit := do
  ensure (Schema.unsupported answerSchema).isNone "the answer schema is inside the subset"
  let withPattern := Json.mkObj [("type", "string"), ("pattern", "a+")]
  ensure (Schema.unsupported withPattern).isSome "a keyword outside the subset is refused"
  ensure (Schema.violation answerSchema (Json.mkObj [("answer", (5 : Nat))])).isNone
    "a conforming answer passes"
  for bad in [Json.mkObj [], Json.mkObj [("answer", "five")],
      Json.mkObj [("answer", (5 : Nat)), ("extra", true)], Json.arr #[]] do
    ensure (Schema.violation answerSchema bad).isSome s!"{bad.compress} must break the schema"
  let listSchema := Json.mkObj [("type", "array"), ("items", Json.mkObj [("enum", Json.arr #["a", "b"])])]
  ensure (Schema.violation listSchema (Json.arr #["a", "b"])).isNone "allowed items pass"
  ensure (Schema.violation listSchema (Json.arr #["a", "c"])).isSome "an item outside the enum fails"

def testClaude : IO Unit := do
  let seen ← IO.mkRef []
  let ok ← run (scripted (ran 0 (claudeReport "{\"answer\":5}") (millis := 7)) seen) claude
  match ok with
  | .ok outcome =>
    ensure (outcome.answer == Json.mkObj [("answer", (5 : Nat))]) "the answer is parsed"
    ensure (outcome.cost == { millis := 7, tokens := some 15 }) "the cost is returned"
  | .error f => throw <| IO.userError s!"a valid answer failed: {f.describe}"
  let inv := (← seen.get).head!
  ensure (inv.cmd == "claude" && inv.cwd == "/scratch") "claude runs in the scratch directory"
  ensure (inv.args.contains "--safe-mode") "claude runs without the user's settings"
  let toolsAt := inv.args.findIdx? (· == "--tools")
  ensure (toolsAt.bind (fun i => inv.args[i+1]?) == some "") "claude runs with no tools"
  ensure (inv.args.back? == some "q") "the prompt is the last argument"
  let broken ← run (scripted (ran 0 (claudeReport "{\"answer\":\"x\"}")) seen) claude
  ensure (isMalformed broken) "an answer breaking the schema is an error"
  let reported ← run (scripted (ran 0 (claudeReport "{}" (isError := true))) seen) claude
  ensure (isMalformed reported) "the harness's own error is an error"
  let garbage ← run (scripted (ran 0 "not json") seen) claude
  ensure (isMalformed garbage) "output that is no JSON is an error"

def testCodex : IO Unit := do
  let seen ← IO.mkRef []
  let ok ← run (scripted (ran 0 "" (readBack := [("answer.json", "{\"answer\":5}")])) seen) codex
  ensure (match ok with | .ok o => o.answer == Json.mkObj [("answer", (5 : Nat))] | _ => false)
    "codex's answer file is read"
  let inv := (← seen.get).head!
  let sandboxAt := inv.args.findIdx? (· == "--sandbox")
  ensure (sandboxAt.bind (fun i => inv.args[i+1]?) == some "read-only") "codex runs read-only"
  ensure (inv.files.lookup "schema.json" == some answerSchema.compress) "codex gets the schema file"
  let usageLimit ← run (scripted (ran 1 "" "ERROR: You've hit your usage limit.") seen) codex
  ensure (match usageLimit with
    | .error (.exited name 1 lines) => name == "codex/m" && (lines.splitOn "usage limit").length > 1
    | _ => false) "a non-zero exit names the backend and its output"
  let missing ← run (scripted (ran 0 "") seen) codex
  ensure (isMalformed missing) "a missing answer file is an error"

def testRefusals : IO Unit := do
  let seen ← IO.mkRef []
  let runner := scripted (ran 0 (claudeReport "{\"answer\":5}")) seen
  let other : Backend := { claude with model := "other" }
  let notAllowed ← ask runner [codex] claude question "/scratch"
  ensure (match notAllowed with | .error (.refused _ _) => true | _ => false)
    "a backend the project doesn't allow is refused"
  let _ ← ask runner [claude] other question "/scratch"
  let badSchema ← run runner claude (question (Json.mkObj [("type", "string"), ("format", "date")]))
  ensure (match badSchema with | .error (.refused _ _) => true | _ => false)
    "a schema outside the subset is refused"
  let huge ← run runner claude (question (prompt := "".pushn 'x' (maxPromptBytes + 1)))
  ensure (match huge with | .error (.refused _ _) => true | _ => false) "an oversized prompt is refused"
  ensure ((← seen.get).isEmpty) "no process starts for a refused call"
  let timedOut ← run (scripted none seen) claude
  ensure (match timedOut with | .error (.timedOut "claude-code/m" 1000) => true | _ => false)
    "an overrun names the backend and its limit"

def testAgentRuns : IO Unit := do
  let inv := agentInvocation claude "do it" ["Read", "Bash(spec-tools:*)"] "/copy"
  ensure (inv.cwd == "/copy") "an agent run works in its copy"
  let toolsAt := inv.args.findIdx? (· == "--tools")
  ensure (toolsAt.bind (fun i => inv.args[i+1]?) == some "Read,Bash(spec-tools:*)")
    "an agent run gets exactly the named tools"
  let codexRun := agentInvocation codex "do it" [] "/copy"
  let sandboxAt := codexRun.args.findIdx? (· == "--sandbox")
  ensure (sandboxAt.bind (fun i => codexRun.args[i+1]?) == some "workspace-write") "codex writes in its copy only"

def testNoLiveCall : IO Unit := do
  let blocked ← (liveRunner { cmd := "true", args := #[], cwd := "." } [] 1000).toBaseIO
  ensure (match blocked with | .error _ => true | .ok _ => false) "a live call during the tests is refused"

def main : IO Unit := do
  liveCallsForbidden.set true
  testSchema
  testClaude
  testCodex
  testRefusals
  testAgentRuns
  testNoLiveCall
  IO.println "PASS: schema, adapters, refusals, agent runs, no live call"
