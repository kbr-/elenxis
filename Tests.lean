import SpecTools
import SpecTools.DraftHook

open SpecTools.DraftHook in
#guard additions "*** Begin Patch\n*** Add File: tasks/t/spec/Coverage.draft.json\n+[]\n*** End Patch" ==
  [⟨"tasks/t/spec/Coverage.draft.json", "[]\n"⟩]

open SpecTools.DraftHook in
#guard additions "*** Begin Patch\n*** Update File: tasks/t/spec/Coverage.draft.json\n+[]\n*** End Patch" == []

/-!
Tests of what meets the world: the live runner starting real processes. The pure core's properties
are theorems (`SpecTools.ModelProofs`).
-/

open SpecTools.Model

def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

def scratch (name : String) : IO System.FilePath := do
  let dir := (← IO.FS.createTempDir) / name
  IO.FS.createDirAll dir
  return dir

/-- A process that exits is read back whole: status, output, the files it wrote. -/
def testFinishedProcess : IO Unit := do
  let dir ← scratch "finished"
  let inv : Invocation := {
    cmd := "sh"
    args := #["-c", "cat in.txt > out.txt; echo said; exit 3"]
    cwd := dir
    files := [("in.txt", "written first")] }
  match ← liveRunner inv ["out.txt", "absent.txt"] 10000 with
  | none => throw <| IO.userError "a quick process was reported as an overrun"
  | some ran =>
    ensure (ran.exitCode == 3) s!"exit status {ran.exitCode}, expected 3"
    ensure (ran.stdout == "said\n") s!"stdout {ran.stdout.quote}"
    ensure (ran.readBack == [("out.txt", "written first")])
      "the invocation's file was written before the run and the run's file read back, an absent one skipped"

/-- A process past its limit is killed and reported as an overrun, without waiting for it. -/
def testOverrun : IO Unit := do
  let dir ← scratch "overrun"
  let start ← IO.monoMsNow
  let result ← liveRunner { cmd := "sleep", args := #["30"], cwd := dir } [] 300
  let elapsed := (← IO.monoMsNow) - start
  ensure result.isNone "an overrun gives no result"
  ensure (elapsed < 5000) s!"the overrun was waited out for {elapsed} ms"

def testFullCodexPrompt : IO Unit := do
  let dir ← scratch "codex-stdin"
  let prompt := "".pushn 'x' 150912
  let question : Question := { prompt, schema := Lean.Json.null, timeoutMs := 10000 }
  let call := invocation ⟨.codex, "test-model", "test", none⟩ question dir
  ensure (call.args.back? == some "-" && !(call.args.contains prompt))
    "Codex receives the stdin marker with no prompt in argv"
  match ← liveRunner { call with cmd := "cat", args := #[] } [] 10000 with
  | some result =>
    ensure (result.exitCode == 0 && result.stdout == prompt)
      "the full prompt arrives unchanged and stdin closes"
  | none => throw <| IO.userError "child did not receive EOF on stdin"
  IO.FS.removeDirAll dir

open Lean in
def testDraftReview : IO Unit := IO.FS.withTempDir fun dir => do
  let capture := dir / "captured.json"
  let calls := dir / "calls"
  let reply := dir / "reply.json"
  let config := dir / "backend.json"
  let prose := dir / "requirements.txt"
  let inventory := dir / "inventory.json"
  let complete := dir / "complete.json"
  let invalid := dir / "invalid.json"
  let source (id clause : String) :=
    Json.mkObj [("id", toJson id), ("clause", toJson clause)]
  let row (source evidence : Json) := Json.mkObj [("source", source), ("evidence", evidence)]
  let strength := source "strength" "Zero strength uses the left image for both eyes."
  let mono := source "mono" "Mono uses identical eyes."
  let comfort := source "comfort" "Check optical fusion in the glasses."
  let contract (statement : String) :=
    Json.mkObj [("contract", Json.mkObj [("name", toJson "Geometry.mono"),
      ("statement", toJson statement)])]
  let external := Json.mkObj [("externalCheck", Json.mkObj [
    ("reason", toJson "Device optics"), ("acceptance", toJson "Wear the glasses and verify fusion.")])]
  let shared := contract "∀ left, render 0 left = (left, left)"
  IO.FS.writeFile inventory (toJson [strength, mono, comfort]).compress
  IO.FS.writeFile complete (toJson [row strength shared, row mono shared, row comfort external]).compress
  IO.FS.writeFile invalid (toJson [
    row (source "strength" "changed") (contract " "), row strength shared, row mono shared]).compress
  IO.FS.writeFile prose "Zero strength renders mono. Validate fusion on the device."
  let script := "printf 'invoked\\n' >> \"$1\" && cp \"$4\" \"$2\" && cat \"$3\""
  IO.FS.writeFile config (Json.mkObj [
    ("adapter", toJson "command"), ("command", toJson "sh"), ("model", toJson "local/review"),
    ("dataGoesTo", toJson "local"), ("args", toJson [
      "-c", script, "review-adapter", calls.toString, capture.toString, reply.toString])]).compress
  let run (draft : System.FilePath) := IO.Process.output {
    cmd := "lake", args := #["exe", "spec-tools", "draft-review", "configured", "default",
      prose.toString, inventory.toString, draft.toString],
    env := #[("SPEC_TOOLS_BACKEND", some config.toString)] }
  IO.FS.writeFile reply "{\"gaps\":[]}"
  let refused ← run invalid
  ensure (refused.exitCode == 1) (refused.stdout ++ refused.stderr)
  for diagnostic in ["Missing draft row: comfort", "Duplicate draft key: strength",
      "Unknown or changed source clause: strength", "Empty draft contract: strength"] do
    ensure ((refused.stderr.splitOn diagnostic).length > 1) refused.stderr
  ensure (!(← calls.pathExists)) "incomplete draft started the command adapter"
  let accepted ← run complete
  ensure (accepted.exitCode == 0 &&
    (accepted.stdout.splitOn "0 gaps, 0 proposals refused").length > 1)
      (accepted.stdout ++ accepted.stderr)
  ensure ((← IO.FS.readFile calls) == "invoked\n") "complete draft did not invoke the adapter once"
  let request ← IO.ofExcept (Json.parse (← IO.FS.readFile capture))
  let prompt ← IO.ofExcept (request.getObjValAs? String "prompt")
  ensure ((prompt.splitOn "render 0 left").length == 2 &&
    (prompt.splitOn "Geometry.mono, statement 0").length == 3 &&
    (prompt.splitOn "verify fusion").length > 1) "review request lost draft evidence"
  IO.FS.writeFile reply "{\"gaps\":[{\"kind\":\"too weak\",\"row\":\"strength, comfort\",\"why\":\"wrong key\"}]}"
  let badReply ← run complete
  ensure (badReply.exitCode == 1 && (badReply.stderr.splitOn "schema").length > 1)
    (badReply.stdout ++ badReply.stderr)
  IO.println "PASS: draft review CLI (refusal before spawn, file transport, invalid response)"

/-- Run the audit over a Lean file written for the case, in this project's environment. -/
def auditCase (dir : System.FilePath) (name body : String) : IO (UInt32 × String) := do
  let file := dir / s!"{name}.lean"
  IO.FS.writeFile file ("import SpecTools.Audit\nimport SpecTools.GapsRun\nopen SpecTools.Ledger\n" ++ body)
  let out ← IO.Process.output { cmd := "lake", args := #["env", "lean", file.toString] }
  return (out.exitCode, out.stdout ++ out.stderr)

def has (text needle : String) : Bool := (text.splitOn needle).length > 1

def testToolchain : IO Unit := do
  for fixture in ["FiniteScope", "AdversarialAdmission"] do
    let result ← IO.Process.output {
      cmd := "lake", args := #["env", "lean", s!"integration/{fixture}.lean"] }
    ensure (result.exitCode == 0) (result.stdout ++ result.stderr)
  let rejection ← IO.Process.output {
    cmd := "lake", args := #["env", "lean", "integration/RejectedClaim.lean"] }
  let messages := rejection.stdout ++ rejection.stderr
  ensure (rejection.exitCode != 0 && has messages "no cheapest-wrong-model refutation supplied" &&
    !has messages "A refused declaration must not elaborate its body") messages
  IO.println "PASS: Lean toolchain (scope extraction, admission, refusal before body elaboration)"

def testApprovedContracts : IO Unit := do
  let dir ← scratch "approved-contracts"
  let baseline := "def Approved.mono (n : Nat) : Prop := n = 0\n"
  let check := "#eval SpecTools.Audit.checkApprovedContracts [⟨`Spec.mono, `Approved.mono⟩]\n"
  let (okCode, ok) ← auditCase dir "Match" (baseline ++
    "def Spec.mono (value : Nat) : Prop := value = 0\n" ++ check)
  ensure (okCode == 0 && has ok "1 specification declarations match") ok
  let (changedCode, changed) ← auditCase dir "Changed" (baseline ++
    "def Spec.mono (value : Nat) : Prop := value = 1\n" ++ check)
  ensure (changedCode != 0 && has changed "differs from approved contract") changed
  let (missingCode, missing) ← auditCase dir "Missing" (baseline ++ check)
  ensure (missingCode != 0 && has missing "missing requirement definition") missing
  let (selfCode, self) ← auditCase dir "Self" (baseline ++
    "#eval SpecTools.Audit.checkApprovedContracts [⟨`Approved.mono, `Approved.mono⟩]\n")
  ensure (selfCode != 0 && has self "baseline must be a separate declaration") self
  let draft := "open SpecTools.Gaps\n" ++
    "def reviewed : List DraftRow := [⟨⟨\"c1\", \"first\"⟩, .contract `Spec.mono \"first\"⟩, " ++
    "⟨⟨\"c2\", \"second\"⟩, .contract `Spec.stereo \"second\"⟩]\n"
  let (completeCode, complete) ← auditCase dir "CompleteBinding" (draft ++ baseline ++
    "def Spec.mono (n : Nat) : Prop := n = 0\n" ++
    "def Approved.stereo (n : Nat) : Prop := n = 1\n" ++
    "def Spec.stereo (n : Nat) : Prop := n = 1\n" ++
    "#eval checkDraftContracts reviewed [⟨`Spec.mono, `Approved.mono⟩, " ++
    "⟨`Spec.stereo, `Approved.stereo⟩]\n")
  ensure (completeCode == 0 && has complete "2 specification declarations match") complete
  let (bindingCode, binding) ← auditCase dir "Binding" (draft ++
    "#eval checkDraftContracts reviewed [⟨`Spec.mono, `Approved.mono⟩, " ++
    "⟨`Spec.mono, `Approved.mono⟩, ⟨`Spec.extra, `Approved.extra⟩]\n")
  ensure (bindingCode != 0 && has binding "Missing final contract binding: Spec.stereo" &&
    has binding "Duplicate final contract binding: Spec.mono" &&
    has binding "Unreviewed final contract binding: Spec.extra") binding
  IO.FS.removeDirAll dir
  IO.println "PASS: approved contracts (bodies, complete bindings, missing, duplicate, extra)"

/-- The audit reads the environment: missing names, unclaimed theorems, axioms, hypotheses without
witnesses, and the digests that skip unchanged rows. -/
def testAudit : IO Unit := do
  let dir ← IO.FS.createTempDir
  let digest := dir / "digests.txt"
  let base := "theorem plain : 1 + 1 = 2 := rfl\n\
    theorem guarded (n : Nat) (h : 0 < n) : n ≠ 0 := by omega\n\
    theorem witness : ∃ n : Nat, ∃ _h : 0 < n, True := ⟨1, by decide, trivial⟩\n"
  let rows (clause : String) := s!"#eval SpecTools.Audit.run [
    \{ id := \"r1\", clause := \"{clause}\", theorems := [``plain] },
    \{ id := \"r2\", clause := \"guarded\", theorems := [``guarded],
      evidence := [⟨``guarded, ``witness, .inhabited⟩] }]
    `AuditCase (digestFile := some \"{digest}\")\n"
  -- The cases reading no digests run beside the three that share the digest file, in order.
  let missing ← IO.asTask <| auditCase dir "missing" (base ++ "#eval SpecTools.Audit.run [
    { id := \"r1\", clause := \"c\", theorems := [`nonexistent, ``plain, ``guarded], witnesses := [``witness] }] `AuditCase\n")
  let unclaimedCase ← IO.asTask <| auditCase dir "unclaimed" (base ++ "#eval SpecTools.Audit.run [
    { id := \"r1\", clause := \"c\", theorems := [``plain] }] `AuditCase\n")
  let axiomCase ← IO.asTask <| auditCase dir "axiom" ("axiom myAxiom : 1 = 1\ntheorem leans : 1 = 1 := myAxiom\n\
    #eval SpecTools.Audit.run [{ id := \"r1\", clause := \"c\", theorems := [``leans] }] `AuditCase\n")
  let vacuous ← IO.asTask <| auditCase dir "vacuous" ("theorem guarded (n : Nat) (h : 0 < n) : n ≠ 0 := by omega\n\
    #eval SpecTools.Audit.run [{ id := \"r1\", clause := \"c\", theorems := [``guarded] }] `AuditCase\n")
  let (code, out) ← auditCase dir "pass" (base ++ rows "one plus one")
  ensure (code == 0 && has out "proved: r1" && has out "proved: r2" &&
      has out "2 rows: 2 proved, 0 conditional, 0 unknown nonvacuity, 0 inconsistent premises, 0 not stated (2 judged)")
    s!"a complete ledger passes, both rows proved:\n{out}"
  let (code, out) ← auditCase dir "again" (base ++ rows "one plus one")
  ensure (code == 0 && has out "unchanged: r1" && has out "(0 judged)")
    s!"a second run with nothing changed judges no row:\n{out}"
  let (code, out) ← auditCase dir "changed" (base ++ rows "one and one")
  ensure (code == 0 && has out "unchanged: r2" && has out "proved: r1" && has out "(1 judged)")
    s!"a changed clause re-judges that row alone:\n{out}"
  let (code, out) ← IO.ofExcept missing.get
  ensure (code != 0 && has out "names nonexistent, which is no theorem")
    s!"a row naming no theorem fails the audit:\n{out}"
  let (code, out) ← IO.ofExcept unclaimedCase.get
  ensure (code != 0 && has out "no row claims theorem guarded")
    s!"a written theorem no row claims fails the audit:\n{out}"
  let (code, out) ← IO.ofExcept axiomCase.get
  ensure (code == 0 && has out "conditional: r1" && has out "axioms: [myAxiom]")
    s!"an axiom outside the accepted three makes the row conditional:\n{out}"
  let (code, out) ← IO.ofExcept vacuous.get
  ensure (code == 0 && has out "unknown nonvacuity: r1")
    s!"hypotheses without a witness are reported:\n{out}"
  let (code, out) ← auditCase dir "typed" (base ++
    "theorem impossible (h : False) : (1 : Nat) = 2 := False.elim h\n\
    theorem irrelevant : True := True.intro\n\
    theorem disjoint : ¬ (∃ _h : False, True) := fun ⟨h, _⟩ => h\n\
    axiom assumption : ∃ n : Nat, ∃ _h : 0 < n, True\n\
    theorem unchecked : ∃ n : Nat, ∃ _h : 0 < n, True := assumption\n\
    #eval SpecTools.Audit.run [
    { id := \"ordinary\", clause := \"plain\", theorems := [``plain] },
    { id := \"legacy\", clause := \"impossible\", theorems := [``impossible],
      witnesses := [``irrelevant] },
    { id := \"wrong-type\", clause := \"impossible\", theorems := [``impossible],
      evidence := [⟨``impossible, ``irrelevant, .inhabited⟩] },
    { id := \"negative\", clause := \"impossible\", theorems := [``impossible],
      evidence := [⟨``impossible, ``disjoint, .inconsistent⟩] },
    { id := \"dependent\", clause := \"guarded\", theorems := [``guarded],
      evidence := [⟨``guarded, ``witness, .inhabited⟩] },
    { id := \"no-binding\", clause := \"guarded\", theorems := [``guarded] },
    { id := \"untrusted\", clause := \"guarded\", theorems := [``guarded],
      evidence := [⟨``guarded, ``unchecked, .inhabited⟩] },
    { id := \"two-theorems\", clause := \"two domains\", theorems := [``guarded, ``impossible],
      evidence := [⟨``guarded, ``witness, .inhabited⟩] }] `AuditCase\n")
  ensure (code == 0 && has out "unknown nonvacuity: legacy:" &&
    has out "unknown nonvacuity: wrong-type:" && has out "inconsistent premises: negative:" &&
    has out "proved: dependent:" && has out "unknown nonvacuity: no-binding:" &&
    has out "unknown nonvacuity: untrusted:" && has out "unknown nonvacuity: two-theorems:")
    s!"the real Lean audit checks exact, row-local and trusted evidence:\n{out}"

def testRequirementAudits : IO Unit := IO.FS.withTempDir fun dir => do
  let cases : List (String × String × Bool × List String) := [
    ("Requirement", "def obligation (n : Nat) : Prop := n + 0 = n\n\
      #eval SpecTools.Audit.run [{ id := \"r\", clause := \"identity\", theorems := [``obligation] }] \
      `Requirement (requirements := true)\n", true, ["specified (unproved): r", "n + 0 = n"]),
    ("ProofOnly", "def obligation : Prop := True\n\
      #eval SpecTools.Audit.run [{ id := \"r\", clause := \"identity\", theorems := [``obligation] }] \
      `ProofOnly\n", false, ["which is no theorem"]),
    ("WrongType", "def notAProperty : Nat := 4\n\
      #eval SpecTools.Audit.run [{ id := \"r\", clause := \"identity\", theorems := [``notAProperty] }] \
      `WrongType (requirements := true)\n", false, ["not a proposition"]),
    ("MissingRequirement", "#eval SpecTools.Audit.run \
      [{ id := \"r\", clause := \"identity\", theorems := [`absent] }] \
      `MissingRequirement (requirements := true)\n", false, ["names absent"]),
    ("EmptyRequirements", "#eval SpecTools.Model.liveCallsForbidden.set true\n\
      #eval SpecTools.Gaps.run [] \"\" \
      { harness := .codex, model := \"must-not-run\", dataGoesTo := \"forbidden\" } (requirements := true)\n",
      false, ["specification ledger is empty"]),
    ("UntrustedRequirement", "axiom untrusted : Prop\ndef obligation : Prop := untrusted\n\
      #eval SpecTools.Audit.run [{ id := \"r\", clause := \"identity\", theorems := [``obligation] }] \
      `UntrustedRequirement (requirements := true)\n", false, ["conditional"]),
    ("OpaqueRequirement", "opaque obligation : Prop := True\n\
      #eval SpecTools.Audit.run [{ id := \"r\", clause := \"identity\", theorems := [``obligation] }] \
      `OpaqueRequirement (requirements := true)\n", false, ["safe requirement body"]),
    ("UnsafeRequirement", "unsafe def obligation : Prop := True\n\
      #eval SpecTools.Audit.run [{ id := \"r\", clause := \"identity\", theorems := [``obligation] }] \
      `UnsafeRequirement (requirements := true)\n", false, ["safe requirement body"]),
    ("MultipleInvalidRequirements", "def notAProperty : Nat := 4\n\
      #eval SpecTools.Audit.run [{ id := \"r\", clause := \"identity\", \
      theorems := [`absent, ``notAProperty] }] `MultipleInvalidRequirements (requirements := true)\n",
      false, ["names absent", "notAProperty is not a proposition"]),
    ("UnprovedWitness", "theorem guarded (h : False) : False := h\ndef witness : Prop := False\n\
      #eval SpecTools.Audit.run [{ id := \"r\", clause := \"identity\", \
      theorems := [``guarded], witnesses := [``witness] }] `UnprovedWitness (requirements := true)\n",
      false, ["witness witness is not proved"])]
  let running ← cases.mapM fun (name, body, passes, messages) => do
    let task ← IO.asTask (auditCase dir name body)
    return (name, passes, messages, task)
  for (name, passes, messages, task) in running do
    let (code, output) ← IO.ofExcept task.get
    ensure ((code == 0) == passes && messages.all (has output)) s!"{name}: {output}"
  IO.println "PASS: requirement audit (unproved, proof-only, wrong type, missing, empty, untrusted, opaque, unsafe, all findings, witness)"

/-- Real process boundary: literal prompts survive the request file, and malformed/schema-breaking
responses and nonzero exits cannot become successful answers. No model or provider is contacted. -/
def testCommandAdapter : IO Unit := do
  let dir ← IO.FS.createTempDir
  let backend : Backend := { harness := .command "cat" [], model := "local/model", dataGoesTo := "local" }
  let schema := Lean.Json.mkObj [("type", "object")]
  for prompt in ["", "Zażółć\n\"quotes\" $(literal) \\ path"] do
    let question : Question := { prompt, schema, timeoutMs := 10000 }
    match ← ask liveRunner [backend] backend question dir with
    | .error failure => throw (IO.userError failure.describe)
    | .ok outcome =>
      ensure ((outcome.answer.getObjValAs? String "prompt").toOption == some prompt) "prompt changed in transport"
      ensure ((outcome.answer.getObjValAs? String "model").toOption == some "local/model") "configured model lost"
      ensure ((outcome.answer.getObjValAs? String "mode").toOption == some "question") "wrong adapter mode"
      ensure (outcome.answer.getObjVal? "effort").toOption.isNone "an effort sent though none was configured"
    let effortful := { backend with effort := some "medium" }
    match ← ask liveRunner [effortful] effortful question dir with
    | .error failure => throw (IO.userError failure.describe)
    | .ok outcome =>
      ensure ((outcome.answer.getObjValAs? String "effort").toOption == some "medium")
        "configured effort lost in transport"
    let invalid : Question := { question with schema := Lean.Json.mkObj [("type", "string")] }
    let rejected ← ask liveRunner [backend] backend invalid dir
    ensure rejected.toOption.isNone "schema-breaking process output accepted"
  for (executable, arguments) in [("printf", ["not json"]), ("false", [])] do
    let broken := { backend with harness := .command executable arguments }
    ensure (← ask liveRunner [broken] broken { prompt := "", schema, timeoutMs := 10000 } dir).toOption.isNone
      "failed adapter accepted"
  for adapter in ["codex", "claude-code", "command"] do
    let json := Lean.Json.mkObj [("adapter", Lean.toJson adapter), ("model", Lean.toJson "chosen"),
      ("dataGoesTo", Lean.toJson "chosen destination"), ("command", Lean.toJson "cat"),
      ("args", Lean.toJson ([] : List String))]
    let parsed ← IO.ofExcept (backendOfJson json)
    ensure (parsed.model == "chosen" && parsed.dataGoesTo == "chosen destination") "configuration changed"
    ensure (parsed.effort == none) "an effort chosen though the configuration names none"
    let withEffort := json.setObjVal! "effort" (Lean.toJson "medium")
    ensure ((← IO.ofExcept (backendOfJson withEffort)).effort == some "medium") "configured effort lost"
    ensure ((backendOfJson (json.setObjVal! "effort" (Lean.toJson " "))).toOption.isNone)
      "empty effort accepted"
    ensure ((backendOfJson (Lean.Json.mkObj [("adapter", Lean.toJson adapter)])).toOption.isNone)
      "incomplete configuration accepted"
  let config := dir / "backend.json"
  IO.FS.writeFile config "{\"adapter\":\"command\",\"command\":\"cat\",\"args\":[],\"model\":\"default\",\"dataGoesTo\":\"local\",\"effort\":\"medium\"}"
  let source := dir / "Select.lean"
  IO.FS.writeFile source "import SpecTools.BackendConfig\n#eval show IO Unit from do\n  let b ← SpecTools.Model.selectedBackend \"configured\" \"override\"\n  if b.model != \"override\" then throw (IO.userError \"model override lost\")\n  if b.effort != some \"medium\" then throw (IO.userError \"configured effort lost on a model override\")\n  match b.harness with\n  | .command \"cat\" [] => pure ()\n  | _ => throw (IO.userError \"configured adapter lost\")\n"
  let selected ← IO.Process.output {
    cmd := "lake"
    args := #["env", "lean", source.toString]
    env := #[("SPEC_TOOLS_BACKEND", some config.toString)] }
  ensure (selected.exitCode == 0) s!"configured selection: {selected.stdout}{selected.stderr}"
  for model in ["", "  "] do
    let refused ← (selectedBackend "configured" model).toBaseIO
    ensure (match refused with | .error _ => true | .ok _ => false)
      "empty configured model override accepted"
  IO.FS.removeDirAll dir
  IO.println "PASS: configurable command adapter (transport, schema, malformed output, exit, configuration)"

open SpecTools.Usage in
/-- A call's usage, read from what each harness really printed (the probes saved in
`research/results/lean-specification-tools/` of the workspace, copied here), from a command adapter's
`usage.json`, and printed by `gaps`; and the trace `SPEC_TOOLS_TRACE` asks for. -/
def testUsage : IO Unit := do
  -- Claude Code's report for "Answer with the single word: ok" under the adapter's flags.
  let claude := "{\"total_cost_usd\":0.018001800000000002,\"num_turns\":1,\"duration_api_ms\":4620,\"usage\":{\"input_tokens\":2,\"cache_creation_input_tokens\":2223,\"cache_read_input_tokens\":649,\"output_tokens\":4}}"
  let u := ofClaudeReport (← IO.ofExcept (Lean.Json.parse claude)) 5196
  ensure (u.input == .of (some 2) && u.cacheWrite == .of (some 2223) && u.cacheRead == .of (some 649) &&
    u.output == .of (some 4) && u.turns == .of (some 1) && u.listPriceNano == .of (some 18001800))
    s!"Claude Code's report read wrong: {repr u}"
  -- Codex's events for the same question, `gpt-6.1-sol`.
  let codex := "{\"type\":\"thread.started\",\"thread_id\":\"t\"}\n{\"type\":\"turn.started\"}\n{\"type\":\"item.completed\",\"item\":{\"id\":\"item_2\",\"type\":\"agent_message\",\"text\":\"ok\"}}\n{\"type\":\"turn.completed\",\"usage\":{\"input_tokens\":35450,\"cached_input_tokens\":0,\"cache_write_input_tokens\":0,\"output_tokens\":5,\"reasoning_output_tokens\":0}}\n"
  let c := ofCodexEvents codex 11000
  ensure (c.input == .of (some 35450) && c.cacheRead == .of (some 0) && c.cacheWrite == .of (some 0) &&
    c.output == .of (some 5) && c.listPriceNano == .of none) s!"Codex's events read wrong: {repr c}"
  ensure (ofCodexEvents "not json\n" 1 == unreported 1) "Codex events without a turn's end aren't unreported"
  -- A command adapter with and without `usage.json`.
  let dir ← IO.FS.createTempDir
  let schema := Lean.Json.mkObj [("type", "object")]
  let script := "printf '{\"input\":7,\"output\":3,\"listPriceUsd\":0.5}' > usage.json; cat \"$1\""
  let reporting : Backend :=
    { harness := Harness.command "sh" ["-c", script, "adapter"], model := "local/model", dataGoesTo := "local" }
  let (r, used) ← askWithUsage liveRunner [reporting] reporting { prompt := "p", schema, timeoutMs := 10000 } dir
  ensure r.toOption.isSome "the reporting adapter's answer was refused"
  ensure (used.input == .of (some 7) && used.output == .of (some 3) && used.cacheWrite == .of none &&
    used.listPriceNano == .of (some 500000000)) s!"usage.json read wrong: {repr used}"
  let silent : Backend := { harness := .command "cat" [], model := "local/model", dataGoesTo := "local" }
  let dir2 ← IO.FS.createTempDir
  let (_, quiet) ← askWithUsage liveRunner [silent] silent { prompt := "p", schema, timeoutMs := 10000 } dir2
  ensure (quiet.input == .of none && quiet.output == .of none && quiet.calls == 1)
    s!"an adapter writing no usage.json reported counts: {repr quiet}"
  ensure (has (line quiet "x") "input unknown (1 unreported)") s!"an unknown count printed as known: {line quiet "x"}"
  -- `gaps` prints the usage line, records it where SPEC_TOOLS_USAGE says, and traces when asked.
  let gapsFile (name script : String) : IO System.FilePath := do
    let file := dir / s!"{name}.lean"
    IO.FS.writeFile file ("import SpecTools.GapsRun\n#eval SpecTools.Gaps.run [] \"prose\" " ++
      "{ harness := .command \"sh\" [\"-c\", \"" ++ script ++ "\", \"adapter\"], model := \"m\", " ++
      "dataGoesTo := \"local\" }\n")
    return file
  let answering := "touch " ++ (dir / "ran").toString ++ "; printf '{\\\"input\\\":7,\\\"output\\\":3}' > usage.json; printf '{\\\"gaps\\\":[]}'"
  let file ← gapsFile "GapsUsage" answering
  let usageRecord := dir / "usage.jsonl"
  let traceDir := dir / "trace"
  let out ← IO.Process.output {
    cmd := "lake"
    args := #["env", "lean", file.toString]
    env := #[("SPEC_TOOLS_USAGE", some usageRecord.toString), ("SPEC_TOOLS_TRACE", some traceDir.toString)] }
  let text := out.stdout ++ out.stderr
  ensure (out.exitCode == 0 && has text "usage: 1 calls; tokens input 7" && has text "output 3")
    s!"gaps printed no usage line: {text}"
  ensure ((← readRecorded usageRecord).input == .of (some 7)) "gaps recorded no usage in SPEC_TOOLS_USAGE"
  let traces := (← traceDir.readDir).map (·.path)
  ensure (traces.size == 1) s!"one trace file expected, found {traces.size}"
  let traced ← IO.FS.readFile traces[0]!
  ensure (((traced.splitOn "\n").filter (· ≠ "")).length == 1 && has traced "\"prompt\"" &&
    has traced "\"usage\"" && has traced "\"answer\"") s!"the trace line lacks its parts: {traced}"
  -- A trace directory that can't be written fails before the adapter runs.
  IO.FS.removeFile (dir / "ran")
  let blocked ← IO.Process.output {
    cmd := "lake"
    args := #["env", "lean", file.toString]
    env := #[("SPEC_TOOLS_TRACE", some "/proc/spec-tools-trace")] }
  ensure (!(← (dir / "ran").pathExists)) "the adapter ran though the trace couldn't be written"
  ensure (has (blocked.stdout ++ blocked.stderr) "error") "an unwritable trace gave no error"
  -- Without SPEC_TOOLS_TRACE nothing is traced: the trace directory keeps its one file, one line.
  let plain ← IO.Process.output { cmd := "lake", args := #["env", "lean", file.toString] }
  ensure (plain.exitCode == 0 && (← (dir / "ran").pathExists)) "the untraced run didn't run"
  ensure ((← traceDir.readDir).size == 1 && (← IO.FS.readFile traces[0]!) == traced)
    "a trace written though none was asked for"
  let parallelFile := dir / "ParallelGaps.lean"
  IO.FS.writeFile parallelFile ("import SpecTools.GapsRun\n" ++
    "#eval SpecTools.Gaps.run [] (String.ofList (List.replicate 100003 'a')) " ++
    "{ harness := .command \"sh\" [\"-c\", \"printf '{\\\"gaps\\\":[]}'\"], model := \"m\", " ++
    "dataGoesTo := \"local\" }\n")
  let parallelTrace := dir / "parallel-trace"
  let parallel ← IO.Process.output {
    cmd := "lake", args := #["env", "lean", parallelFile.toString]
    env := #[("SPEC_TOOLS_TRACE", some parallelTrace.toString),
      ("SPEC_TOOLS_GAP_READINGS", some "8")] }
  ensure (parallel.exitCode == 0) s!"parallel gaps failed: {parallel.stdout}{parallel.stderr}"
  let #[traceFile] ← parallelTrace.readDir |
    throw (IO.userError "parallel readings did not share one process trace")
  let lines := ((← IO.FS.readFile traceFile.path).splitOn "\n").filter (!·.isEmpty)
  let records ← IO.ofExcept (lines.mapM Lean.Json.parse)
  let prompts ← IO.ofExcept (records.mapM (·.getObjValAs? String "prompt"))
  let expectedPrompt := String.ofList (List.replicate 100003 'a')
  ensure (prompts.length == 8 && prompts.all (fun prompt => has prompt expectedPrompt))
    "parallel gap traces lost or mixed records"
  IO.FS.removeDirAll dir
  IO.FS.removeDirAll dir2
  IO.println "PASS: usage (Claude Code, Codex, adapter file, unreported, gaps line, record, trace)"

open SpecTools.Prose SpecTools.Generated in
/-- The person-prose writer's loop with a scripted model: a kept document, a rewrite, a variant left
out, a failed call. Each extraction answer is taken from a queue, each writer call from another. -/
def testProse : IO Unit := do
  let rules : List Rule := [⟨0, "deliver", ["requests", "loans"], 15, none⟩,
    ⟨1, "pay", ["fines"], 3, some "staff"⟩]
  let shown := [(0, Presentation.exampleOnly), (1, Presentation.definedTerm)]
  let answer (r : Rule) := Lean.Json.mkObj [("kind", Lean.Json.str r.kind),
    ("measures", Lean.Json.arr (r.measures.reverse.map Lean.Json.str).toArray),
    ("bound", Lean.toJson r.bound), ("exempt", Lean.Json.str (r.flag.getD "none"))]
  let exact := (Lean.Json.mkObj [("rules", Lean.Json.arr (rules.map answer).toArray)]).compress
  let wrong := (Lean.Json.mkObj [("rules", Lean.Json.arr #[answer rules[0]!,
    answer { rules[1]! with flag := none }])]).compress
  let run (attempts : List (Option String × List String)) : IO (Writing × Nat × String) :=
    IO.FS.withTempDir fun dir => do
      let input := dir / "responses"
      let workspace := dir / "workspace"
      let calls := dir / "calls"
      for ((writer, readers), index) in attempts.zipIdx do
        let replies := input / s!"writing{index + 1}"
        IO.FS.createDirAll replies
        if let some reply := writer then
          IO.FS.writeFile (replies / "write") reply
        for (reply, reader) in readers.zipIdx do
          IO.FS.writeFile (replies / s!"extract{reader + 1}") reply
      let script := "stage=${PWD##*/}; parent=${PWD%/*}; " ++
        "printf '%s\\n' \"$stage\" >> \"$2\" && cat \"$1/${parent##*/}/$stage\""
      let backend : Backend :=
        ⟨.command "sh" ["-c", script, "prose-adapter", input.toString, calls.toString],
          "local/prose", "local", none⟩
      let result ← writeFaithful liveRunner [backend] backend rules shown workspace 10000
      let request ← IO.ofExcept (Lean.Json.parse
        (← IO.FS.readFile (workspace / "writing1" / "write" / "request.json")))
      let prompt ← IO.ofExcept (request.getObjValAs? String "prompt")
      let launched ← IO.FS.lines calls
      return (result, launched.size, prompt)
  let doc := some "{\"document\":\"Our desk rules.\"}"
  let (kept, calls, deliveredPrompt) ← run [(doc, [exact, exact])]
  ensure (kept.document == some "Our desk rules." && kept.writings == 1 && kept.discarded.isEmpty &&
    calls == 3 && kept.usage.calls == 3) s!"equal extractions didn't keep the document: {kept.discarded}"
  ensure ((deliveredPrompt.splitOn "worked example").length > 1 && (deliveredPrompt.splitOn "group name").length > 1)
    "the writer's prompt lacks the rules' presentations"
  let (rewritten, _, _) ← run [(doc, [wrong, exact]), (doc, [exact, exact])]
  ensure (rewritten.document.isSome && rewritten.writings == 2 && rewritten.discarded.length == 1 &&
    (rewritten.discarded[0]!.splitOn "exempt staff").length > 1)
    s!"one differing rule didn't rewrite the document: {rewritten.discarded}"
  let (leftOut, calls, _) ← run (List.replicate 3 (doc, [wrong, wrong]))
  ensure (leftOut.document.isNone && leftOut.writings == 3 && leftOut.discarded.length == 3 && calls == 9)
    s!"three failed writings didn't leave the variant out: {leftOut.discarded}"
  let (afterFailure, calls, _) ← run [(none, []), (doc, [exact, exact])]
  ensure (afterFailure.document.isSome && afterFailure.writings == 2 && calls == 4 &&
    (afterFailure.discarded[0]!.splitOn "writing 1").length > 1)
    s!"a failed writer call didn't count as a failed writing: {afterFailure.discarded}"
  IO.println "PASS: person prose adapter (kept, rewritten, left out, failed call)"

/-- The owners' loop with a scripted runner (Path step 14.4 and 14.5): five review rounds each
followed by a revision, a round whose review finds nothing among them, then one more review and
the fidelity check; one clear rule read wrong, or a flaw read as stated, sends the text back; four
failed checks start again, and two failed starts leave no text. -/
def testOwners : IO Unit := do
  let v := SpecTools.Generated.Vocab.salon
  let rules : List SpecTools.Generated.Rule := [⟨0, "perm", ["no_shows"], 3, some "regular"⟩,
    ⟨1, "colour", ["complaints"], 5, none⟩]
  let flaws : List SpecTools.Owners.Imperfection := [⟨0, .loose⟩]
  let read (kind : String) (m : String) (bound : Nat) (mark exempt : String) :=
    Lean.Json.mkObj [("kind", Lean.Json.str kind), ("measures", Lean.Json.arr #[Lean.Json.str m]),
      ("bound", Lean.toJson bound), ("mark", Lean.Json.str mark), ("exempt", Lean.Json.str exempt)]
  let reads (rs : List Lean.Json) := (Lean.Json.mkObj [("rules", Lean.Json.arr rs.toArray)]).compress
  let exact := reads [read "perm" "no_shows" 4 "loose" "regular", read "colour" "complaints" 5 "stated" "none"]
  let ruleWrong := reads [read "perm" "no_shows" 4 "loose" "regular", read "colour" "complaints" 6 "stated" "none"]
  let flawStated := reads [read "perm" "no_shows" 3 "stated" "regular", read "colour" "complaints" 5 "stated" "none"]
  let doc := (Lean.Json.mkObj [("document", Lean.Json.str "We do hair.")]).compress
  let tells (n : Nat) := (Lean.Json.mkObj [("tells", Lean.toJson ((List.range n).map fun k =>
    s!"tell {k}")), ("could_be_real", Lean.toJson (n == 2))]).compress
  let backend : Backend := ⟨.codex, "test-model", "test", none⟩
  let run (readings : List String) (judges : List String := []) (rounds : Nat := 3)
      (startingText : Option String := none)
      (reviewPrefix : Option SpecTools.Owners.ReviewPrefix := none)
      : IO (SpecTools.Owners.Writing × Nat × List String) := do
    let r ← IO.mkRef readings
    let js ← IO.mkRef judges
    let reviews ← IO.mkRef (0 : Nat)
    let calls ← IO.mkRef (0 : Nat)
    let reviewerPrompts ← IO.mkRef ([] : List String)
    let runner : Runner := fun invocation _ _ => do
      calls.modify (· + 1)
      let prompt := invocation.input.getD ""
      let has (t : String) := (prompt.splitOn t).length > 1
      let reply ← if has "# Text to judge" then do
          reviewerPrompts.modify (· ++ [prompt])
          -- The third review of each start finds nothing.
          let n ← reviews.modifyGet fun n => (n, n + 1)
          pure (some (tells (if n % 6 == 2 then 0 else 2)))
        else if has "# Text\n" then r.modifyGet fun l => (l.head?, l.tail)
        else if has "If you had to bet" then do
          -- The development judge: the scripted probabilities first, then 92.
          let p ← js.modifyGet fun l => ((l.head?.bind String.toNat?).getD 92, l.tail)
          pure (some (Lean.Json.mkObj [("human_probability", Lean.toJson p),
            ("why", Lean.Json.arr #["typos"])]).compress)
        else if has "`human_probability`" then pure (some (Lean.Json.mkObj [
          ("human_probability", Lean.toJson (92 : Nat)), ("why", Lean.Json.arr #["fragments"])]).compress)
        else if has "# The message" then do
          pure (some (Lean.Json.mkObj [("verdict", "owner"),
            ("confidence", Lean.toJson (80 : Nat)), ("reasons", Lean.Json.arr #["typos"])]).compress)
        else pure (some doc)
      return reply.map fun a =>
        { exitCode := 0, stdout := "", stderr := "", readBack := [("answer.json", a)], millis := 1 }
    let dir ← IO.FS.createTempDir
    let w ← SpecTools.Owners.writeOwner runner [backend] backend v .prose rules flaws "" dir 10000
      (judgeRounds := rounds) (startingText := startingText) (reviewPrefix := reviewPrefix)
    IO.FS.removeDirAll dir
    return (w, ← calls.get, ← reviewerPrompts.get)
  let (kept, calls, rprompts) ← run [exact, exact]
  ensure (kept.text == some "We do hair." && calls == 20 && kept.steps.length == 6 &&
    (kept.steps.filter (·.notes.isEmpty)).length == 2 && kept.faults == [[]] &&
    kept.lastTells.length == 2 && kept.lastVerdict == some true && kept.usage.calls == 20 &&
    kept.testSamples == [92, 92, 92] && kept.devJudge == some 92 &&
    SpecTools.Owners.meanOf [90, 88, 88] == some 88 && SpecTools.Owners.meanOf [90, 92, 90] == some 90 &&
    SpecTools.Owners.meanOf [] == none &&
    kept.heldOut == some ("owner", 80) && kept.heldOutReasons == ["typos"] &&
    kept.testJudge == some 92 && kept.testJudgeWhy == ["fragments"] &&
    SpecTools.Owners.passesBar kept.testJudge && !SpecTools.Owners.passesBar (some 89) &&
    SpecTools.Owners.passesBar (some 90) && !SpecTools.Owners.passesBar none &&
    SpecTools.Owners.passesJudge .prose kept.heldOut &&
    !SpecTools.Owners.passesJudge .conversation kept.heldOut &&
    !SpecTools.Owners.passesJudge .prose (some ("ai", 70)) &&
    !SpecTools.Owners.passesJudge .prose none)
    s!"five rounds and a faithful reading didn't keep the text: {calls} calls, {kept.steps.length} steps"
  ensure (rprompts.length == 6 && rprompts.all fun p =>
      (p.splitOn "no shows").length == 1 && (p.splitOn "# What you want").length == 1)
    "a reviewer's prompt holds the rules"
  let (judgedBack, calls, _) ← run [exact, exact] ["70", "89"]
  let judgeRevisions := judgedBack.steps.filter fun s => (s.what.splitOn "revised after judge").length > 1
  ensure (judgedBack.text.isSome && judgeRevisions.length == 2 &&
    judgeRevisions.all (·.notes == ["typos"]) &&
    calls == 24) s!"two scores under the bar didn't bring two revisions against the judge's reasons: \
      {judgeRevisions.length} revisions, {calls} calls"
  let (judgeCapped, _, _) ← run [exact, exact] ["50", "50", "50", "50"]
  let (judgeAtBar, _, _) ← run [exact, exact] ["90"]
  ensure ((judgeAtBar.steps.filter fun s => (s.what.splitOn "revised after judge").length > 1).isEmpty)
    "a score at the bar brought a revision"
  ensure ((judgeCapped.steps.filter fun s => (s.what.splitOn "revised after judge").length > 1).length ==
    3) "the judge's revisions didn't stop at the rounds given"
  let (noRounds, calls, _) ← run [exact, exact] ["50", "50"] SpecTools.Owners.judgeRounds
  ensure (SpecTools.Owners.judgeRounds == 0 && calls == 19 &&
    (noRounds.steps.filter fun s => (s.what.splitOn "revised after judge").length > 1).isEmpty)
    s!"the default revised against the development judge: {calls} calls"
  let (sentBack, calls, _) ← run [ruleWrong, exact, exact, exact]
  ensure (sentBack.text.isSome && sentBack.faults.length == 2 && sentBack.steps.length == 7 &&
    calls == 23) s!"a clear rule read wrong didn't send the text back: {sentBack.faults}"
  let (flawBack, _, _) ← run [flawStated, exact, exact, exact]
  let firstFault := (flawBack.faults.headD []).headD ""
  ensure (flawBack.text.isSome && flawBack.faults.length == 2 &&
    (firstFault.splitOn "(stated)").length > 1)
    s!"a flaw read as stated didn't send the text back: {flawBack.faults}"
  let (failed, calls, _) ← run (List.replicate 16 ruleWrong)
  ensure (failed.text.isNone && failed.faults.length == 8 && calls == 46 &&
    (failed.steps.filter fun s => s.what.startsWith "start 2").length > 0)
    s!"four failed checks didn't start again, or two failed starts kept a text: {calls} calls"
  let draft := "The supplied transcript has its own opening."
  let (imported, calls, reviewerPrompts) ← run [exact, exact] [] 0 (some draft)
  ensure (imported.text.isSome && calls == 18 && imported.steps.length == 6 &&
    (imported.steps.head?.map (·.text)) == some draft &&
    ((reviewerPrompts.headD "").splitOn draft).length == 2)
    "a supplied draft did not go straight into the five review rounds"
  let (importFailed, calls, _) ← run (List.replicate 16 ruleWrong) [] 0 (some draft)
  ensure (importFailed.text.isNone && calls == 21 &&
    importFailed.faults.length == SpecTools.Owners.fidelityRounds + 1 &&
    !(importFailed.steps.any fun s => s.what.startsWith "start 2"))
    s!"a supplied draft that exhausted fidelity made {calls} calls; steps: {importFailed.steps.map (·.what)}"
  let row (step text : String) := (Lean.Json.mkObj [("step", Lean.toJson step),
    ("text", Lean.toJson text), ("notes", Lean.Json.arr #[])]).compress
  let lastRevision := "The fourth completed review changed this line."
  let initial := row "start 1: supplied draft" draft
  let revisions := (List.range 4).map fun i =>
    row s!"start 1: revised after review {i + 1}" lastRevision
  let failureRow := row "start 1: review 5 failed" lastRevision
  let journal := "\n".intercalate (initial :: revisions ++ [failureRow])
  let saved ← IO.ofExcept (SpecTools.Owners.decodeReviewPrefix draft journal { calls := 9 })
  let (resumed, calls, prompts) ← run [exact, exact] [] 0 (some draft) (some saved)
  ensure (resumed.text.isSome && calls == 10 && resumed.usage.calls == 19 &&
    resumed.steps.length == 6 && ((prompts.headD "").splitOn lastRevision).length == 2)
    "resuming a four-round prefix did not start at review five"
  let reordered := "\n".intercalate (initial :: revisions.reverse ++ [failureRow])
  ensure (!(SpecTools.Owners.decodeReviewPrefix "Different draft" journal {}).isOk &&
    !(SpecTools.Owners.decodeReviewPrefix draft reordered {}).isOk)
    "a changed draft or out-of-order review journal was accepted"
  IO.println "PASS: owners (five rounds, kept, sent back for a rule and for a flaw, started again, failed)"

/-- A failing preparation supplies its diagnostic and never runs the checks that follow it. -/
def testPrepareReports : IO Unit := do
  let dir ← scratch "prepare-reports"
  let executable := dir / "check-fixture"
  let journal := dir / "attempts"
  let failure := dir / "failure"
  try
    IO.FS.writeFile executable "#!/bin/sh\n\
      printf '%s\\n' \"$2\" >> attempts\n\
      printf 'report for %s\\n' \"$2\"\n\
      if test -f failure && test \"$2\" = \"$(cat failure)\"; then\n\
        printf 'diagnostic for %s\\n' \"$2\" >&2\n\
        exit 42\n\
      fi\n"
    let mode ← IO.Process.output { cmd := "chmod", args := #["+x", executable.toString] }
    ensure (mode.exitCode == 0) mode.stderr
    let modes : List (SpecTools.SyntheticRun.Arm × List String × Nat) :=
      [(.tools, ["audit", "tests", "gaps"], 1),
       (.confirmed, ["audit", "tests", "gaps", "clauses"], 3)]
    for (arm, expected, readings) in modes do
      let run := (SpecTools.SyntheticRun.prepareReports executable.toString dir
        arm.preparedChecks readings).run
      IO.FS.writeFile failure ""
      IO.FS.writeFile journal ""
      let valid ← run
      ensure (match valid with
        | .ok report => expected.all fun name =>
            ((arm.prompt "check" report).splitOn s!"report for {name}").length == 2
        | .error _ => false) s!"the {arm.name} prompt did not contain the successful reports"
      ensure ((← IO.FS.readFile journal) == "\n".intercalate expected ++ "\n")
        "wrong preparation order"
      for (name, index) in expected.zipIdx do
        IO.FS.writeFile failure name
        IO.FS.writeFile journal ""
        let failed ← run
        ensure (match failed with
          | .error e => e == s!"preparing {name}: exit 42\nreport for {name}\ndiagnostic for {name}\n"
          | .ok _ => false) s!"the failed {name} preparation did not preserve its output"
        ensure ((← IO.FS.readFile journal) == "\n".intercalate (expected.take (index + 1)) ++ "\n")
          s!"preparation continued past {name}"
    let absent ← (SpecTools.SyntheticRun.prepareReports (dir / "missing").toString dir).run
    ensure (match absent with
      | .error error => error.startsWith "preparing audit"
      | .ok _ => false) "a failed process start did not identify the attempted check"
  finally
    IO.FS.removeDirAll dir.parent.get!
  IO.println "PASS: tool preparation stops on a failed check"

/-- Run `act` as a task, printing its wall time when it ends, so a slow group is named. -/
def timed (name : String) (act : IO Unit) : IO (Task (Except IO.Error Unit)) := IO.asTask do
  let start ← IO.monoMsNow
  act
  IO.println s!"time: {name} {(← IO.monoMsNow) - start} ms"

def main : IO Unit := do
  -- The groups share no state (each makes its own directories, its scripted runners and its
  -- processes' environments its own), so they run at once; the live runner's prohibition below is
  -- the one global, set after all of them end.
  let groups ← [("command adapter", testCommandAdapter), ("usage", testUsage), ("prose", testProse),
      ("owners", testOwners), ("tool preparation", testPrepareReports),
      ("requirement audits", testRequirementAudits), ("finished process", testFinishedProcess),
      ("overrun", testOverrun), ("full codex prompt", testFullCodexPrompt),
      ("draft review", testDraftReview), ("approved contracts", testApprovedContracts),
      ("audit", testAudit), ("Lean toolchain", testToolchain)].mapM fun (name, action) => timed name action
  let outcomes := groups.map (·.get)
  for outcome in outcomes do IO.ofExcept outcome
  IO.println "PASS: audit (pass, unchanged, changed, missing, unclaimed, axiom, vacuous)"
  liveCallsForbidden.set true
  let blocked ← (liveRunner { cmd := "true", args := #[], cwd := "." } [] 1000).toBaseIO
  ensure (match blocked with | .error _ => true | .ok _ => false)
    "a live call while forbidden is refused"
  IO.println "PASS: live runner (exit, output, files, overrun, forbidden)"
