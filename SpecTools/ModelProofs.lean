import SpecTools.Model

/-!
The model interface's guarantees, proved over its pure core (`plan`, `invocation`, `finish`) and the
one step of `ask` that joins them to a runner.
-/

namespace SpecTools.Model
open Lean

/-- A backend the project doesn't allow is refused. -/
theorem plan_refuses_disallowed {allowed : List Backend} {backend : Backend} (q : Question)
    (s : System.FilePath) (h : routeAllowed allowed backend = false) :
    ∃ reason, plan allowed backend q s = .error (.refused backend.name reason) :=
  ⟨"the project doesn't allow this backend", by simp [plan, h]⟩

/-- A schema outside the supported subset is refused. -/
theorem plan_refuses_unsupported {allowed : List Backend} {backend : Backend} {q : Question}
    (s : System.FilePath) (problem : String) (h : Schema.unsupported q.schema = some problem) :
    ∃ failure, plan allowed backend q s = .error failure := by
  unfold plan
  split
  · exact ⟨_, rfl⟩
  · rw [h]
    exact ⟨_, rfl⟩

/-- A prompt over the limit is refused. -/
theorem plan_refuses_oversized {allowed : List Backend} {backend : Backend} {q : Question}
    (s : System.FilePath) (h : q.prompt.utf8ByteSize > maxPromptBytes) :
    ∃ failure, plan allowed backend q s = .error failure := by
  unfold plan
  split
  · exact ⟨_, rfl⟩
  · split
    · exact ⟨_, rfl⟩
    · -- `split` resolved the size test from `h`, leaving the refusal.
      exact ⟨_, rfl⟩

/-- What `plan` lets through is exactly the adapter's command line. -/
theorem plan_runs_invocation {allowed : List Backend} {backend : Backend} {q : Question}
    {s : System.FilePath} {inv : Invocation} (h : plan allowed backend q s = .ok inv) :
    inv = invocation backend q s := by
  unfold plan at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · cases h; rfl

/-- A refused question never reaches the runner: `ask` returns the refusal without calling it. -/
theorem ask_refused_runs_nothing (runner : Runner) {allowed : List Backend} {backend : Backend}
    {q : Question} {s : System.FilePath} {failure : Failure}
    (h : plan allowed backend q s = .error failure) :
    ask runner allowed backend q s = pure (.error failure) := by
  simp [ask, h]

/-- A refused question used nothing: its usage is the empty record. -/
theorem refused_used_nothing (runner : Runner) {allowed : List Backend} {backend : Backend}
    {q : Question} {s : System.FilePath} {failure : Failure}
    (h : plan allowed backend q s = .error failure) :
    askWithUsage runner allowed backend q s = pure (.error failure, {}) := by
  simp [askWithUsage, h]

/-- A question to Claude Code runs with no tools and without the user's settings, at any effort. -/
theorem claude_question_cannot_act (model dest : String) (effort : Option String) (q : Question)
    (s : System.FilePath) :
    let args := (invocation ⟨.claudeCode, model, dest, effort⟩ q s).args.toList
    "--safe-mode" ∈ args ∧ ["--tools", ""] <:+: args := by
  cases effort with
  | none =>
    refine ⟨by simp [invocation, callInvocation], ?_⟩
    exact ⟨["-p", "--safe-mode"], ["--no-session-persistence", "--model", model, "--output-format",
      "json", "--json-schema", q.schema.compress, "--", q.prompt],
      by simp [invocation, callInvocation]⟩
  | some e =>
    refine ⟨by simp [invocation, callInvocation], ?_⟩
    exact ⟨["-p", "--safe-mode"], ["--no-session-persistence", "--model", model, "--effort", e,
      "--output-format", "json", "--json-schema", q.schema.compress, "--", q.prompt],
      by simp [invocation, callInvocation]⟩

/-- A configured effort reaches Claude Code as its `--effort` flag. -/
theorem claude_question_effort (model dest e : String) (q : Question) (s : System.FilePath) :
    ["--model", model, "--effort", e] <:+:
      (invocation ⟨.claudeCode, model, dest, some e⟩ q s).args.toList :=
  ⟨["-p", "--safe-mode", "--tools", "", "--no-session-persistence"],
    ["--output-format", "json", "--json-schema", q.schema.compress, "--", q.prompt],
    by simp [invocation, callInvocation]⟩

/-- A question to Codex runs in a read-only sandbox, at any effort. -/
theorem codex_question_read_only (model dest : String) (effort : Option String) (q : Question)
    (s : System.FilePath) :
    ["--sandbox", "read-only"] <:+: (invocation ⟨.codex, model, dest, effort⟩ q s).args.toList := by
  cases effort with
  | none =>
    exact ⟨["exec", "--json", "--skip-git-repo-check", "--ephemeral"], ["-m", model, "--output-schema",
      "schema.json", "-o", "answer.json", "-"], by simp [invocation, callInvocation]⟩
  | some e =>
    exact ⟨["exec", "--json", "--skip-git-repo-check", "--ephemeral"], ["-m", model, "-c",
      s!"model_reasoning_effort=\"{e}\"", "--output-schema", "schema.json", "-o", "answer.json",
      "-"], by simp [invocation, callInvocation]⟩

/-- A question to Codex prints its events as JSON lines, where its usage is read, and still writes
its answer to the file the adapter reads back. -/
theorem codex_question_events (model dest : String) (effort : Option String) (q : Question)
    (s : System.FilePath) :
    let args := (invocation ⟨.codex, model, dest, effort⟩ q s).args.toList
    "--json" ∈ args ∧ ["-o", "answer.json"] <:+: args := by
  cases effort with
  | none =>
    refine ⟨by simp [invocation, callInvocation], ?_⟩
    exact ⟨["exec", "--json", "--skip-git-repo-check", "--ephemeral", "--sandbox", "read-only", "-m",
      model, "--output-schema", "schema.json"], ["-"], by simp [invocation, callInvocation]⟩
  | some e =>
    refine ⟨by simp [invocation, callInvocation], ?_⟩
    exact ⟨["exec", "--json", "--skip-git-repo-check", "--ephemeral", "--sandbox", "read-only", "-m",
      model, "-c", s!"model_reasoning_effort=\"{e}\"", "--output-schema", "schema.json"], ["-"],
      by simp [invocation, callInvocation]⟩

/-- A configured effort reaches Codex as its reasoning-effort setting. -/
theorem codex_question_effort (model dest e : String) (q : Question) (s : System.FilePath) :
    ["-m", model, "-c", s!"model_reasoning_effort=\"{e}\""] <:+:
      (invocation ⟨.codex, model, dest, some e⟩ q s).args.toList :=
  ⟨["exec", "--json", "--skip-git-repo-check", "--ephemeral", "--sandbox", "read-only"],
    ["--output-schema", "schema.json", "-o", "answer.json", "-"],
    by simp [invocation, callInvocation]⟩

theorem codex_question_input (model dest : String) (effort : Option String) (q : Question)
    (s : System.FilePath) :
    (invocation ⟨.codex, model, dest, effort⟩ q s).input = some q.prompt := by
  cases effort <;> rfl

/-- Each question runs in the scratch directory it was given. -/
theorem question_runs_in_scratch (b : Backend) (q : Question) (s : System.FilePath) :
    (invocation b q s).cwd = s := by
  cases h : b.harness <;> simp [invocation, callInvocation, h]

theorem codex_agent_workspace (model dest : String) (effort : Option String) (q : Question)
    (s : System.FilePath) (tools : List String) :
    ["--sandbox", "workspace-write", "-C", s.toString] <:+:
      (agentInvocation ⟨.codex, model, dest, effort⟩ q tools s).args.toList := by
  cases effort with
  | none =>
    exact ⟨["exec", "--json", "--skip-git-repo-check", "--ephemeral"],
      ["-m", model, "--output-schema", "schema.json", "-o", "answer.json", "--", q.prompt],
      by simp [agentInvocation, callInvocation]⟩
  | some e =>
    exact ⟨["exec", "--json", "--skip-git-repo-check", "--ephemeral"],
      ["-m", model, "-c", s!"model_reasoning_effort=\"{e}\"", "--output-schema", "schema.json",
        "-o", "answer.json", "--", q.prompt],
      by simp [agentInvocation, callInvocation]⟩

theorem claude_agent_tools (model dest : String) (effort : Option String) (q : Question)
    (s : System.FilePath) (tools : List String) :
    let names := ",".intercalate (tools.map fun t => (t.splitOn "(").headD t).eraseDups
    ["--tools", names, "--allowedTools", " ".intercalate tools] <:+:
      (agentInvocation ⟨.claudeCode, model, dest, effort⟩ q tools s).args.toList := by
  cases effort with
  | none =>
    exact ⟨["-p", "--safe-mode"], ["--no-session-persistence", "--model", model, "--output-format",
      "json", "--json-schema", q.schema.compress, "--", q.prompt],
      by simp [agentInvocation, callInvocation]⟩
  | some e =>
    exact ⟨["-p", "--safe-mode"], ["--no-session-persistence", "--model", model, "--effort", e,
      "--output-format", "json", "--json-schema", q.schema.compress, "--", q.prompt],
      by simp [agentInvocation, callInvocation]⟩

/-- An overrun is an error naming the backend and its limit. -/
theorem finish_overrun (b : Backend) (q : Question) :
    finish b q none = .error (.timedOut b.name q.timeoutMs) := rfl

/-- A non-zero exit is an error naming the backend and the status. -/
theorem finish_nonzero_exit (b : Backend) (q : Question) (ran : Ran) (h : ran.exitCode ≠ 0) :
    ∃ lines, finish b q (some ran) = .error (.exited b.name ran.exitCode lines) := by
  refine ⟨firstLines (ran.stderr ++ "\n" ++ ran.stdout), ?_⟩
  have : (ran.exitCode != 0) = true := by simpa using h
  simp only [finish, readAnswer, this, bind, Except.bind, ite_true]
  rfl

/-- Every answer `finish` returns meets the question's schema. -/
theorem finish_answer_conforms {b : Backend} {q : Question} {ran : Ran} {o : Outcome}
    (h : finish b q (some ran) = .ok o) : Schema.violation q.schema o.answer = none := by
  simp only [finish, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i pair _
    split at h
    · cases h
    · rename_i hv
      cases h
      exact hv

/-- Claude Code's own error report is never taken for an answer. -/
theorem claude_reported_error_fails (model dest : String) (effort : Option String) {ran : Ran}
    {report : Json} (exit0 : ran.exitCode = 0) (parsed : Json.parse ran.stdout = .ok report)
    (flagged : report.getObjValAs? Bool "is_error" = .ok true) :
    ∃ failure, readAnswer ⟨.claudeCode, model, dest, effort⟩ ran = .error failure := by
  refine ⟨.malformed (Backend.name ⟨.claudeCode, model, dest, effort⟩)
    s!"the harness reported an error: {firstLines ran.stdout}", ?_⟩
  simp [readAnswer, exit0, parsed, flagged, bind, Except.bind, Except.mapError, Except.toOption]
  rfl

/-- Codex without its answer file gives no answer. -/
theorem codex_missing_answer_fails (model dest : String) (effort : Option String) {ran : Ran}
    (exit0 : ran.exitCode = 0) (missing : ran.readBack.lookup "answer.json" = none) :
    ∃ failure, readAnswer ⟨.codex, model, dest, effort⟩ ran = .error failure := by
  refine ⟨.malformed (Backend.name ⟨.codex, model, dest, effort⟩)
    "the answer file was not written", ?_⟩
  simp [readAnswer, exit0, missing]
  rfl

/-! Witnesses: each theorem's hypotheses can hold, so none of them is vacuous. -/

/-- A destination label cannot change process routing, arguments or request data. -/
theorem destination_does_not_route (harness : Harness) (model before after : String)
    (effort : Option String) (q : Question) (s : System.FilePath) :
    invocation ⟨harness, model, before, effort⟩ q s =
      invocation ⟨harness, model, after, effort⟩ q s := by
  cases harness <;> rfl

/-- Descriptive destination notes cannot change the planner's permission decision or invocation. -/
theorem plan_ignores_destination (allowed : List Backend) (backend : Backend) (destination : String)
    (q : Question) (s : System.FilePath) :
    plan allowed { backend with dataGoesTo := destination } q s = plan allowed backend q s := by
  rcases backend with ⟨harness, model, previous, effort⟩
  simp only [plan, routeAllowed, Backend.name]
  rw [destination_does_not_route harness model destination previous effort]
  rfl

example : routeAllowed [] ⟨.codex, "m", "d", none⟩ = false := rfl

/-- External adapters receive one JSON request file and literal arguments, without shell expansion. -/
theorem command_invocation (executable model destination : String) (arguments : List String)
    (effort : Option String) (q : Question) (s : System.FilePath) :
    invocation ⟨.command executable arguments, model, destination, effort⟩ q s =
      { cmd := executable, args := (arguments ++ ["request.json"]).toArray, cwd := s,
        files := [("request.json",
          (commandRequest ⟨.command executable arguments, model, destination, effort⟩ q).compress)] } :=
  rfl

/-- Agent adapters receive the same request protocol with the requested mode and tool policy. -/
theorem command_agent_invocation (executable model destination : String)
    (arguments tools : List String) (effort : Option String) (q : Question) (s : System.FilePath) :
    agentInvocation ⟨.command executable arguments, model, destination, effort⟩ q tools s =
      { cmd := executable, args := (arguments ++ ["request.json"]).toArray, cwd := s,
        files := [("request.json",
          (commandRequest ⟨.command executable arguments, model, destination, effort⟩ q "agent"
            tools).compress)] } :=
  rfl

example : (⟨.codex, "m", "d", none⟩ : Backend) ∉ ([] : List Backend) := by simp

example : Schema.unsupported (Json.mkObj [("type", "string"), ("pattern", "a+")]) ≠ none := by
  native_decide

example : ("".pushn 'x' (maxPromptBytes + 1)).utf8ByteSize > maxPromptBytes := by native_decide

example : ∃ ran : Ran, ran.exitCode ≠ 0 := ⟨⟨1, "", "", [], 0⟩, by decide⟩

/-- A report Claude Code flags as an error parses and carries the flag. -/
example : (match Json.parse "{\"is_error\":true}" with
    | .ok report => (report.getObjValAs? Bool "is_error").toOption == some true
    | .error _ => false) = true := by native_decide

example : ∃ ran : Ran, ran.exitCode = 0 ∧ ran.readBack.lookup "answer.json" = none :=
  ⟨⟨0, "", "", [], 0⟩, rfl, rfl⟩

/-- An agent run outside `/tmp` is never sent to another host, since its mirror is removed after. -/
theorem onHost_refuses_agent_outside_tmp (host : String) (inv : Invocation) (readBack : List String)
    (h : inv.args.contains "--allowedTools" = true)
    (ht : inv.cwd.toString.startsWith "/tmp/" = false) :
    (onHost host inv readBack).toOption = none := by
  have hm : "--allowedTools" ∈ inv.args := by simpa using h
  unfold onHost
  split
  · rfl
  · simp [hm, ht, Except.toOption]

/-- An agent run under `/tmp` follows `agentScript`. -/
theorem onHost_agent (host : String) (inv : Invocation) (readBack : List String)
    (hf : inv.files = []) (hr : readBack = [])
    (h : inv.args.contains "--allowedTools" = true)
    (ht : inv.cwd.toString.startsWith "/tmp/" = true) :
    onHost host inv readBack = .ok { inv with cmd := "sh", args := #["-c", agentScript host inv] } := by
  have hm : "--allowedTools" ∈ inv.args := by simpa using h
  simp [onHost, hf, hr, hm, ht]

/-- A call that exchanges files is never sent to another host. -/
theorem onHost_refuses_files (host : String) (inv : Invocation) (readBack : List String)
    (h : !inv.files.isEmpty || !readBack.isEmpty) : (onHost host inv readBack).toOption = none := by
  unfold onHost
  rw [if_pos h]
  rfl

/-- A question sent to another host runs ssh to that host, the whole command its last word, its
working directory and input unchanged. -/
theorem onHost_question (host : String) (inv i : Invocation) (readBack : List String)
    (hq : inv.args.contains "--allowedTools" = false)
    (h : onHost host inv readBack = .ok i) :
    i.cmd = "ssh" ∧ i.args = #["-o", "BatchMode=yes", host, questionCommand inv] ∧
      i.cwd = inv.cwd ∧ i.input = inv.input := by
  unfold onHost at h
  split at h
  · cases h
  · rw [if_neg (by rw [hq]; exact Bool.false_ne_true)] at h
    cases h
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- A Claude question sent to build-host: its words quoted, a quote inside one written `'\''`. -/
example :
    let inv : Invocation :=
      { cmd := "claude", args := #["-p", "--tools", "", "--", "it's"], cwd := "/tmp/q" }
    remoteCommand inv =
    "mkdir -p '/tmp/q' && cd '/tmp/q' && 'claude' '-p' '--tools' '' '--' 'it'\\''s'" := by
  native_decide

/-- The question's directory removed after, its status kept. -/
example :
    let inv : Invocation := { cmd := "claude", args := #["-p"], cwd := "/tmp/t/q" }
    questionCommand inv =
    "mkdir -p '/tmp/t/q' && cd '/tmp/t/q' && 'claude' '-p'; s=$?; cd / && rmdir -p \
    --ignore-fail-on-non-empty '/tmp/t/q' 2>/dev/null; exit $s" := by
  native_decide

/-- Claude Code's question sent to a host runs through ssh; its agent run in a copy under `/tmp`
runs the mirroring script; one in a copy elsewhere is refused. -/
example :
    let b : Backend := ⟨.claudeCode, "claude-opus-5-5", "Anthropic", some "medium"⟩
    let q : Question := { prompt := "p", schema := Json.mkObj [], timeoutMs := 1 }
    ((onHost "build-host" (callInvocation b q "/tmp/s" .question) []).toOption.map (·.cmd)) ==
        some "ssh" &&
      ((onHost "build-host" (callInvocation b q "/tmp/s" (.agent ["Read"])) []).toOption.map (·.cmd)) ==
        some "sh" &&
      (onHost "build-host" (callInvocation b q "/home/user" (.agent ["Read"])) []).toOption.isNone := by
  native_decide

/-- The mirroring script: the copy made on the host, synced, the harness run there, the mirror
removed with the parents left empty, the harness's status kept. -/
example :
    let inv : Invocation := { cmd := "claude", args := #["-p"], cwd := "/tmp/t/c" }
    agentScript "build-host" inv =
      "ssh -o BatchMode=yes 'build-host' 'mkdir -p '\\''/tmp/t/c'\\''' && rsync -a --delete '/tmp/t/c/' \
      'build-host:/tmp/t/c/' && ssh -o BatchMode=yes 'build-host' 'mkdir -p '\\''/tmp/t/c'\\'' && cd \
      '\\''/tmp/t/c'\\'' && '\\''claude'\\'' '\\''-p'\\'''; s=$?; ssh -o BatchMode=yes 'build-host' \
      'rm -rf '\\''/tmp/t/c'\\''; rmdir -p --ignore-fail-on-non-empty '\\''/tmp/t'\\'''; exit $s" := by
  native_decide

end SpecTools.Model
