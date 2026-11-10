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

/-- A question to Claude Code runs with no tools and without the user's settings. -/
theorem claude_question_cannot_act (model dest : String) (q : Question) (s : System.FilePath) :
    let args := (invocation ⟨.claudeCode, model, dest⟩ q s).args.toList
    "--safe-mode" ∈ args ∧ ["--tools", ""] <:+: args := by
  refine ⟨by simp [invocation, callInvocation], ?_⟩
  exact ⟨["-p", "--safe-mode"], ["--no-session-persistence", "--model", model, "--output-format",
    "json", "--json-schema", q.schema.compress, "--", q.prompt], by simp [invocation, callInvocation]⟩

/-- A question to Codex runs in a read-only sandbox. -/
theorem codex_question_read_only (model dest : String) (q : Question) (s : System.FilePath) :
    ["--sandbox", "read-only"] <:+: (invocation ⟨.codex, model, dest⟩ q s).args.toList :=
  ⟨["exec", "--skip-git-repo-check", "--ephemeral"], ["-m", model, "--output-schema", "schema.json",
    "-o", "answer.json", "-"], by simp [invocation, callInvocation]⟩

theorem codex_question_input (model dest : String) (q : Question) (s : System.FilePath) :
    (invocation ⟨.codex, model, dest⟩ q s).input = some q.prompt := by
  rfl

/-- Each question runs in the scratch directory it was given. -/
theorem question_runs_in_scratch (b : Backend) (q : Question) (s : System.FilePath) :
    (invocation b q s).cwd = s := by
  cases h : b.harness <;> simp [invocation, callInvocation, h]

theorem codex_agent_workspace (model dest : String) (q : Question) (s : System.FilePath)
    (tools : List String) :
    ["--sandbox", "workspace-write", "-C", s.toString] <:+:
      (agentInvocation ⟨.codex, model, dest⟩ q tools s).args.toList :=
  ⟨["exec", "--skip-git-repo-check", "--ephemeral"],
    ["-m", model, "--output-schema", "schema.json", "-o", "answer.json", "--", q.prompt],
    by simp [agentInvocation, callInvocation]⟩

theorem claude_agent_tools (model dest : String) (q : Question) (s : System.FilePath)
    (tools : List String) :
    let names := ",".intercalate (tools.map fun t => (t.splitOn "(").headD t).eraseDups
    ["--tools", names, "--allowedTools", " ".intercalate tools] <:+:
      (agentInvocation ⟨.claudeCode, model, dest⟩ q tools s).args.toList :=
  ⟨["-p", "--safe-mode"], ["--no-session-persistence", "--model", model, "--output-format",
    "json", "--json-schema", q.schema.compress, "--", q.prompt],
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
theorem claude_reported_error_fails (model dest : String) {ran : Ran} {report : Json}
    (exit0 : ran.exitCode = 0) (parsed : Json.parse ran.stdout = .ok report)
    (flagged : report.getObjValAs? Bool "is_error" = .ok true) :
    ∃ failure, readAnswer ⟨.claudeCode, model, dest⟩ ran = .error failure := by
  refine ⟨.malformed (Backend.name ⟨.claudeCode, model, dest⟩)
    s!"the harness reported an error: {firstLines ran.stdout}", ?_⟩
  simp [readAnswer, exit0, parsed, flagged, bind, Except.bind, Except.mapError, Except.toOption]
  rfl

/-- Codex without its answer file gives no answer. -/
theorem codex_missing_answer_fails (model dest : String) {ran : Ran} (exit0 : ran.exitCode = 0)
    (missing : ran.readBack.lookup "answer.json" = none) :
    ∃ failure, readAnswer ⟨.codex, model, dest⟩ ran = .error failure := by
  refine ⟨.malformed (Backend.name ⟨.codex, model, dest⟩) "the answer file was not written", ?_⟩
  simp [readAnswer, exit0, missing]
  rfl

/-! Witnesses: each theorem's hypotheses can hold, so none of them is vacuous. -/

/-- A destination label cannot change process routing, arguments or request data. -/
theorem destination_does_not_route (harness : Harness) (model before after : String)
    (q : Question) (s : System.FilePath) :
    invocation ⟨harness, model, before⟩ q s = invocation ⟨harness, model, after⟩ q s := by
  cases harness <;> rfl

/-- Descriptive destination notes cannot change the planner's permission decision or invocation. -/
theorem plan_ignores_destination (allowed : List Backend) (backend : Backend) (destination : String)
    (q : Question) (s : System.FilePath) :
    plan allowed { backend with dataGoesTo := destination } q s = plan allowed backend q s := by
  rcases backend with ⟨harness, model, previous⟩
  simp only [plan, routeAllowed, Backend.name]
  rw [destination_does_not_route harness model destination previous]
  rfl

example : routeAllowed [] ⟨.codex, "m", "d"⟩ = false := rfl

/-- External adapters receive one JSON request file and literal arguments, without shell expansion. -/
theorem command_invocation (executable model destination : String) (arguments : List String)
    (q : Question) (s : System.FilePath) :
    invocation ⟨.command executable arguments, model, destination⟩ q s =
      { cmd := executable, args := (arguments ++ ["request.json"]).toArray, cwd := s,
        files := [("request.json",
          (commandRequest ⟨.command executable arguments, model, destination⟩ q).compress)] } := rfl

/-- Agent adapters receive the same request protocol with the requested mode and tool policy. -/
theorem command_agent_invocation (executable model destination : String) (arguments tools : List String)
    (q : Question) (s : System.FilePath) :
    agentInvocation ⟨.command executable arguments, model, destination⟩ q tools s =
      { cmd := executable, args := (arguments ++ ["request.json"]).toArray, cwd := s,
        files := [("request.json",
          (commandRequest ⟨.command executable arguments, model, destination⟩ q "agent" tools).compress)] } := rfl

example : (⟨.codex, "m", "d"⟩ : Backend) ∉ ([] : List Backend) := by simp

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

end SpecTools.Model
