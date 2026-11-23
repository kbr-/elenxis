import SpecTools.GapsRun

namespace SpecTools.DraftHook
open Lean SpecTools.Gaps

structure Submission where
  path : String
  text : String
  deriving BEq, Repr

inductive PatchLine where
  | add (path : String)
  | boundary
  | payload (text : String)
  | other

def classifyLine (line : String) : PatchLine :=
  if line.startsWith "*** Add File: " then .add (line.drop 14).toString
  else if line.startsWith "*** " then .boundary
  else if line.startsWith "+" then .payload (line.drop 1).toString
  else .other

def PatchLine.addPath : PatchLine → Option String
  | .add path => some path
  | _ => none

/-- Close the current addition at the next section header or at the end of input. -/
def collectAdditions (current : Option Submission) : List PatchLine → List Submission
  | [] => current.toList
  | .add path :: rest => current.toList ++ collectAdditions (some ⟨path, ""⟩) rest
  | .boundary :: rest => current.toList ++ collectAdditions none rest
  | .payload text :: rest => collectAdditions
      (current.map fun item => { item with text := item.text ++ text ++ "\n" }) rest
  | .other :: rest => collectAdditions current rest

/-- Extract complete Add File bodies; update hunks belong to later repair rounds. -/
def additions (patch : String) : List Submission :=
  collectAdditions none ((patch.splitOn "\n").map classifyLine)

private theorem collect_payload (item : Submission) (body : List String) (rest : List PatchLine) :
    collectAdditions (some item) (body.map PatchLine.payload ++ rest) =
      collectAdditions (some { item with
        text := body.foldl (fun text line => text ++ line ++ "\n") item.text }) rest := by
  induction body generalizing item with
  | nil => rfl
  | cons line body ih =>
    simpa [collectAdditions, List.foldl_cons] using
      ih { item with text := item.text ++ line ++ "\n" }

theorem collect_add_section (path : String) (body : List String) (rest : List PatchLine) :
    collectAdditions none (.add path :: (body.map PatchLine.payload ++ .boundary :: rest)) =
      ⟨path, body.foldl (fun text line => text ++ line ++ "\n") ""⟩ ::
        collectAdditions none rest := by
  simp only [collectAdditions, Option.toList_none, List.nil_append]
  rw [collect_payload]
  rfl

private theorem collect_paths (current : Option Submission) (lines : List PatchLine) :
    (collectAdditions current lines).map Submission.path =
      current.toList.map Submission.path ++ lines.filterMap PatchLine.addPath := by
  induction lines generalizing current with
  | nil => simp [collectAdditions]
  | cons line rest ih =>
    cases current <;> cases line <;>
      simp [collectAdditions, List.filterMap_cons, PatchLine.addPath, ih]

theorem additions_paths (patch : String) :
    (additions patch).map Submission.path =
      ((patch.splitOn "\n").map classifyLine).filterMap PatchLine.addPath := by
  simpa [additions] using collect_paths none ((patch.splitOn "\n").map classifyLine)

theorem additions_without_add_headers (patch : String)
    (headers : ∀ line ∈ patch.splitOn "\n", line.startsWith "*** Add File: " = false) :
    additions patch = [] := by
  apply (List.map_eq_nil_iff (f := Submission.path)).mp
  rw [additions_paths, List.filterMap_map, List.filterMap_eq_nil_iff]
  intro line member
  simp only [Function.comp_apply, classifyLine, headers line member, Bool.false_eq_true,
    ite_false]
  split
  · rfl
  · split <;> rfl

def field (j : Json) (key : String) : String :=
  (j.getObjValAs? String key).toOption.getD ""

def submissions (payload : Json) : List Submission :=
  let input := (payload.getObjVal? "tool_input").toOption.getD Json.null
  match field payload "tool_name" with
  | "Write" => [⟨field input "file_path", field input "content"⟩]
  | "apply_patch" => additions (field input "command")
  | _ => []

def pathAt (cwd path : String) : String :=
  let file := System.FilePath.mk path
  (if file.isAbsolute then file else System.FilePath.mk cwd / file).normalize.toString

def selected (cwd expected : String) (items : List Submission) : List Submission :=
  items.filter fun item => pathAt cwd item.path == expected

theorem selected_iff (cwd expected : String) (items : List Submission) (item : Submission) :
    item ∈ selected cwd expected items ↔ item ∈ items ∧ pathAt cwd item.path = expected := by
  simp [selected]

/-- Every selected submission names the exact task's draft path. -/
theorem selected_exact (cwd expected : String) (items : List Submission) (item : Submission)
    (h : item ∈ selected cwd expected items) : pathAt cwd item.path = expected := by
  exact ((selected_iff cwd expected items item).mp h).2

def inventory (clauses : List (String × String)) : List DraftSource :=
  clauses.zipIdx.map fun ((_, text), index) => ⟨toString (index + 1), text⟩

theorem inventory_length (clauses : List (String × String)) :
    (inventory clauses).length = clauses.length := by simp [inventory]

def issues (clauses : List (String × String)) (text : String) : Except String (List String) := do
  let rows : List DraftRow ← (Json.parse text).bind fromJson?
  return draftIssues (inventory clauses) rows

/-- Successful admission has exactly the existing full-inventory validator's verdict. -/
theorem issues_complete (clauses : List (String × String)) (text : String)
    (rows : List DraftRow) (h : (Json.parse text).bind fromJson? = .ok rows) :
    issues clauses text = .ok (draftIssues (inventory clauses) rows) := by
  simp [issues, h]
  rfl

def identityIssue (payload : Json) (tasks : List (String × String)) : Option (String × String) :=
  if tasks.isEmpty || field payload "session_id" != "" then none
  else some ("task_lock_gate:no session",
    s!"this call writes the records of task {(tasks.headD ("", "")).1}, and its hook input has no session_id, so no lock can tell this session from another; report the harness call to the user.")

theorem no_task_identity (payload : Json) : identityIssue payload [] = none := by
  simp [identityIssue]

theorem supplied_identity (payload : Json) (tasks : List (String × String))
    (h : (field payload "session_id" != "") = true) : identityIssue payload tasks = none := by
  simp [identityIssue, h]

theorem missing_task_identity (payload : Json) (task : String × String)
    (others : List (String × String)) (missing : field payload "session_id" = "") :
    (identityIssue payload (task :: others)).map Prod.fst = some "task_lock_gate:no session" := by
  simp [identityIssue, missing]

def check (python bridge : String) : IO (Option (String × String)) := do
  let raw ← (← IO.getStdin).readToEnd
  let input : Json × List (String × String) ← IO.ofExcept ((Json.parse raw).bind fromJson?)
  let (payload, tasks) := input
  let cwd := field payload "cwd"
  for (slug, root) in tasks do
    let task := System.FilePath.mk root / "tasks" / slug
    let expected := (task / "spec" / "Coverage.draft.json").normalize.toString
    for item in selected cwd expected (submissions payload) do
      let extracted ← IO.Process.output {
        cmd := python, args := #[bridge, (task / "PLAN.md").toString] }
      if extracted.exitCode != 0 then
        return some ("coverage_draft_gate:incomplete", extracted.stderr)
      let clauses : List (String × String) ←
        IO.ofExcept ((Json.parse extracted.stdout).bind fromJson?)
      let problems ← IO.ofExcept (issues clauses item.text)
      unless problems.isEmpty do
        return some ("coverage_draft_gate:incomplete",
          s!"{slug}: submit all Coverage clauses in one write.\n{"\n".intercalate problems}")
  return identityIssue payload tasks

def run (python bridge : String) : IO UInt32 := do
  match ← check python bridge with
  | none => return 0
  | some (kind, message) => IO.eprintln s!"Refused ({kind}): {message}"; return 2

/-- The Python hook applies this structured verdict through its existing refusal path. -/
def runJson (python bridge : String) : IO UInt32 := do
  let problem ← try check python bridge
    catch error => pure (some ("coverage_draft_gate:incomplete", toString error))
  IO.println (toJson problem).compress
  return 0

end SpecTools.DraftHook
