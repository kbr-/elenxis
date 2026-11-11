import SpecTools.GapsRun

namespace SpecTools.DraftHook
open Lean SpecTools.Gaps

structure Submission where
  path : String
  text : String
  deriving BEq, Repr

/-- Extract complete Add File bodies; update hunks belong to later repair rounds. -/
def additions (patch : String) : List Submission := Id.run do
  let mut result := []
  let mut current : Option Submission := none
  for line in patch.splitOn "\n" do
    if line.startsWith "*** Add File: " then
      if let some previous := current then result := result ++ [previous]
      current := some ⟨(line.drop 14).toString, ""⟩
    else if line.startsWith "*** " then
      if let some previous := current then result := result ++ [previous]
      current := none
    else if line.startsWith "+" then
      current := current.map fun item => { item with text := item.text ++ (line.drop 1).toString ++ "\n" }
  if let some previous := current then result := result ++ [previous]
  return result

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

/-- Every selected submission names the exact task's draft path. -/
theorem selected_exact (cwd expected : String) (items : List Submission) (item : Submission)
    (h : item ∈ selected cwd expected items) : pathAt cwd item.path = expected := by
  simp only [selected, List.mem_filter, beq_iff_eq] at h
  exact h.2

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

def run (python bridge : String) : IO UInt32 := do
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
        IO.eprintln extracted.stderr
        return 2
      let clauses : List (String × String) ←
        IO.ofExcept ((Json.parse extracted.stdout).bind fromJson?)
      let problems ← IO.ofExcept (issues clauses item.text)
      unless problems.isEmpty do
        IO.eprintln s!"Refused (coverage_draft_gate:incomplete): {slug}: submit all Coverage clauses in one write."
        IO.eprintln ("\n".intercalate problems)
        return 2
  return 0

end SpecTools.DraftHook
