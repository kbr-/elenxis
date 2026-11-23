import Lean.Data.Json

namespace SpecTools.Replay
open Lean

structure Observation (State : Type) where
  accepted : Bool
  state : State
  deriving DecidableEq, FromJson, ToJson

/-- A fixture supplies a concrete operation and may append further operations to the trace. -/
structure Trace (State Operation : Type) where
  initial : State
  first : Operation
  rest : List Operation

def Trace.operations (tr : Trace State Operation) : List Operation :=
  tr.first :: tr.rest

def observe (step : State → Operation → Option State) (view : State → Snapshot) :
    State → List Operation → List (Observation Snapshot)
  | _, [] => []
  | s, op :: rest =>
    match step s op with
    | none => ⟨false, view s⟩ :: observe step view s rest
    | some next => ⟨true, view next⟩ :: observe step view next rest

theorem observe_length (step : State → Operation → Option State) (view : State → Snapshot)
    (s : State) (ops : List Operation) : (observe step view s ops).length = ops.length := by
  induction ops generalizing s with
  | nil => rfl
  | cons op rest ih =>
    unfold observe
    cases step s op <;> simp [ih]

theorem refusal_observed (step : State → Operation → Option State) (view : State → Snapshot)
    (s : State) (op : Operation) (rest : List Operation) (h : step s op = none) :
    observe step view s (op :: rest) = ⟨false, view s⟩ :: observe step view s rest := by
  simp [observe, h]

/-- Compare aligned observations. The entry point checks equal lengths before calling this. -/
def firstMismatch [DecidableEq α] : List α → List α → Option Nat
  | x :: xs, y :: ys =>
    if x = y then (firstMismatch xs ys).map Nat.succ else some 0
  | _, _ => none

theorem firstMismatch_none [DecidableEq α] (xs ys : List α) (hlen : xs.length = ys.length) :
    firstMismatch xs ys = none ↔ xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [firstMismatch]
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      by_cases same : x = y
      · subst y
        simp [firstMismatch, ih ys (by simpa using hlen)]
      · simp [firstMismatch, same]

theorem firstMismatch_at [DecidableEq α] (xs ys : List α) (i : Nat)
    (h : firstMismatch xs ys = some i) :
    xs[i]? ≠ ys[i]? ∧ ∀ j : Nat, j < i → xs[j]? = ys[j]? := by
  induction xs generalizing ys i with
  | nil => simp [firstMismatch] at h
  | cons x xs ih =>
    cases ys with
    | nil => simp [firstMismatch] at h
    | cons y ys =>
      by_cases same : x = y
      · subst y
        cases tail : firstMismatch xs ys with
        | none => simp [firstMismatch, tail] at h
        | some index =>
          have hi : index + 1 = i := by simpa [firstMismatch, tail, Nat.succ_eq_add_one] using h
          subst i
          obtain ⟨diff, earlier⟩ := ih ys index tail
          refine ⟨by simpa using diff, ?_⟩
          intro j hj
          cases j with
          | zero => rfl
          | succ k => simpa using earlier k (by omega)
      · have hz : i = 0 := by simpa [firstMismatch, same] using h.symm
        subst i
        simp [same]

def decode [FromJson Snapshot] (count : Nat) (raw : String) :
    Except String (List (Observation Snapshot)) :=
  match (Json.parse raw).bind fromJson? with
  | .error message => .error s!"malformed observations: {message}"
  | .ok records =>
    if records.length = count then .ok records
    else .error s!"expected {count} observations, got {records.length}"

theorem decode_length [FromJson Snapshot] (count : Nat) (raw : String)
    (records : List (Observation Snapshot)) (h : decode count raw = .ok records) :
    records.length = count := by
  unfold decode at h
  cases parsed : ((Json.parse raw).bind fromJson? : Except String (List (Observation Snapshot))) with
  | error message => simp [parsed] at h
  | ok result =>
    by_cases hs : result.length = count
    · simp [parsed, hs] at h
      subst records
      exact hs
    · simp [parsed, hs] at h

#guard (decode (Snapshot := Nat) 1 "[").isOk == false
#guard (decode (Snapshot := Nat) 1 "[{\"accepted\":true}]").isOk == false
#guard (decode (Snapshot := Nat) 1 "[]").isOk == false
#guard (decode (Snapshot := Nat) 0 "[{\"accepted\":true,\"state\":1}]").isOk == false
#guard (decode (Snapshot := Nat) 1 "[{\"accepted\":true,\"state\":1}]").isOk

def run [ToJson State] [ToJson Operation] [DecidableEq Snapshot]
    [ToJson Snapshot] [FromJson Snapshot] (tr : Trace State Operation)
    (step : State → Operation → Option State) (view : State → Snapshot)
    (adapter cwd : String) : IO Unit := do
  let scratch ← IO.FS.createTempDir
  let ops := tr.operations
  let request := Json.mkObj [("initial", toJson tr.initial), ("operations", toJson ops)]
  let response ← try
      let input := scratch / "trace.json"
      IO.FS.writeFile input request.compress
      IO.Process.output { cmd := "python3", args := #[adapter, input.toString], cwd := some cwd }
    finally IO.FS.removeDirAll scratch
  if response.exitCode != 0 then
    throw (IO.userError s!"replay error: Python exited {response.exitCode}: {response.stderr}")
  let actual : List (Observation Snapshot) ←
    IO.ofExcept ((decode ops.length response.stdout).mapError (s!"replay error: " ++ ·))
  let expected := observe step view tr.initial ops
  if let some index := firstMismatch expected actual then
    match ops[index]?, expected[index]?, actual[index]? with
    | some op, some left, some right =>
      throw (IO.userError
        (s!"replay disagreement at operation {index + 1}: {(toJson op).compress}\n" ++
          s!"Lean: {(toJson left).compress}\nPython: {(toJson right).compress}"))
    | _, _, _ => throw (IO.userError "replay error: comparison returned an out-of-range index")
  let accepted := (expected.filter (·.accepted)).length
  IO.println s!"replay: {ops.length} matching observations, {accepted} accepted, {ops.length - accepted} refused"

end SpecTools.Replay
