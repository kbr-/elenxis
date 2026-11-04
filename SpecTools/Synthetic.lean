/-!
The synthetic test's variant generator: a variant is the complete fixture with some planted gaps,
each a named set of exact-text edits; the key (which gaps, of which kind, on which clause) stays
with the generator. The choice of plants comes from a seed, so a batch is reproducible. Pure: the
files are given and returned as text.
-/

namespace SpecTools.Synthetic

/-- One exact-text edit of one file. -/
structure Edit where
  file : String
  old : String
  new : String
  deriving Repr, DecidableEq, Inhabited

/-- A planted gap: its kind (one of the eight), the clause it concerns, and its edits. -/
structure Plant where
  kind : String
  clause : String
  edits : List Edit
  deriving Repr, DecidableEq, Inhabited

/-- The number of times `pat` occurs in `s`, by position. -/
def occurrences (pat s : String) : Nat := (s.splitOn pat).length - 1

/-- Apply an edit to the files, refusing one whose old text doesn't occur exactly once. -/
def applyEdit (files : List (String × String)) (e : Edit) : Except String (List (String × String)) :=
  match files.lookup e.file with
  | none => .error s!"no file {e.file}"
  | some text =>
    if occurrences e.old text != 1 then
      .error s!"{e.file}: the edit's text occurs {occurrences e.old text} times, not once"
    else .ok (files.map fun (f, t) => if f == e.file then (f, t.replace e.old e.new) else (f, t))

def applyEdits (files : List (String × String)) : List Edit → Except String (List (String × String))
  | [] => .ok files
  | e :: es => applyEdit files e >>= fun fs => applyEdits fs es

/-- A linear congruential generator's next state. -/
def next (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- A draw below `m` from state `s`, read from its high bits: a power-of-two generator's bit `k`
repeats with period `2 ^ (k + 1)`, so its low bits are no fair draw. -/
def draw (s m : Nat) : Nat := (s / 2 ^ 40) % m

/-- `k` distinct indices below `n`, drawn from `seed`, in drawing order. -/
def pick (seed n k : Nat) : List Nat :=
  go seed k (List.range n) []
where
  go (s : Nat) : Nat → List Nat → List Nat → List Nat
    | 0, _, acc => acc.reverse
    | _, [], acc => acc.reverse
    | k + 1, pool, acc =>
      let s' := next s
      let i := draw s' pool.length
      go s' k (pool.eraseIdx i) (pool[i]! :: acc)

/-- A variant: its files and its key. -/
structure Variant where
  files : List (String × String)
  key : List Plant

/-- Variant `index` of a batch from `seed`: the first `empty` variants plant nothing, the others
between one and three plants. -/
def variant (catalogue : List Plant) (fixture : List (String × String)) (seed index empty : Nat) :
    Except String Variant :=
  let s := next (seed + index * 7919)
  let count := if index < empty then 0 else 1 + draw s 3
  let chosen := (pick s catalogue.length count).map fun i => catalogue[i]!
  (applyEdits fixture (chosen.flatMap (·.edits))).map fun files => { files, key := chosen }

end SpecTools.Synthetic
