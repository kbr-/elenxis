import SpecTools.Model

/-!
`clauses`: a model extracts a prose file's clauses; a second extraction, made blind to the first, is
compared with it, and each clause one has and the other lacks is printed as a row to add. The
comparison is pure (`differences`); the extraction asks a model through `SpecTools.Model.ask`.
-/

namespace SpecTools.Clauses
open Lean SpecTools.Model

/-- A clause as compared: lower case, runs of white space as one space, trimmed. -/
def normalize (s : String) : String :=
  " ".intercalate ((s.toLower.splitOn " ").filter (· ≠ "") |>.flatMap fun w =>
    (w.splitOn "\n").filter (· ≠ ""))

/-- The members of `b` that `a` lacks, each once. -/
def missingFrom (a b : List String) : List String := (b.filter (!a.contains ·)).eraseDups

/-- The clauses one extraction has and the other lacks (compared as given; callers normalize). -/
def differences (first second : List String) : List String :=
  missingFrom first second ++ missingFrom second first

/-- The schema of an extraction: a list of clauses, each a quoted sentence or table row. -/
def extractionSchema : Json :=
  Json.mkObj [("type", "object"),
    ("properties", Json.mkObj [("clauses", Json.mkObj [("type", "array"),
      ("items", Json.mkObj [("type", "string")])])]),
    ("required", Json.arr #["clauses"]), ("additionalProperties", false)]

def extractionPrompt (prose : String) : String :=
  "List every clause of the requirements below: each rule, exception, fallback and 'never', one \
  per item, quoted from the text as written. A rule spread over two sentences is one clause; each \
  row of a table stating a rule is a clause of its own. Leave out headings and explanation.\n\n" ++
  prose

def clausesOf (answer : Json) : Option (List String) := do
  let arr ← (answer.getObjValAs? (Array Json) "clauses").toOption
  arr.toList.mapM fun j => j.getStr?.toOption

/-- Two independent extractions of `prose`'s clauses, and their differences, normalized. -/
def compare (runner : Runner) (allowed : List Backend) (backend : Backend) (prose : String)
    (scratch : System.FilePath) (timeoutMs : Nat) :
    IO (Except Failure (List String × List String × List String)) := do
  let question : Question := { prompt := extractionPrompt prose, schema := extractionSchema, timeoutMs }
  IO.FS.createDirAll (scratch / "first")
  IO.FS.createDirAll (scratch / "second")
  let first ← ask runner allowed backend question (scratch / "first")
  let second ← ask runner allowed backend question (scratch / "second")
  return do
    let a ← first
    let b ← second
    let malformed := Failure.malformed backend.name "an extraction is not a list of strings"
    let ca ← (clausesOf a.answer).elim (.error malformed) .ok
    let cb ← (clausesOf b.answer).elim (.error malformed) .ok
    return (ca, cb, differences (ca.map normalize) (cb.map normalize))

end SpecTools.Clauses
