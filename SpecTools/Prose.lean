import SpecTools.Generated
import SpecTools.UsageReport

/-!
The person-prose test: a model writes a variant's requirements as a library's manager would write
them to staff, each rule in the presentation the key drew for it; the document is kept only when
two independent extractions of it, each blind to the other and to the rule list, give back exactly
the rules it was written from. The prompts, the schemas and the comparison are pure; `writeFaithful`
asks the model through a `Runner`, so tests script it.
-/

namespace SpecTools.Prose
open Lean SpecTools.Model SpecTools.Generated

/-- A rule as the prose must state it and an extraction reads it back: the generator's rule without
its number, its measures in a fixed order. -/
structure Shape where
  kind : String
  measures : List String
  bound : Nat
  flag : Option String
  deriving Repr, DecidableEq, Inhabited

/-- The shape a rule's prose states, measures sorted, since "the loans and the fines together" and
"the fines and the loans together" are one rule. -/
def Shape.norm (s : Shape) : Shape := { s with measures := s.measures.mergeSort }

def shapeOf (r : Rule) : Shape := Shape.norm ⟨r.kind, r.measures, r.bound, r.flag⟩

/-- The extraction gives back the rule list exactly: the same rules, each once, measures in any
order. -/
def faithful (expected got : List Shape) : Bool :=
  (expected.map Shape.norm).isPerm (got.map Shape.norm)

/-- The expected rules an extraction lacks, and the rules it gives that none expected. -/
def differences (expected got : List Shape) : List Shape × List Shape :=
  let e := expected.map Shape.norm
  let g := got.map Shape.norm
  (e.filter (!g.contains ·), g.filter (!e.contains ·))

/-- The folded rules paired in list order, each pair the two rules' numbers; `presentations` leaves
their number even (`pairFolded_even`). -/
def foldPairs (shown : List (Nat × Presentation)) : List (Nat × Nat) :=
  go ((shown.filter (·.2 == .folded)).map (·.1))
where
  go : List Nat → List (Nat × Nat)
    | a :: b :: rest => (a, b) :: go rest
    | _ => []

def ruleText (r : Rule) : String :=
  ruleSentence r ++ match r.flag with
    | some f => " " ++ flagSentence r f
    | none => ""

/-- How the writer is to present rule `r`, with `partner` the rule it is folded with. -/
def instruction (r : Rule) (p : Presentation) (partner : Option Nat) : String :=
  match p with
  | .plain => "state it in one plain sentence"
  | .spread => if r.flag.isSome
      then "state the limit in one section of the document and its exception in a different, later section, without repeating the limit there"
      else "state it in passing, inside a paragraph about something else"
  | .definedTerm => if r.flag.isSome
      then "name the members it exempts by a group name of your own (such as \"regular readers\"), defined once, in another paragraph, as the members with that status"
      else "state the counted quantity by a term of your own, defined once, in another paragraph"
  | .exampleOnly => "state it only through a worked example of a named person and numbers, never as a general rule; the example must leave the threshold unambiguous (a case one below it allowed, a case at it refused)" ++
      (if r.flag.isSome then ", and a second example shows the exempt member allowed" else "")
  | .twoWordings => "state it twice, in two different places, in different words meaning the same"
  | .folded => match partner with
      | some j => s!"state it in one sentence together with rule {j}"
      | none => "state it in one plain sentence"

/-- The writer's prompt: the rules the prose must state, each with its presentation. -/
def writerPrompt (rules : List Rule) (shown : List (Nat × Presentation)) : String :=
  let pairs := foldPairs shown
  let partner (id : Nat) : Option Nat :=
    (pairs.find? (·.1 == id)).map (·.2) <|> (pairs.find? (·.2 == id)).map (·.1)
  let items := rules.map fun r =>
    let p := (shown.lookup r.id).getD .plain
    s!"- Rule {r.id}: {ruleText r} How to write it: {instruction r p (partner r.id)}."
  "You manage a lending library and are writing the rules for your front-desk staff, the way a \
  non-technical person writes to colleagues: everyday language, paragraphs grouped by topic, a \
  short introduction, no list with a line per rule, no rule numbers, no identifiers or code. A \
  request is something a member asks the desk for; a member's counts (their loans, fines, holds \
  and so on) are what the library keeps for them. State every rule below with its exact numbers \
  and its exceptions, each written the way it says; add no rule, condition, number or exception \
  of your own, and leave none out. Give the whole document as `document`.\n\n# Rules\n\n" ++
    "\n".intercalate items

def documentSchema : Json :=
  Json.mkObj [("type", "object"),
    ("properties", Json.mkObj [("document", Json.mkObj [("type", "string")])]),
    ("required", Json.arr #["document"]), ("additionalProperties", false)]

def enumOf (xs : List String) : Json :=
  Json.mkObj [("type", "string"), ("enum", Json.arr (xs.map Json.str).toArray)]

/-- The extraction's schema: each rule in the generator's own vocabulary, so the comparison is
mechanical. -/
def extractionSchema : Json :=
  Json.mkObj [("type", "object"),
    ("properties", Json.mkObj [("rules", Json.mkObj [("type", "array"),
      ("items", Json.mkObj [("type", "object"),
        ("properties", Json.mkObj [("kind", enumOf kinds),
          ("measures", Json.mkObj [("type", "array"), ("items", enumOf measures)]),
          ("bound", Json.mkObj [("type", "integer")]),
          ("exempt", enumOf (flags ++ ["none"]))]),
        ("required", Json.arr #["kind", "measures", "bound", "exempt"]),
        ("additionalProperties", false)])])]),
    ("required", Json.arr #["rules"]), ("additionalProperties", false)]

def extractionPrompt (document : String) : String :=
  "Below is a lending library's document for its staff. List every rule in it that refuses a \
  member's request: the kind of request, the member's counts it adds up (one count, or two \
  counted together), the number at which the request is refused, and the member status exempt \
  from it, or `none`. Use only the schema's words: a request kind is its verb (a \"delivery \
  request\" is `deliver`), a count its plural noun (`days_late` for days late), and a group the \
  document defines is the status it is defined by. A rule the document states more than once, or \
  only through an example, is listed once. List nothing the document doesn't state.\n\n# Document\n\n" ++
    document

/-- An extraction's rules, or none when its answer isn't one. -/
def shapesOf (answer : Json) : Option (List Shape) := do
  let arr ← (answer.getObjValAs? (Array Json) "rules").toOption
  arr.toList.mapM fun j => do
    let kind ← (j.getObjValAs? String "kind").toOption
    let ms ← (j.getObjValAs? (Array String) "measures").toOption
    let bound ← (j.getObjValAs? Nat "bound").toOption
    let exempt ← (j.getObjValAs? String "exempt").toOption
    return Shape.norm ⟨kind, ms.toList, bound, if exempt == "none" then none else some exempt⟩

/-- A rule as `gvariants` saves the rules a variant's prose states, in `prose-rules.json`. -/
def ruleJson (r : Rule) : Json :=
  Json.mkObj [("id", Json.num r.id), ("kind", Json.str r.kind),
    ("measures", Json.arr (r.measures.map Json.str).toArray), ("bound", Json.num r.bound),
    ("flag", match r.flag with | some f => Json.str f | none => Json.null)]

def ruleOfJson (j : Json) : Option Rule := do
  let id ← (j.getObjValAs? Nat "id").toOption
  let kind ← (j.getObjValAs? String "kind").toOption
  let ms ← (j.getObjValAs? (Array String) "measures").toOption
  let bound ← (j.getObjValAs? Nat "bound").toOption
  let flag ← match j.getObjVal? "flag" with
    | .ok .null => some none
    | .ok (.str f) => some (some f)
    | _ => none
  return { id, kind, measures := ms.toList, bound, flag }

def Shape.describe (s : Shape) : String :=
  let f := match s.flag with | some f => s!", exempt {f}" | none => ""
  s!"{s.kind} on {" + ".intercalate s.measures} at {s.bound}{f}"

/-- A variant's writing: the document kept, if any; why each discarded writing was discarded; the
prompt; and what every call used. -/
structure Writing where
  document : Option String
  discarded : List String
  writings : Nat
  prompt : String
  usage : Usage.Usage

/-- The most writings a variant gets before it is left out. -/
def maxWritings : Nat := 3

/-- Write `rules` in their presentations and check the document with two blind extractions, up to
`maxWritings` times; a failed or malformed call discards its writing. -/
def writeFaithful (runner : Runner) (allowed : List Backend) (backend : Backend) (rules : List Rule)
    (shown : List (Nat × Presentation)) (scratch : System.FilePath) (timeoutMs : Nat) :
    IO Writing := do
  let prompt := writerPrompt rules shown
  let expected := rules.map shapeOf
  let mut used : Usage.Usage := {}
  let mut discarded : List String := []
  for attempt in List.range maxWritings do
    let dir := scratch / s!"writing{attempt + 1}"
    IO.FS.createDirAll (dir / "write")
    let (r, u) ← Usage.askRecorded "prose-writer" runner allowed backend
      { prompt, schema := documentSchema, timeoutMs } (dir / "write")
    used := used + u
    let doc ← match r with
      | .error f => discarded := discarded ++ [s!"writing {attempt + 1}: {f.describe}"]; continue
      | .ok o => match (o.answer.getObjValAs? String "document").toOption with
        | some d => pure d
        | none => discarded := discarded ++ [s!"writing {attempt + 1}: no document"]; continue
    let extract (name : String) := IO.asTask do
      IO.FS.createDirAll (dir / name)
      Usage.askRecorded "prose-extraction" runner allowed backend
        { prompt := extractionPrompt doc, schema := extractionSchema, timeoutMs } (dir / name)
    let t1 ← extract "extract1"
    let t2 ← extract "extract2"
    let mut faults : List String := []
    for (name, t) in [("extraction 1", t1), ("extraction 2", t2)] do
      let (e, ue) ← IO.ofExcept t.get
      used := used + ue
      match e with
      | .error f => faults := faults ++ [s!"{name}: {f.describe}"]
      | .ok o => match shapesOf o.answer with
        | none => faults := faults ++ [s!"{name}: no rule list"]
        | some got =>
          unless faithful expected got do
            let (lacks, adds) := differences expected got
            faults := faults ++ [s!"{name} lacks [{"; ".intercalate (lacks.map (·.describe))}] and adds [{"; ".intercalate (adds.map (·.describe))}]"]
    if faults.isEmpty then
      return { document := some doc, discarded, writings := attempt + 1, prompt, usage := used }
    discarded := discarded ++ [s!"writing {attempt + 1}: " ++ "; ".intercalate faults]
  return { document := none, discarded, writings := maxWritings, prompt, usage := used }

end SpecTools.Prose
