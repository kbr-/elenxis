import SpecTools.Generated
import SpecTools.Prose

/-!
The owners' tests: a small business owner, non-technical and imperfect, describes the program they
want, in prose of their own or in a conversation with a developer. The owner gets some rules wrong
the way such a person does (a flaw per rule, drawn from the seed and named in the key), and the
text goes through rounds of an adversarial reviewer who sees only the persona and the text and
lists what gives away that no such person wrote it. A text is kept when two blind extractions read
back every rule as the owner was told to state it, flaws included. The draws, the prompts and the
comparison are pure; `writeOwner` asks the model through a `Runner`, so tests script it.
-/

namespace SpecTools.Owners
open Lean SpecTools.Model SpecTools.Generated SpecTools.Synthetic

/-- What an owner gets wrong about one rule. -/
inductive Flaw where
  /-- The limit given roughly ("about a dozen"), never the exact number. -/
  | loose
  /-- The limit given twice, with two different numbers. -/
  | twoLimits
  /-- The rule's exception, which the business has, never mentioned. -/
  | forgotten
  /-- The number given, but whether the number itself is still allowed left unclear. -/
  | openBoundary
  deriving Repr, DecidableEq, Inhabited

def Flaw.name : Flaw → String
  | .loose => "loose limit"
  | .twoLimits => "two limits"
  | .forgotten => "forgotten exception"
  | .openBoundary => "open boundary"

def Flaw.all : List Flaw := [.loose, .twoLimits, .forgotten, .openBoundary]

/-- A flaw on rule `rule`. -/
structure Imperfection where
  rule : Nat
  flaw : Flaw
  deriving Repr, DecidableEq, Inhabited

/-- The rules a flaw can fall on: a forgotten exception needs a rule with one. -/
def Flaw.fits (f : Flaw) (r : Rule) : Bool := f != .forgotten || r.flag.isSome

/-- Each flaw in `fs` drawn from state `s` onto a rule of `rs` that fits it and no earlier flaw
took; a flaw no free rule fits falls on none. -/
def drawFlaws (rs : List Rule) : Nat → List Flaw → List Nat → List Imperfection
  | _, [], _ => []
  | s, f :: fs, taken =>
    match rs.filter fun r => f.fits r && !taken.contains r.id with
    | [] => drawFlaws rs (next s) fs taken
    | q :: qs =>
      let r := (q :: qs)[draw s (qs.length + 1)]'(Nat.mod_lt _ (Nat.succ_pos _))
      ⟨r.id, f⟩ :: drawFlaws rs (next s) fs (taken ++ [r.id])

/-- How many rules an owner's test has: two flawed and three stated clearly for the shared blind
spots, few enough that an owner would state them (a held-out judge read eight as "a full matrix of
eligibility rules"). -/
def ruleCount : Nat := 5

/-- The two flaw kinds an owner of the domain makes, chosen so each kind falls on some test; a
forgotten exception comes first, since only a rule with an exception can take it. -/
def _root_.SpecTools.Generated.Vocab.flawKinds (v : Vocab) : List Flaw :=
  match v.name with
  | "salon" => [.loose, .twoLimits]
  | "tailor" => [.forgotten, .openBoundary]
  | "bakery" => [.twoLimits, .openBoundary]
  | _ => [.forgotten, .loose, .twoLimits, .openBoundary]

/-- A test's flaws: one of each of `kinds`, on distinct rules, drawn from the seed. -/
def imperfections (seed : Nat) (rs : List Rule) (kinds : List Flaw) : List Imperfection :=
  drawFlaws rs (next (seed + 104723)) kinds []

/-- The shapes of an owners' test's shared blind spots: the library's that change the artifacts
(a twin exception changes the prose, which the owner's text replaces, so it would plant nothing),
and a limit every artifact moves, which any rule allows, so that rules without exceptions can
carry one. -/
def ownerShapes : List String := blindShapes.filter (· != "twin exception") ++ ["limit moved"]

/-- The plants of `shape` on the rules `rs` touching no rule of `touched`. -/
def freePlants (rs : List Rule) (extra : Rule) (shape : String) (touched : List Nat) :
    List GPlant :=
  (candidates rs extra shape).filter fun p => p.touches.all (!touched.contains ·)

/-- `count` blind spots on the rules `rs`, none touching `touched`: each step draws among the
shapes that still have a candidate, so a variant gets all of them while any shape can. -/
def drawOwnerPlants (rs : List Rule) (extra : Rule) : Nat → Nat → List Nat → List GPlant
  | _, 0, _ => []
  | s, k + 1, touched =>
    let s1 := next s
    let s2 := next s1
    let open_ := (ownerShapes.map fun shape => freePlants rs extra shape touched).filter
      (!·.isEmpty)
    let ps := open_.getD (draw s1 open_.length) []
    match ps[draw s2 ps.length]? with
    | none => []
    | some p => p :: drawOwnerPlants rs extra s2 k (touched ++ p.touches)

/-- Variant `index` of an owners' batch: the first `empty` plant nothing, the others three shared
blind spots, each on a rule no flaw took, applied to the plain views of every rule. The flaws live
in the owner's text alone, so the artifacts are those of the plants. -/
def ownerVariant (rs : List Rule) (extra : Rule) (flawed : List Nat) (seed index empty : Nat) :
    List View × List GPlant :=
  let s := next (seed + index * 7919)
  let count := if index < empty then 0 else 3
  let plants := drawOwnerPlants (rs.filter (!flawed.contains ·.id)) extra s count flawed
  (plants.foldl (fun vs p => p.apply vs) (rs.map View.plain), plants)

/-- The key's row for a flaw: the exception's row for a forgotten exception, the rule's otherwise. -/
def flawRow (i : Imperfection) : String :=
  if i.flaw == .forgotten then s!"r{i.rule}-exempt" else s!"r{i.rule}"

/-- A flaw's kind in the key: "imperfection: " and the flaw's name, counted apart from the shared
blind spots. -/
def flawKind (f : Flaw) : String := "imperfection: " ++ f.name

def isFlawKind (kind : String) : Bool := kind.startsWith "imperfection: "

/-- A flaw as a plant of the key: named by its row, so a finding naming the row finds it and is no
false alarm. -/
def flawPlant (rs : List Rule) (i : Imperfection) : Synthetic.Plant :=
  let clause := match rs.find? (·.id == i.rule) with
    | some r => match i.flaw, r.flag with
      | .forgotten, some f => flagSentence r f
      | _, _ => ruleSentence r
    | none => ""
  { kind := flawKind i.flaw, clause, edits := [], row := some (flawRow i) }

/-! The persona, the writer and the reviewer. -/

/-- Who writes: the owner's trade and what they want built. -/
def persona (v : Vocab) : String :=
  match v.name with
  | "salon" => "You own a small hair salon: three chairs, two stylists and a junior, mostly local \
      women and their kids, some regulars for twenty years. You are tired of the phone and the \
      paper diary and want an app or website where customers book themselves, and you want it to \
      say no to some bookings the way you and the girls do at the desk."
  | "tailor" => "You own a one-man alterations and tailoring shop with a seamstress two days a \
      week. Customers drop off clothes for hemming, taking in, repairs and suits; a few shops send \
      trade work. You want a simple website where people place alteration orders, and it should \
      turn some orders away the way you do at the counter."
  | "bakery" => "You run a home bakery from your kitchen, licensed, with your sister helping on \
      weekends: birthday and wedding cakes, cupcakes, cookie boxes, some wholesale to two cafes. \
      Orders come by Instagram messages and you lose track. You want a website for cake orders \
      that refuses some orders the way you would."
  | _ => "You run a small business and want a website where customers make requests, refusing \
      some of them the way you would."

/-- The other number a rule with two limits is given: the first natural number at least two above
its limit, as an owner would misremember it. -/
def secondLimit (b : Nat) : Nat :=
  ((List.range 40).map (b + 2 + ·)).find? Generated.natural |>.getD (b + 2)

/-- The owner's lines about one rule, with the flaw to commit on it, if any. -/
def flawInstruction (r : Rule) : Option Flaw → String
  | none => "say this one clearly, with its exact number"
  | some .loose => s!"you don't remember the exact number: say it roughly (\"about\", \"a dozen \
      or so\", \"a few\"), never the exact number {r.bound}"
  | some .twoLimits => s!"mention this limit in two different places and give a different number \
      each time, {r.bound} once and {secondLimit r.bound} the other time; you don't notice, so \
      never remark on it"
  | some .forgotten => "you forget its exception entirely: never mention who is exempt"
  | some .openBoundary => s!"give the number {r.bound}, but word it so it stays unclear whether \
      exactly {r.bound} is already refused or only more than {r.bound}; you don't see the \
      question yourself, so never point it out or ask about it"

/-- A rule in plain words, as the owner's notes give it to the writer. -/
def ownerRuleText (r : Rule) : String :=
  s!"Turn down a {r.kind} when the customer's {what r} reach {r.bound}" ++
    match r.flag with
    | some f => s!", except for {f} customers, who are never turned down by this."
    | none => "."

/-- Whether the owner writes alone or talks with a developer. -/
inductive Form where
  | prose
  | conversation
  deriving Repr, DecidableEq, Inhabited

def Form.name : Form → String
  | .prose => "prose"
  | .conversation => "conversation"

/-- The writer's prompt: the persona, the form, the rules with what the owner gets wrong about
each, and, for a conversation, notes on how real ones go. -/
def writerPrompt (v : Vocab) (form : Form) (rs : List Rule) (flaws : List Imperfection)
    (notes : String) : String :=
  let items := rs.map fun r =>
    s!"- {ownerRuleText r} How you get it across: \
      {flawInstruction r ((flaws.find? (·.rule == r.id)).map (·.flaw))}."
  let shape := match form with
    | .prose => "Write, in English, the job post or message you send a freelance developer asking \
        for this website. You are not technical and you type it quickly between customers, \
        maybe on your phone: typos you don't go back to fix, wherever your thumb slips and not \
        spread one per paragraph, a lowercase \"i\", missing apostrophes, run-on lines and \
        fragments, numbers as digits. Most of what you write is about the site itself: what \
        pages it has, your photos, how people order or book, paying, what you have now (a \
        Facebook page, a domain someone set up, a free theme you don't like), when you want it \
        by. When it should say no comes up only where it belongs: say each one in the middle of \
        what you are telling about that part of the site (booking, rush jobs, delivery, paying), \
        in passing, never gathered into a list or a block of their own. Give a limit as the \
        number you keep in mind, never followed by the first number that's refused (not \"5 is \
        the max, 6 no\"). You may half \
        fill it in like a form (a few labels with your answers after them) or just write it in \
        one go, whichever you would. Where you aren't sure of something, leave it, or ask the \
        developer to tell you. No software or maths words (never \"threshold\", \"parameter\", \
        \"validation\", \"edge case\"). Don't dress it up: no anecdote per rule, no colourful \
        detail added to sound real, no polished sign-off."
    | .conversation => "Write, in English, the transcript of a first call between you and a \
        developer you might hire. You know nothing about how software is made. The developer \
        asks questions and proposes concrete numbers and behaviours; you answer as you really \
        would: vague, sidetracked, sometimes changing your mind, sometimes saying you'd have to \
        ask your staff. Where a rule below says you don't remember a number or leave something \
        unclear, the developer may propose a value but you leave it open (\"whatever you think\", \
        \"I'd have to check\"). Some of the developer's suggestions you simply take (\"yeah, \
        two's about right\"), some you change, some you don't answer; a suggestion is not always \
        wrong, and not every number arrives as a correction. Say each number in a different way, \
        never the same emphatic pattern twice. The rules don't come up one service after another: \
        some come out while talking about something else, one only when the developer asks back \
        later, and most of the call is about the site and the business, not the rules. It is a \
        transcript of a real phone call, not a scene: false starts, \"um\", \"yeah\", half \
        sentences, both talking at once ([crosstalk]), a word lost ([inaudible]), the developer \
        fumbling too and asking plain questions, no crafted anecdotes or punchlines, nobody \
        summarizing the requirements. Speakers are \"Owner:\" and \"Developer:\"."
  s!"{persona v}\n\n{shape} Everything below must come across exactly as it says, the mistakes \
    included; add no other rule that turns customers away.\n\n# What you want\n\n" ++
    "\n".intercalate items ++
    (if notes.isEmpty then "" else match form with
      | .conversation => s!"\n\n# How real first calls go (notes from real ones)\n\n{notes}"
      | .prose => "\n\n# The message you start from\n\nA real owner of a business like yours once \
          sent this to a developer. Start from it: keep its words, its mistakes, its layout and \
          about its length, and change only what you must so that it is about your business and \
          says what you want above, each rule put the way this owner puts things. Drop what is \
          about their business and not yours.\n\n" ++ notes) ++
    "\n\nGive the whole text as `document`."

/-- The reviewer's prompt: the persona and the text, never the rules. -/
def reviewerPrompt (v : Vocab) (form : Form) (text : String) : String :=
  let what := match form with
    | .prose => "a message this person wrote to a developer about the program they want"
    | .conversation => "the transcript of a first call between this person and a developer"
  s!"Here is who supposedly wrote the text below:\n\n{persona v}\n\nThe text is said to be \
    {what}. Be adversarial: list every tell that it did not really come from such a person (or, \
    for a call, from two real people talking): order or structure too neat, a technical, \
    software or mathematical word, precision a busy owner wouldn't have, a voice too even or \
    too polished, turns too long or too tidy, a developer who doesn't ask or propose, anything \
    that reads like a model wrote it. Quote the passage behind each tell. Give them as `tells`, \
    an empty list if you find none. Then judge the whole: could a real person like this have \
    written it, as it stands? Give `could_be_real` true only if you would believe it came from \
    them.\n\n# Text to judge\n\n{text}"

def tellsSchema : Json :=
  Json.mkObj [("type", "object"),
    ("properties", Json.mkObj [("tells", Json.mkObj [("type", "array"),
      ("items", Json.mkObj [("type", "string")])]),
      ("could_be_real", Json.mkObj [("type", "boolean")])]),
    ("required", Json.arr #["tells", "could_be_real"]), ("additionalProperties", false)]

/-- The revision's prompt: the writer's brief, its draft, and what to fix. -/
def revisionPrompt (brief draft : String) (fixes : List String) : String :=
  s!"{brief}\n\n# Your draft\n\n{draft}\n\n# What to fix\n\nA reader found the following. \
    Rewrite the draft so none of it holds, keeping everything in \"What you want\" exactly as it \
    says, the mistakes included:\n\n" ++ "\n".intercalate (fixes.map ("- " ++ ·))

/-! The fidelity check: how a rule comes across, and the comparison. -/

/-- How an extraction reads a rule's limit. -/
inductive Mark where
  /-- One exact number at which the request is refused. -/
  | stated
  /-- No exact number, or unclear whether the number itself is refused. -/
  | loose
  /-- Two different numbers. -/
  | conflicting
  deriving Repr, DecidableEq, Inhabited

def Mark.name : Mark → String
  | .stated => "stated"
  | .loose => "loose"
  | .conflicting => "conflicting"

def Mark.ofName : String → Option Mark
  | "stated" => some .stated
  | "loose" => some .loose
  | "conflicting" => some .conflicting
  | _ => none

/-- A rule as an extraction reads it: its kind, its measures sorted, the number when stated, the
exempt status, and the mark. -/
structure Read where
  kind : String
  measures : List String
  bound : Option Nat
  flag : Option String
  mark : Mark
  deriving Repr, DecidableEq, Inhabited

def Read.norm (r : Read) : Read :=
  { r with measures := r.measures.mergeSort, bound := if r.mark == .stated then r.bound else none }

/-- How rule `r` must read with flaw `f`: a loose limit or an open boundary reads loose, two limits
conflicting, a forgotten exception with no exemption. -/
def expectedRead (r : Rule) (f : Option Flaw) : Read :=
  let mark := match f with
    | some .loose | some .openBoundary => Mark.loose
    | some .twoLimits => .conflicting
    | _ => .stated
  Read.norm ⟨r.kind, r.measures, some r.bound, if f == some .forgotten then none else r.flag, mark⟩

def expected (rs : List Rule) (flaws : List Imperfection) : List Read :=
  rs.map fun r => expectedRead r ((flaws.find? (·.rule == r.id)).map (·.flaw))

/-- An extraction reads the text as the owner was told to write it: the same rules, each once. -/
def faithful (exp got : List Read) : Bool := (exp.map Read.norm).isPerm (got.map Read.norm)

def Read.describe (r : Read) : String :=
  let b := match r.bound with | some b => s!" at {b}" | none => ""
  let f := match r.flag with | some f => s!", exempt {f}" | none => ""
  s!"{r.kind} on {" + ".intercalate r.measures}{b} ({r.mark.name}){f}"

def differences (exp got : List Read) : List Read × List Read :=
  let e := exp.map Read.norm
  let g := got.map Read.norm
  (e.filter (!g.contains ·), g.filter (!e.contains ·))

def readSchema (v : Vocab) : Json :=
  Json.mkObj [("type", "object"),
    ("properties", Json.mkObj [("rules", Json.mkObj [("type", "array"),
      ("items", Json.mkObj [("type", "object"),
        ("properties", Json.mkObj [("kind", Prose.enumOf v.kinds),
          ("measures", Json.mkObj [("type", "array"), ("items", Prose.enumOf v.measures)]),
          ("bound", Json.mkObj [("type", "integer")]),
          ("mark", Prose.enumOf ["stated", "loose", "conflicting"]),
          ("exempt", Prose.enumOf (v.flags ++ ["none"]))]),
        ("required", Json.arr #["kind", "measures", "bound", "mark", "exempt"]),
        ("additionalProperties", false)])])]),
    ("required", Json.arr #["rules"]), ("additionalProperties", false)]

def readPrompt (text : String) : String :=
  "Below is what a business owner said about the program they want. List every rule in it that \
  turns a customer's request away: the kind of request, the customer's counts it adds up (one \
  count, or two counted together), the number at which the request is turned away, how that \
  number comes across (`stated`: one exact number, and clearly whether that number itself is \
  turned away; `loose`: no exact number, or unclear whether the number itself is turned away; \
  `conflicting`: two different numbers given), and the customer status exempt from it, or `none`. \
  For a loose or conflicting limit give `bound` as the number closest to what was said. Use only \
  the schema's words, choosing the closest. A rule said more than once is listed once. List \
  nothing the text doesn't say.\n\n# Text\n\n" ++ text

def readsOf (answer : Json) : Option (List Read) := do
  let arr ← (answer.getObjValAs? (Array Json) "rules").toOption
  arr.toList.mapM fun j => do
    let kind ← (j.getObjValAs? String "kind").toOption
    let ms ← (j.getObjValAs? (Array String) "measures").toOption
    let bound ← (j.getObjValAs? Nat "bound").toOption
    let mark ← (j.getObjValAs? String "mark").toOption >>= Mark.ofName
    let exempt ← (j.getObjValAs? String "exempt").toOption
    return Read.norm ⟨kind, ms.toList, some bound, if exempt == "none" then none else some exempt, mark⟩

/-! The loop. -/

/-- The review rounds a text goes through. -/
def reviewRounds : Nat := 5

/-- The fidelity rounds a text gets before it is written again from the start. -/
def fidelityRounds : Nat := 3

/-- The starts a test gets before it is reported failed. -/
def maxStarts : Nat := 2

/-- One step of the loop: the text after it, and what the step was (written, revised for tells,
revised for fidelity) with the reader's list. -/
structure Step where
  what : String
  text : String
  notes : List String
  deriving Repr, Inhabited

/-- The held-out judge's prompt, which the loop's revisions never see: is the text an owner's (or a
real call) or a model's imitation? Its wording is the one whose verdicts on three owners' posts of
12 to 14 years ago were "owner" (the task's theory). -/
def judgePrompt (form : Form) (text : String) : String :=
  match form with
  | .prose => s!"You are screening messages that a freelance web developer received from small \
      business owners asking for a website or an app. Some of these messages were really written \
      by the owners; some were generated by an AI model imitating such an owner. Read the message \
      below and decide which it is. Give `verdict` as \"owner\" or \"ai\", `confidence` from 0 to \
      100 for that verdict, and `reasons`, the passages that decided it, quoted.\n\n# The \
      message\n\n{text}"
  | .conversation => s!"You are screening transcripts of first calls between a freelance web \
      developer and small business owners who want a website or an app. Some transcripts are of \
      real calls; some were generated by an AI model imitating such a call. Read the transcript \
      below and decide which it is. Give `verdict` as \"real\" or \"ai\", `confidence` from 0 to \
      100 for that verdict, and `reasons`, the passages that decided it, quoted.\n\n# The \
      transcript\n\n{text}"

def judgeSchema : Json :=
  Json.mkObj [("type", "object"),
    ("properties", Json.mkObj [("verdict", Json.mkObj [("type", "string")]),
      ("confidence", Json.mkObj [("type", "integer")]),
      ("reasons", Json.mkObj [("type", "array"), ("items", Json.mkObj [("type", "string")])])]),
    ("required", Json.arr #["verdict", "confidence", "reasons"]), ("additionalProperties", false)]

/-- The judge's verdict and confidence, or none when its answer has neither. -/
def judgeOf (r : Except Failure Outcome) : Option (String × Nat) :=
  match r with
  | .error _ => none
  | .ok o => match (o.answer.getObjValAs? String "verdict").toOption,
      (o.answer.getObjValAs? Nat "confidence").toOption with
    | some v, some c => some (v, c)
    | _, _ => none

/-- The judge's quoted reasons, empty when its answer has none. -/
def judgeReasonsOf (r : Except Failure Outcome) : List String :=
  match r with
  | .error _ => []
  | .ok o => ((o.answer.getObjValAs? (Array String) "reasons").toOption.getD #[]).toList

/-- How many times the writer revises against the development judge's reasons: none, since on the
ninth writing the salon's text scored 76.3 by the second judge as first written, 86.0 after the
review rounds and 71 after three such revisions (the task's theory). -/
def judgeRounds : Nat := 0

/-- The development judge's prompt, the loop's to learn from: the bar's question (a probability)
in other words than the second judge's, which the loop never sees. -/
def devJudgePrompt (form : Form) (text : String) : String :=
  match form with
  | .prose => s!"Here is a message a freelancer got through their contact form from a small \
      business owner who wants a website made. If you had to bet, how likely is it that the owner \
      wrote this themselves, rather than having it written by an AI? Answer `human_probability` \
      from 0 to 100, and in `why` list what in the message makes it read as a person's or as \
      generated, quoting it.\n\n---\n\n{text}"
  | .conversation => s!"Here is what is said to be a transcript of a first phone call between a \
      freelancer and a small business owner who wants a website made. If you had to bet, how \
      likely is it that this was a real call, rather than written by an AI? Answer \
      `human_probability` from 0 to 100, and in `why` list what in it makes it read as a real call \
      or as generated, quoting it.\n\n---\n\n{text}"

/-- The second judge's prompt, which the loop never sees: how likely a person running the business
typed the text (for a call: that it transcribes a real call), 0 to 100. -/
def testJudgePrompt (form : Form) (text : String) : String :=
  match form with
  | .prose => s!"A web developer received the message below from someone asking for a website. \
      Estimate how likely it is that a person running the business typed it themselves, as \
      opposed to an AI tool producing it. Give `human_probability` from 0 to 100 and `why`, the \
      passages that moved your estimate most, quoted.\n\n---\n\n{text}"
  | .conversation => s!"Below is said to be the transcript of a first call between a web developer \
      and a person running a small business who wants a website. Estimate how likely it is that \
      it transcribes a real call, as opposed to an AI tool producing it. Give `human_probability` \
      from 0 to 100 and `why`, the passages that moved your estimate most, quoted.\n\n---\n\n{text}"

def testJudgeSchema : Json :=
  Json.mkObj [("type", "object"),
    ("properties", Json.mkObj [("human_probability", Json.mkObj [("type", "integer")]),
      ("why", Json.mkObj [("type", "array"), ("items", Json.mkObj [("type", "string")])])]),
    ("required", Json.arr #["human_probability", "why"]), ("additionalProperties", false)]

def humanProbabilityOf (r : Except Failure Outcome) : Option Nat :=
  match r with
  | .error _ => none
  | .ok o => (o.answer.getObjValAs? Nat "human_probability").toOption

def whyOf (r : Except Failure Outcome) : List String :=
  match r with
  | .error _ => []
  | .ok o => ((o.answer.getObjValAs? (Array String) "why").toOption.getD #[]).toList

/-- The bar: the second judge's mean probability at least the lowest it gave a human post (the
theory's calibration on three owners' posts, 90; the salon post's three samples 90, 92, 90). -/
def testBar : Nat := 90

/-- How many samples of the second judge the bar averages. -/
def testSamples : Nat := 3

/-- Of a test's writings, by their development judge's scores (none for a writing with no kept
text or no score), the index of the first with the highest score; none when no writing has one. -/
def bestIndex (scores : List (Option Nat)) : Option Nat := do
  let m ← (scores.filterMap id).max?
  scores.findIdx? (· == some m)

/-- The index of the first writing Tells read as a human's. -/
def firstHuman : List Bool → Option Nat
  | [] => none
  | true :: _ => some 0
  | false :: vs => (firstHuman vs).map (· + 1)

theorem firstHuman_reads_human : ∀ (vs : List Bool) (i : Nat), firstHuman vs = some i → vs[i]? = some true
  | [], _, h => by simp [firstHuman] at h
  | true :: _, i, h => by simp [firstHuman] at h; subst h; rfl
  | false :: vs, i, h => by
    simp only [firstHuman, Option.map_eq_some_iff] at h
    obtain ⟨j, hj, rfl⟩ := h
    simpa using firstHuman_reads_human vs j hj

theorem firstHuman_none_all_model : ∀ (vs : List Bool), firstHuman vs = none → ∀ b ∈ vs, b = false
  | [], _ => by simp
  | true :: _, h => by simp [firstHuman] at h
  | false :: vs, h => by
    simp only [firstHuman, Option.map_eq_none_iff] at h
    intro b hb
    simp only [List.mem_cons] at hb
    rcases hb with rfl | hb
    · rfl
    · exact firstHuman_none_all_model vs h b hb

/-- The writings a suite's test makes at most. -/
def suiteWritings : Nat := 3

/-- What a test of `owners-suite` does next, from Tells' verdicts on its writings so far. -/
inductive SuiteStep where
  | write
  | keep (index : Nat)
  | none
  deriving DecidableEq, Repr

/-- Keep the first writing Tells reads as a human's; else write another, up to `suiteWritings`. -/
def suiteNext (vs : List Bool) : SuiteStep :=
  match firstHuman vs with
  | some i => .keep i
  | none => if vs.length < suiteWritings then .write else .none

theorem suiteNext_keeps_human (vs : List Bool) (i : Nat) (h : suiteNext vs = .keep i) :
    vs[i]? = some true := by
  unfold suiteNext at h
  cases hf : firstHuman vs with
  | some j => rw [hf] at h; cases h; exact firstHuman_reads_human vs i hf
  | none =>
    rw [hf] at h
    by_cases hl : vs.length < suiteWritings <;> simp [hl] at h

theorem suiteNext_bounded (vs : List Bool) (h : suiteWritings ≤ vs.length) : suiteNext vs ≠ .write := by
  unfold suiteNext
  cases firstHuman vs with
  | some _ => simp
  | none =>
    have hl : ¬ vs.length < suiteWritings := by omega
    simp [hl]

theorem suiteNext_writes_after_models (vs : List Bool) (hm : ∀ b ∈ vs, b = false)
    (h : vs.length < suiteWritings) : suiteNext vs = .write := by
  have : firstHuman vs = none := by
    induction vs with
    | nil => rfl
    | cons b vs ih =>
      have hb := hm b (by simp); subst hb
      simp [firstHuman, ih (fun c hc => hm c (by simp [hc])) (by simp at h; omega)]
  simp [suiteNext, this, h]

/-- A line of `tells verdicts`: the text's name and whether Tells read it as a human's. -/
def parseVerdict (line : String) : Option (String × Bool) :=
  match line.splitOn ": score " with
  | [n, rest] =>
    if rest.endsWith ", human" then some (n, true)
    else if rest.endsWith ", model" then some (n, false) else none
  | _ => none

theorem parseVerdict_reads :
    parseVerdict "o12-salon-a-0: score 0.920000, human" = some ("o12-salon-a-0", true) ∧
    parseVerdict "o12-tailor-b-0: score 0.400000, model" = some ("o12-tailor-b-0", false) ∧
    parseVerdict "o12-x-0: not judged" = none ∧
    parseVerdict "threshold (second lowest of 93 calibration scores) 0.920000" = none := by native_decide

/-- A decimal score as `tells verdicts` prints it ("0.700000"), in hundredths, rounded down. -/
def hundredths (s : String) : Option Nat :=
  match s.splitOn "." with
  | [w, f] => do
    let w ← w.toNat?
    let f ← (String.ofList ((f.toList ++ ['0', '0']).take 2)).toNat?
    return w * 100 + f
  | [w] => (· * 100) <$> w.toNat?
  | _ => none

/-- A line of `tells verdicts` with its score: the name, whether Tells read it as a human's, and
the score in hundredths. -/
def parseScored (line : String) : Option (String × Bool × Nat) := do
  let (n, h) ← parseVerdict line
  let rest ← (line.splitOn ": score ")[1]?
  let s ← hundredths ((rest.splitOn ", ").headD "")
  return (n, h, s)

theorem parseScored_reads :
    parseScored "o12-salon-a-0: score 0.700000, model" = some ("o12-salon-a-0", false, 70) ∧
    parseScored "o12-salon-b-0: score 0.920000, human" = some ("o12-salon-b-0", true, 92) ∧
    parseScored "o12-x-0: not judged" = none := by native_decide

/-- The writing a test of `owners-suite` keeps: the one `suiteNext` keeps, or, with `best` and
none passing, the highest-scored; a writing with no score is never kept. -/
def suiteKeep (best : Bool) (vs : List (Bool × Option Nat)) : Option Nat :=
  match suiteNext (vs.map (·.1)) with
  | .keep i => some i
  | _ => if best then bestIndex (vs.map (·.2)) else none

theorem suiteKeep_strict_keeps_human (vs : List (Bool × Option Nat)) (i : Nat)
    (h : suiteKeep false vs = some i) : (vs.map (·.1))[i]? = some true := by
  unfold suiteKeep at h
  cases hs : suiteNext (vs.map (·.1)) with
  | keep j => rw [hs] at h; cases h; exact suiteNext_keeps_human _ i hs
  | write => rw [hs] at h; simp at h
  | none => rw [hs] at h; simp at h

theorem suiteKeep_best_highest :
    suiteKeep true [(false, some 70), (false, some 40), (false, some 55)] = some 0 ∧
    suiteKeep true [(false, some 40), (true, some 92)] = some 1 ∧
    suiteKeep false [(false, some 70), (false, some 40), (false, some 55)] = none := by native_decide

/-- The mean of the samples, rounded down; none for no sample. -/
def meanOf (xs : List Nat) : Option Nat :=
  if xs.isEmpty then none else some (xs.sum / xs.length)

def passesBar : Option Nat → Bool
  | some p => p ≥ testBar
  | none => false

/-- Whether a held-out verdict passes the bar: "owner" for prose, "real" for a call. -/
def passesJudge (form : Form) : Option (String × Nat) → Bool
  | some (v, _) => v == (match form with | .prose => "owner" | .conversation => "real")
  | none => false

/-- A test's writing: the text kept, if any; every step; the last review's tells; the extractions'
faults per fidelity check; and what every call used. -/
structure Writing where
  text : Option String
  steps : List Step
  lastTells : List String
  /-- The last review's verdict on the kept text: could a person of the persona have written it. -/
  lastVerdict : Option Bool
  /-- The held-out judge's verdict on the kept text and its confidence: the test's bar. -/
  heldOut : Option (String × Nat) := none
  /-- The passages the judge quoted for its verdict. -/
  heldOutReasons : List String := []
  /-- The second judge's probability that the owner typed the text, the test's bar; the loop
  never reads it. -/
  testJudge : Option Nat := none
  testJudgeWhy : List String := []
  /-- The second judge's samples, whose mean (rounded down) is `testJudge`. -/
  testSamples : List Nat := []
  /-- The development judge's score of the kept text, by which a test's writings are chosen. -/
  devJudge : Option Nat := none
  faults : List (List String)
  brief : String
  usage : Usage.Usage

/-- The writer's text, or why there is none. -/
def documentOf (r : Except Failure Outcome) : Except String String :=
  match r with
  | .error f => .error f.describe
  | .ok o => match (o.answer.getObjValAs? String "document").toOption with
    | some d => .ok d
    | none => .error "no document"

/-- A review's tells and its verdict, whether a person of the persona could have written the text. -/
def tellsOf (r : Except Failure Outcome) : Except String (List String × Bool) :=
  match r with
  | .error f => .error f.describe
  | .ok o => match (o.answer.getObjValAs? (Array String) "tells").toOption,
      (o.answer.getObjValAs? Bool "could_be_real").toOption with
    | some ts, some real => .ok (ts.toList, real)
    | _, _ => .error "no tells or no verdict"

/-- The fidelity check on a text however it was written (by `writeOwner`, or by hand from a real
owner's post): two blind extractions, started together, each compared with the reads the rules and
flaws require (`expected`); the faults, none when both read the text faithfully, and what the calls
used. -/
def checkFidelity (runner : Runner) (allowed : List Backend) (backend : Backend) (v : Vocab)
    (rs : List Rule) (flaws : List Imperfection) (text : String) (scratch : System.FilePath)
    (timeoutMs : Nat) : IO (List String × Usage.Usage) := do
  let exp := expected rs flaws
  let read (n : Nat) : IO (Except Failure Outcome × Usage.Usage) := do
    let dir := scratch / s!"reading{n}"
    IO.FS.createDirAll dir
    Usage.askRecorded "owner-reader" runner allowed backend
      { prompt := readPrompt text, schema := readSchema v, timeoutMs } dir
  let t1 ← IO.asTask (read 1)
  let t2 ← IO.asTask (read 2)
  let mut faults : List String := []
  let mut used : Usage.Usage := {}
  for (name, t) in [("reading 1", t1), ("reading 2", t2)] do
    let (r, u) ← IO.ofExcept t.get
    used := used + u
    match r with
    | .error f => faults := faults ++ [s!"{name}: {f.describe}"]
    | .ok o => match readsOf o.answer with
      | none => faults := faults ++ [s!"{name}: no rule list"]
      | some got =>
        unless faithful exp got do
          let (lacks, adds) := differences exp got
          faults := faults ++ [s!"{name} misses [{"; ".intercalate (lacks.map (·.describe))}] \
            and reads [{"; ".intercalate (adds.map (·.describe))}]"]
  return (faults, used)

/-- The prose tests `owners-suite` runs, each with its seed; the test's name is its vocabulary's. -/
def suiteTests : List (String × Nat) := [("salon", 20261120), ("tailor", 20261121), ("bakery", 20261122)]

/-- Write the test's text, put it through `reviewRounds` rounds of review and revision, then check
it with two blind extractions, revising for their differences up to `fidelityRounds` times, and
review the text so kept once more, for the record, the verdict and tells the result reports;
failing, start again, up to `maxStarts` starts. A failed call fails the start it is in. -/
def writeOwner (runner : Runner) (allowed : List Backend) (backend : Backend) (v : Vocab)
    (form : Form) (rs : List Rule) (flaws : List Imperfection) (notes : String)
    (scratch : System.FilePath) (timeoutMs : Nat) (judgeRounds : Nat := judgeRounds) :
    IO Writing := do
  let brief := writerPrompt v form rs flaws notes
  let used ← IO.mkRef ({} : Usage.Usage)
  let calls ← IO.mkRef (0 : Nat)
  let ask (tool prompt : String) (schema : Json) : IO (Except Failure Outcome) := do
    let n ← calls.modifyGet fun c => (c + 1, c + 1)
    let dir := scratch / s!"call{n}"
    IO.FS.createDirAll dir
    let (r, u) ← Usage.askRecorded tool runner allowed backend { prompt, schema, timeoutMs } dir
    used.modify (· + u)
    return r
  let mut steps : List Step := []
  let mut faultLog : List (List String) := []
  let mut lastTells : List String := []
  let mut lastVerdict : Option Bool := none
  for start in List.range maxStarts do
    let label := s!"start {start + 1}"
    let first ← ask "owner-writer" brief Prose.documentSchema
    let mut text ← match documentOf first with
      | .ok d => pure d
      | .error e => steps := steps ++ [⟨s!"{label}: writing failed", "", [e]⟩]; continue
    steps := steps ++ [⟨s!"{label}: written", text, []⟩]
    let mut broken := false
    for round in List.range reviewRounds do
      match tellsOf (← ask "owner-reviewer" (reviewerPrompt v form text) tellsSchema) with
      | .error e =>
        steps := steps ++ [⟨s!"{label}: review {round + 1} failed", text, [e]⟩]
        broken := true
        break
      | .ok (tells, _) =>
        let revised ← ask "owner-writer" (revisionPrompt brief text tells) Prose.documentSchema
        match documentOf revised with
        | .error e =>
          steps := steps ++ [⟨s!"{label}: revision {round + 1} failed", text, [e]⟩]
          broken := true
          break
        | .ok d =>
          text := d
          steps := steps ++ [⟨s!"{label}: revised after review {round + 1}", d, tells⟩]
    if broken then continue
    -- The development judge's reasons are the loop's to learn from: under the bar, the writer
    -- revises against them, up to `judgeRounds` times, before the fidelity checks.
    for round in List.range judgeRounds do
      let judged ← ask "owner-dev-judge" (devJudgePrompt form text) testJudgeSchema
      if passesBar (humanProbabilityOf judged) then break
      let reasons := whyOf judged
      if reasons.isEmpty then break
      let fixes := reasons.map fun r => s!"a reader took your text for a model's imitation: {r}"
      match documentOf (← ask "owner-writer" (revisionPrompt brief text fixes) Prose.documentSchema) with
      | .error e => steps := steps ++ [⟨s!"{label}: judge revision {round + 1} failed", text, [e]⟩]; break
      | .ok d =>
        text := d
        steps := steps ++ [⟨s!"{label}: revised after judge {round + 1}", d, reasons⟩]
    for check in List.range (fidelityRounds + 1) do
      let (faults, u) ← checkFidelity runner allowed backend v rs flaws text
        (scratch / s!"fidelity{start + 1}-{check + 1}") timeoutMs
      used.modify (· + u)
      faultLog := faultLog ++ [faults]
      if faults.isEmpty then
        match tellsOf (← ask "owner-reviewer" (reviewerPrompt v form text) tellsSchema) with
        | .error e => steps := steps ++ [⟨s!"{label}: last review failed", text, [e]⟩]; break
        | .ok (tells, real) =>
          let judged ← ask "owner-judge" (judgePrompt form text) judgeSchema
          let dev ← ask "owner-dev-judge" (devJudgePrompt form text) testJudgeSchema
          -- The bar's judge three times at once, its samples varying by a few points.
          let tasks ← (List.range testSamples).mapM fun _ =>
            IO.asTask (ask "owner-test-judge" (testJudgePrompt form text) testJudgeSchema)
          let mut samples : List Nat := []
          let mut why : List String := []
          for t in tasks do
            let r ← IO.ofExcept t.get
            if let some p := humanProbabilityOf r then samples := samples ++ [p]
            if why.isEmpty then why := whyOf r
          return { text := some text, steps, lastTells := tells, lastVerdict := some real,
                   heldOut := judgeOf judged, heldOutReasons := judgeReasonsOf judged,
                   devJudge := humanProbabilityOf dev, testSamples := samples,
                   testJudge := meanOf samples, testJudgeWhy := why,
                   faults := faultLog, brief, usage := ← used.get }
      if check == fidelityRounds then break
      let fixes := faults.map fun f => s!"a reader of your text got this wrong: {f}"
      match documentOf (← ask "owner-writer" (revisionPrompt brief text fixes) Prose.documentSchema) with
      | .error e => steps := steps ++ [⟨s!"{label}: fidelity revision failed", text, [e]⟩]; break
      | .ok d =>
        text := d
        steps := steps ++ [⟨s!"{label}: revised after fidelity check {check + 1}", d, faults⟩]
  return { text := none, steps, lastTells, lastVerdict, faults := faultLog, brief,
           usage := ← used.get }

/-! The table: the five rows the user asked for, from the saved results. -/

/-- One run's saved result, as `run` and `gapsrun` write it: what its key planted and it found, its
false alarms, and its usage (the agent's and, for an arm running the tools, the tools'). -/
structure RunResult where
  blindPlanted : Nat
  blindFound : Nat
  flawsPlanted : Nat
  flawsFound : Nat
  alarms : Nat
  millis : Nat
  tokens : Nat
  outputTokens : Nat
  deriving Repr, Inhabited

def tokensOf (u : Usage.Usage) : Nat :=
  u.input.known + u.cacheWrite.known + u.cacheRead.known + u.output.known

/-- A saved result line, or none for a failed run's. -/
def runResult (j : Json) : Option RunResult := do
  let found ← (j.getObjValAs? (List String) "found_kinds").toOption
  let missed ← (j.getObjValAs? (List String) "missed_kinds").toOption
  let alarms ← (j.getObjValAs? Nat "false_alarms").toOption
  let usage := ((j.getObjVal? "usage").toOption.bind Usage.fromJson?).getD {}
  let tools := ((j.getObjVal? "tools_usage").toOption.bind Usage.fromJson?).getD {}
  let blind (l : List String) := (l.filter (· == "shared blind spot")).length
  let flaws (l : List String) := (l.filter isFlawKind).length
  return { blindPlanted := blind found + blind missed, blindFound := blind found,
           flawsPlanted := flaws found + flaws missed, flawsFound := flaws found, alarms,
           millis := usage.millis, tokens := tokensOf usage + tokensOf tools,
           outputTokens := usage.output.known + tools.output.known }

/-- A completed arm has one scorable success per variant. Earlier errors remain in the journal
and do not supply a score. -/
def completedRow (arm : String) (variants : Nat) (lines : List String) : Option (List Json) := do
  let entries ← (lines.filter (fun l => !l.trimAscii.isEmpty)).mapM fun line => do
    let j ← (Json.parse line).toOption
    let i ← (j.getObjValAs? Nat "variant").toOption
    let recordedArm ← (j.getObjValAs? String "arm").toOption
    guard (i < variants && recordedArm == arm)
    if (j.getObjVal? "error").isOk then
      let _ ← (j.getObjValAs? String "error").toOption
      return none
    let _ ← runResult j
    return some (i, j)
  let scores := entries.filterMap id
  guard ((scores.map Prod.fst).mergeSort == List.range variants)
  return scores.map Prod.snd

private def successfulLine (arm : String) (variant : Nat) : String :=
  (Json.mkObj [("variant", toJson variant), ("arm", .str arm), ("found_kinds", .arr #[]),
    ("missed_kinds", .arr #[]), ("false_alarms", toJson (0 : Nat))]).compress

theorem completedRow_exact_coverage :
    (completedRow "tools" 2 [successfulLine "tools" 1, successfulLine "tools" 0, " "]).isSome = true ∧
    (completedRow "tools" 2 [successfulLine "tools" 0, successfulLine "tools" 0]).isNone = true ∧
    (completedRow "tools" 2 [successfulLine "tools" 0]).isNone = true ∧
    (completedRow "tools" 2 [successfulLine "tools" 0, successfulLine "ledger" 1]).isNone = true ∧
    (completedRow "tools" 2 [successfulLine "tools" 0, successfulLine "tools" 2]).isNone = true := by
  native_decide

theorem completedRow_allows_successful_retry :
    ((completedRow "gaps" 1
      ["{\"arm\":\"gaps\",\"variant\":0,\"error\":\"exit 1\"}", successfulLine "gaps" 0]).map
      List.length) = some 1 ∧
    (completedRow "gaps" 1 ["{\"arm\":\"gaps\",\"variant\":0,\"error\":\"exit 1\"}"]).isNone = true ∧
    (completedRow "gaps" 1 ["{\"arm\":\"gaps\",\"variant\":0}"]).isNone = true ∧
    (completedRow "gaps" 1 ["unparseable", successfulLine "gaps" 0]).isNone = true := by
  native_decide

/-- A row of the table: runs, blind spots found of those planted, imperfections found of those
planted, false alarms, and time and tokens per run (totals divided by the runs, rounded down);
`failed` the runs that gave no result. -/
def tableRow (name : String) (rs : List RunResult) (failed : Nat) : String :=
  let sum (f : RunResult → Nat) := (rs.map f).sum
  let per (f : RunResult → Nat) := if rs.isEmpty then 0 else sum f / rs.length
  s!"| {name} | {rs.length} | {sum (·.blindFound)} of {sum (·.blindPlanted)} | \
    {sum (·.flawsFound)} of {sum (·.flawsPlanted)} | {sum (·.alarms)} | \
    {per (·.millis) / 1000} s | {per (·.tokens)} | {per (·.outputTokens)} | {failed} |"

def tableHeader : String :=
  "| Row | Runs | Blind spots found | Imperfections found | False alarms | Time per run | \
  Tokens per run | Output tokens per run | Failed runs |\n|---|---|---|---|---|---|---|---|---|"

/-- The five rows: `gaps` alone on the variants with blind spots, `gaps` on those with none (the
control), and the three agents' arms on every variant. Each list holds a row's saved lines. -/
def table (gaps baseline ledger tools : List Json) : String :=
  let results (ls : List Json) := ls.filterMap runResult
  let failed (ls : List Json) := ls.length - (results ls).length
  let gr := results gaps
  "\n".intercalate [tableHeader,
    tableRow "`gaps` alone" (gr.filter (·.blindPlanted > 0)) (failed gaps),
    tableRow "`gaps` on the no-plant variants" (gr.filter (·.blindPlanted == 0)) 0,
    tableRow "baseline arm" (results baseline) (failed baseline),
    tableRow "ledger arm" (results ledger) (failed ledger),
    tableRow "tools arm" (results tools) (failed tools)]

end SpecTools.Owners
