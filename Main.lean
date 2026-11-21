import SpecTools
import SpecTools.DraftHook

/-- The commands, each with what it does. -/
def commands : List (String × String) := [
  ("ask", "ask one question of a backend: ask HARNESS MODEL SCHEMA-FILE PROMPT-FILE [TIMEOUT-MS]"),
  ("clauses", "extract a prose file's clauses twice and print the differences: \
    clauses HARNESS MODEL PROSE-FILE [TIMEOUT-MS]"),
  ("draft-check", "check complete coverage before model review: draft-check INVENTORY DRAFT"),
  ("draft-hook", "check a hook payload and task roots from stdin: draft-hook PYTHON INVENTORY-BRIDGE"),
  ("draft-hook-json", "structured hook verdict: draft-hook-json PYTHON INVENTORY-BRIDGE"),
  ("draft-review", "review a complete coverage draft: draft-review HARNESS MODEL PROSE INVENTORY DRAFT"),
  ("synthetic", "write a batch of variants of the loans fixture with planted gaps, the key apart: \
    synthetic SEED COUNT EMPTY FIXTURE-DIR OUT-DIR"),
  ("check", "run one spec tool on the synthetic variant in the current directory, with the root and \
    model its spec-tools.json names: check audit|tests|gaps|clauses")
]

/-- The loans fixture's files a variant is made of. -/
def fixtureFiles : List String := ["loans.md", "Loans.lean", "loans.py", "test_loans.py"]

/-- The domain a command's `vocab=NAME` argument names (the library without one), and the other
arguments. -/
def splitVocab (args : List String) : Except String (SpecTools.Generated.Vocab × List String) :=
  let (named, rest) := args.partition (·.startsWith "vocab=")
  match named with
  | [] => .ok (.library, rest)
  | [a] => match SpecTools.Generated.Vocab.named (a.drop 6).toString with
    | some v => .ok (v, rest)
    | none => .error s!"{a}: no such domain; the domains are \
        {SpecTools.Generated.Vocab.all.map (·.name)}"
  | _ => .error "give vocab=NAME once"

/-- A batch's domain, from the `vocab` file gvariants writes beside its key (the library when the
batch predates it). -/
def batchVocab (outDir : String) : IO SpecTools.Generated.Vocab := do
  let f := System.FilePath.mk outDir / "vocab"
  unless ← f.pathExists do return .library
  let name := (← IO.FS.readFile f).trimAscii.toString
  match SpecTools.Generated.Vocab.named name with
  | some v => return v
  | none => throw (IO.userError s!"{f} names {name}, no domain")

open SpecTools.Synthetic in
def synthetic (args : List String) : IO UInt32 := do
  let (vocab, args) ← match splitVocab args with
    | .ok r => pure r
    | .error e => IO.eprintln e; return 2
  match args with
  | ["generate", seeds, ns, outDir] =>
    -- The complete generated fixture of N rules from SEED, for each seed and N of the comma-separated
    -- lists, in OUT-DIR/sSEED-nN: the controls generated variants are made from.
    let some seeds := (seeds.splitOn ",").mapM String.toNat? | IO.eprintln "SEEDS are numbers"; return 2
    let some ns := (ns.splitOn ",").mapM String.toNat? | IO.eprintln "NS are numbers"; return 2
    for seed in seeds do
      for n in ns do
        let rs := SpecTools.Generated.rulesOf seed n vocab
        let dir := System.FilePath.mk outDir / s!"s{seed}-n{n}"
        IO.FS.createDirAll dir
        for (f, text) in SpecTools.Generated.files (rs.map SpecTools.Generated.View.plain) do
          IO.FS.writeFile (dir / f) text
        let flagged := (rs.filter (·.flag.isSome)).length
        let sums := (rs.filter (·.measures.length > 1)).length
        IO.println s!"{dir}: {rs.length} rules ({flagged} with an exception, {sums} over two measures), {rs.length + flagged} clauses"
    return 0
  | ["gplants", seed, n, outDir] =>
    -- One variant per plant shape over the fixture of N rules from SEED, each plant alone at a drawn
    -- rule, and the negative control `omitted`, a rule's theorem left out with no row naming one.
    let some seed := seed.toNat? | IO.eprintln "SEED is a number"; return 2
    let some n := n.toNat? | IO.eprintln "N is a number"; return 2
    let all := SpecTools.Generated.rules seed (n + 1) vocab
    let rs := all.take n
    let extra := all.getLastD default
    let plain := rs.map SpecTools.Generated.View.plain
    let mut key : List String := []
    for (shape, i) in SpecTools.Generated.shapes.zipIdx do
      let cs := SpecTools.Generated.candidates rs extra shape
      if cs.isEmpty then IO.eprintln s!"{shape}: no rule allows it"; return 1
      let p := cs[SpecTools.Synthetic.draw (SpecTools.Synthetic.next (seed + i)) cs.length]!
      let dir := System.FilePath.mk outDir / s!"p{i}"
      IO.FS.createDirAll dir
      for (f, text) in SpecTools.Generated.files (p.apply plain) do IO.FS.writeFile (dir / f) text
      key := key ++ [s!"\{\"variant\": {i}, \"shape\": {shape.quote}, \"plants\": [\{\"kind\": {p.kind.quote}, \"clause\": {p.clause.quote}}]}"]
    let dir := System.FilePath.mk outDir / "omitted"
    IO.FS.createDirAll dir
    let r := rs.headD default
    for (f, text) in SpecTools.Generated.files (SpecTools.Generated.onRule r.id
        (fun v => { v with omitTheorem := true }) plain) do
      IO.FS.writeFile (dir / f) text
    IO.FS.writeFile (System.FilePath.mk outDir / "key.jsonl") ("\n".intercalate key ++ "\n")
    IO.println s!"{SpecTools.Generated.shapes.length} single-plant variants and the control `omitted` (rule r{r.id}) in {outDir}"
    return 0
  | ["gvariants", seed, n, count, empty, outDir]
  | ["gvariants", seed, n, count, empty, outDir, "blind"]
  | ["gvariants", seed, n, count, empty, outDir, "blind", "hard"] =>
    -- A batch of COUNT variants of the fixture of N rules from SEED, the first EMPTY with no plant,
    -- in the loans batches' layout, so `synthetic run` takes it; `blind` gives each three shared
    -- blind spots and nothing else (the scaling measure). The key names each rule's presentation
    -- for the person-prose writer, drawn from all six, or from the hard three with `hard`.
    let blindOnly := args.contains "blind"
    let offered := if args.contains "hard" then SpecTools.Generated.Presentation.hard
      else SpecTools.Generated.Presentation.all
    let some seed := seed.toNat? | IO.eprintln "SEED is a number"; return 2
    let some n := n.toNat? | IO.eprintln "N is a number"; return 2
    let some count := count.toNat? | IO.eprintln "COUNT is a number"; return 2
    let some empty := empty.toNat? | IO.eprintln "EMPTY is a number"; return 2
    let all := SpecTools.Generated.rules seed (n + 1) vocab
    let rs := all.take n
    IO.FS.createDirAll outDir
    IO.FS.writeFile (System.FilePath.mk outDir / "vocab") (vocab.name ++ "\n")
    let mut key : List String := []
    for i in List.range count do
      let (vs, ps) := if blindOnly then
          SpecTools.Generated.gvariant rs (all.getLastD default) seed i empty
            SpecTools.Generated.blindShapes (some 3)
        else SpecTools.Generated.gvariant rs (all.getLastD default) seed i empty
      let dir := System.FilePath.mk outDir / s!"v{i}"
      IO.FS.createDirAll dir
      for (f, text) in SpecTools.Generated.files vs do IO.FS.writeFile (dir / f) text
      IO.FS.writeFile (dir / "prose-rules.json")
        (Lean.Json.arr ((vs.filterMap (·.prose)).map SpecTools.Prose.ruleJson).toArray).compress
      let plants := ps.map fun p =>
        let row := match p.touches.head? with
          | some id => s!", \"row\": {(SpecTools.Generated.rowId ⟨id, "", [], 0, none⟩).quote}"
          | none => ""
        s!"\{\"kind\": {p.kind.quote}, \"clause\": {p.clause.quote}{row}}"
      let shown := (SpecTools.Generated.presentations offered seed i rs).map fun (id, p) =>
        s!"\{\"rule\": {id}, \"presentation\": {p.name.quote}}"
      key := key ++ [s!"\{\"variant\": {i}, \"plants\": [{", ".intercalate plants}], \"presentations\": [{", ".intercalate shown}]}"]
    IO.FS.writeFile (System.FilePath.mk outDir / "key.jsonl") ("\n".intercalate key ++ "\n")
    IO.println s!"{count} variants of {n} rules in {outDir}, the key in {outDir}/key.jsonl"
    return 0
  | ["prose", outDir] | ["prose", outDir, _] =>
    -- Each variant's prose rewritten as a person writes it (SpecTools.Prose), three variants at a
    -- time: the template stays as loans.template.md, a kept document becomes loans.md, and a
    -- variant whose three writings all fail gets LEFT_OUT, which `run` skips. Each variant's
    -- prompt, discards and usage go to vI/prose.json.
    let backend ← match (args.drop 2).head? with
      | some model => SpecTools.Model.selectedBackend "configured" model
      | none => SpecTools.Model.configuredBackend
    let keyText ← IO.FS.readFile (System.FilePath.mk outDir / "key.jsonl")
    let shownOf := SpecTools.SyntheticRun.keyPresentations keyText
    if shownOf.isEmpty then
      IO.eprintln s!"{outDir}/key.jsonl names no presentations: write the batch with gvariants"; return 2
    let width := 3
    let batches := (List.range ((shownOf.length + width - 1) / width)).map fun j =>
      (shownOf.drop (j * width)).take width
    let mut used : List SpecTools.Usage.Usage := []
    let mut kept := 0
    let mut writings := 0
    let mut leftOut : List Nat := []
    for batch in batches do
      let tasks ← batch.mapM fun (i, shown) => IO.asTask do
        let dir := System.FilePath.mk outDir / s!"v{i}"
        let rulesText ← IO.FS.readFile (dir / "prose-rules.json")
        let some rules := (Lean.Json.parse rulesText).toOption.bind (·.getArr?.toOption) |>.bind
            (·.toList.mapM SpecTools.Prose.ruleOfJson)
          | throw (IO.userError s!"{dir}/prose-rules.json holds no rule list")
        let scratch ← IO.FS.createTempDir
        let w ← SpecTools.Prose.writeFaithful SpecTools.Model.liveRunner [backend] backend rules
          shown scratch 600000
        IO.FS.removeDirAll scratch
        unless ← (dir / "loans.template.md").pathExists do
          IO.FS.writeFile (dir / "loans.template.md") (← IO.FS.readFile (dir / "loans.md"))
        match w.document with
        | some d => IO.FS.writeFile (dir / "loans.md") d
        | none => IO.FS.writeFile (dir / "LEFT_OUT") ("\n".intercalate w.discarded ++ "\n")
        IO.FS.writeFile (dir / "prose.json") (Lean.Json.mkObj [
          ("kept", Lean.toJson w.document.isSome), ("writings", Lean.toJson w.writings),
          ("discarded", Lean.toJson w.discarded), ("prompt", Lean.Json.str w.prompt),
          ("usage", SpecTools.Usage.asJson w.usage)]).compress
        return (i, w)
      for t in tasks do
        let (i, w) ← IO.ofExcept t.get
        used := used ++ [w.usage]
        writings := writings + w.writings
        for d in w.discarded do IO.println s!"v{i}: discarded {d}"
        if w.document.isSome then
          kept := kept + 1
          IO.println s!"v{i}: kept after {w.writings} writings"
        else
          leftOut := leftOut ++ [i]
          IO.println s!"v{i}: left out after {w.writings} writings"
    IO.println s!"prose: {kept} of {shownOf.length} variants kept, {writings} writings, left out {leftOut}"
    IO.println s!"prose {SpecTools.Usage.line (SpecTools.Usage.total used) (SpecTools.Usage.brief backend)}"
    return if leftOut.isEmpty then 0 else 1
  | ["owners-write", outDir, seed, form]
  | ["owners-write", outDir, seed, form, _]
  | ["owners-write", outDir, seed, form, _, _] =>
    -- An owner's text for the test in OUT-DIR (SpecTools.Owners): `ruleCount` rules of the vocab= domain
    -- from SEED, their flaws, written as `prose` or a `conversation`, five review rounds, the
    -- fidelity check; with NOTES-FILE, notes on real first calls for a conversation, and MODEL the
    -- model. Writes text.md when kept, steps.jsonl (every text and reader's list), writing.json.
    let some seed := seed.toNat? | IO.eprintln "SEED is a number"; return 2
    let form ← match form with
      | "prose" => pure SpecTools.Owners.Form.prose
      | "conversation" => pure .conversation
      | _ => IO.eprintln "FORM is prose or conversation"; return 2
    let notes ← match (args[4]? : Option String) with
      | some f => if f.isEmpty then pure "" else IO.FS.readFile (System.FilePath.mk f)
      | none => pure ""
    let backend ← match (args[5]? : Option String) with
      | some model => SpecTools.Model.selectedBackend "configured" model
      | none => SpecTools.Model.configuredBackend
    let rs := SpecTools.Generated.ownerRules seed SpecTools.Owners.ruleCount vocab
    let flaws := SpecTools.Owners.imperfections seed rs vocab.flawKinds
    let dir := System.FilePath.mk outDir
    IO.FS.createDirAll dir
    -- The calls run in a neutral temporary directory: a model sees its working directory, and the
    -- judges read a path naming owners' tests as a sign of generated text (the task's theory).
    -- Their records are copied into the test's directory after.
    let scratch ← IO.FS.createTempDir
    let w ← SpecTools.Owners.writeOwner SpecTools.Model.liveRunner [backend] backend vocab form rs
      flaws notes scratch 900000
    let copied ← IO.Process.output { cmd := "cp", args := #["-a", scratch.toString, (dir / "calls").toString] }
    if copied.exitCode != 0 then IO.eprintln s!"the calls' records were not copied: {copied.stderr}"
    else IO.FS.removeDirAll scratch
    IO.FS.writeFile (dir / "brief.txt") w.brief
    IO.FS.writeFile (dir / "steps.jsonl") ("\n".intercalate (w.steps.map fun s =>
      (Lean.Json.mkObj [("step", Lean.Json.str s.what), ("text", Lean.Json.str s.text),
        ("notes", Lean.toJson s.notes)]).compress) ++ "\n")
    IO.FS.writeFile (dir / "writing.json") (Lean.Json.mkObj [
      ("vocab", Lean.Json.str vocab.name), ("seed", Lean.toJson seed), ("form", Lean.Json.str form.name),
      ("kept", Lean.toJson w.text.isSome), ("last_tells", Lean.toJson w.lastTells),
      ("could_be_real", Lean.toJson w.lastVerdict),
      ("held_out", match w.heldOut with
        | some (v, c) => Lean.Json.mkObj [("verdict", Lean.Json.str v), ("confidence", Lean.toJson c)]
        | none => Lean.Json.null),
      ("passes_judge", Lean.toJson (SpecTools.Owners.passesJudge form w.heldOut)),
      ("test_judge", Lean.toJson w.testJudge), ("test_judge_why", Lean.toJson w.testJudgeWhy),
      ("test_samples", Lean.toJson w.testSamples), ("dev_judge", Lean.toJson w.devJudge),
      ("passes_bar", Lean.toJson (SpecTools.Owners.passesBar w.testJudge)),
      ("held_out_reasons", Lean.toJson w.heldOutReasons),
      ("fidelity_faults", Lean.toJson w.faults),
      ("flaws", Lean.toJson (flaws.map fun i => s!"r{i.rule}: {i.flaw.name}")),
      ("usage", SpecTools.Usage.asJson w.usage)]).compress
    for s in w.steps do IO.println s!"{s.what} ({s.notes.length} notes)"
    IO.println s!"last review of the kept text: could be real {w.lastVerdict}; tells ({w.lastTells.length}):"
    for t in w.lastTells do IO.println s!"  - {t}"
    for (fs, k) in w.faults.zipIdx do IO.println s!"fidelity check {k + 1}: {if fs.isEmpty then "faithful" else "; ".intercalate fs}"
    IO.println s!"development judge on the kept text: {w.devJudge}"
    IO.println s!"second judge (the bar, mean of {SpecTools.Owners.testSamples} at least {SpecTools.Owners.testBar}): samples {w.testSamples}, mean {w.testJudge}; passes: {SpecTools.Owners.passesBar w.testJudge}"
    for t in w.testJudgeWhy do IO.println s!"  - {t}"
    IO.println s!"first judge: {w.heldOut}; says owner: {SpecTools.Owners.passesJudge form w.heldOut}"
    for t in w.heldOutReasons do IO.println s!"  - {t}"
    IO.println s!"owners-write {SpecTools.Usage.line w.usage (SpecTools.Usage.brief backend)}"
    match w.text with
    | some t => IO.FS.writeFile (dir / "text.md") t; IO.println s!"kept: {dir}/text.md"; return 0
    | none => IO.println "not kept"; return 1
  | ["owners-variants", outDir, seed, count, empty] =>
    -- The batch of the test in OUT-DIR, after owners-write kept its text: COUNT variants of its
    -- rules, the first EMPTY with no plant, the others three shared blind spots on unflawed rules,
    -- each with the owner's text as its prose; the key names the blind spots and every variant's
    -- flaws by row, so `run` and `gapsrun` score both.
    let some seed := seed.toNat? | IO.eprintln "SEED is a number"; return 2
    let some count := count.toNat? | IO.eprintln "COUNT is a number"; return 2
    let some empty := empty.toNat? | IO.eprintln "EMPTY is a number"; return 2
    let dir := System.FilePath.mk outDir
    unless ← (dir / "text.md").pathExists do
      IO.eprintln s!"{dir}/text.md is missing: run owners-write first"; return 2
    let text ← IO.FS.readFile (dir / "text.md")
    let all := SpecTools.Generated.ownerRules seed (SpecTools.Owners.ruleCount + 1) vocab
    let rs := all.take SpecTools.Owners.ruleCount
    let flaws := SpecTools.Owners.imperfections seed rs vocab.flawKinds
    IO.FS.writeFile (dir / "vocab") (vocab.name ++ "\n")
    let flawPlants := flaws.map fun i =>
      let p := SpecTools.Owners.flawPlant rs i
      s!"\{\"kind\": {p.kind.quote}, \"clause\": {p.clause.quote}, \"row\": {(p.row.getD "").quote}}"
    let mut key : List String := []
    for i in List.range count do
      let (vs, ps) := SpecTools.Owners.ownerVariant rs (all.getLastD default) (flaws.map (·.rule))
        seed i empty
      let vdir := dir / s!"v{i}"
      IO.FS.createDirAll vdir
      for (f, t) in SpecTools.Generated.files vs do IO.FS.writeFile (vdir / f) t
      IO.FS.writeFile (vdir / "loans.template.md") (← IO.FS.readFile (vdir / "loans.md"))
      IO.FS.writeFile (vdir / "loans.md") text
      let plants := ps.map fun p =>
        let row := match p.touches.head? with
          | some id => s!", \"row\": {(SpecTools.Generated.rowId ⟨id, "", [], 0, none⟩).quote}"
          | none => ""
        s!"\{\"kind\": {p.kind.quote}, \"clause\": {p.clause.quote}{row}}"
      key := key ++ [s!"\{\"variant\": {i}, \"plants\": [{", ".intercalate (plants ++ flawPlants)}]}"]
    IO.FS.writeFile (dir / "key.jsonl") ("\n".intercalate key ++ "\n")
    IO.println s!"{count} variants of {rs.length} rules ({flaws.length} flawed) in {dir}, the key in {dir}/key.jsonl"
    return 0
  | "owners-fidelity" :: dirs@(_ :: _) =>
    -- The fidelity check alone (Owners.checkFidelity) on each DIR's text.md, DIR named T-k for a
    -- test T of Owners.suiteTests, its rules and flaws from T's seed: every check started before
    -- any is waited on; DIR/fidelity.json holds the faults; exit 1 when a text is not read
    -- faithfully. For a text written outside owners-write, which owners-suite reuses.
    let backend ← SpecTools.Model.selectedBackend "configured" "claude-opus-5-5"
    let jobs ← dirs.mapM fun d => do
      let dir := System.FilePath.mk d
      let test := ((dir.fileName.getD "").splitOn "-").headD ""
      let some seed := SpecTools.Owners.suiteTests.lookup test
        | throw (IO.userError s!"{d}: its name starts with no test of {SpecTools.Owners.suiteTests.map (·.1)}")
      let some v := SpecTools.Generated.Vocab.named test
        | throw (IO.userError s!"{test}: no such vocabulary")
      let text ← IO.FS.readFile (dir / "text.md")
      let rs := SpecTools.Generated.ownerRules seed SpecTools.Owners.ruleCount v
      let flaws := SpecTools.Owners.imperfections seed rs v.flawKinds
      let scratch ← IO.FS.createTempDir
      return (dir, scratch, ← IO.asTask (SpecTools.Owners.checkFidelity SpecTools.Model.liveRunner
        [backend] backend v rs flaws text scratch 900000))
    let mut allFaithful := true
    for (dir, scratch, task) in jobs do
      let (faults, used) ← IO.ofExcept task.get
      IO.FS.removeDirAll scratch
      IO.FS.writeFile (dir / "fidelity.json") (Lean.Json.mkObj [("faithful", Lean.toJson faults.isEmpty),
        ("faults", Lean.toJson faults), ("usage", SpecTools.Usage.asJson used)]).compress
      if faults.isEmpty then IO.println s!"{dir}: faithful"
      else
        allFaithful := false
        IO.println s!"{dir}: not faithful"
        for f in faults do IO.println s!"  - {f}"
    return if allFaithful then 0 else 1
  | "owners-suite" :: outDir :: tellsDir :: only =>
    -- The three prose tests in one invocation (the task's theory, "How does the next writing
    -- run"): each test writes T-a, T-b, T-c in turn under OUT-DIR, a writing holding text.md
    -- reused, Tells (its build in TELLS-DIR) reading each kept text, until Owners.suiteNext keeps
    -- one; then the kept writings' variants and gapsrun, the agents' arms one test at a time, and
    -- each table, written as T-table.md. A writing kept by no fidelity check counts as a model's.
    let self ← IO.appPath
    let out := System.FilePath.mk outDir
    let tells := System.FilePath.mk tellsDir
    let tag := out.fileName.getD "owners"
    let staging := tells / "staging" / tag
    IO.FS.createDirAll out
    IO.FS.createDirAll staging
    let spec (args : Array String) (log : System.FilePath) (limit : Nat) : IO UInt32 := do
      let o ← IO.Process.output { cmd := "timeout", args := #[toString limit, self.toString, "synthetic"] ++ args }
      IO.FS.writeFile log (o.stdout ++ o.stderr)
      return o.exitCode
    let tellsRun (args : Array String) : IO IO.Process.Output :=
      IO.Process.output { cmd := (tells / ".lake" / "build" / "bin" / "tells").toString, args, cwd := tells }
    -- Tells' verdict on a writing and its score in hundredths; a text judged before (by name) is
    -- not judged again, since `tells judge` skips it.
    let verdict (d : System.FilePath) : IO (Bool × Option Nat) := do
      unless ← (d / "text.md").pathExists do return (false, none)
      let name := s!"{tag}-{d.fileName.getD ""}-0"
      let input := staging / s!"{name}.json"
      IO.FS.writeFile input (Lean.Json.mkObj [("text", Lean.Json.str (← IO.FS.readFile (d / "text.md")))]).compress
      let j ← tellsRun #["judge", "prompts/joint.txt", "generated/judge", input.toString]
      let v ← tellsRun #["verdicts", "generated/judge", "posts/sets", name]
      IO.FS.writeFile (d.withExtension "verdict.txt") (j.stdout ++ j.stderr ++ v.stdout ++ v.stderr)
      match (v.stdout.splitOn "\n").findSome? SpecTools.Owners.parseScored with
      | some (_, h, s) => return (h, some s)
      | none => return (false, none)
    -- TEST ... after TELLS-DIR names the tests to run, all three without; `best` keeps each test's
    -- highest-scored writing when none passes (Owners.suiteKeep), its table stating the bar unmet
    let best := only.contains "best"
    let names := only.filter (· != "best")
    let all := SpecTools.Owners.suiteTests
    let tests := if names.isEmpty then all else all.filter (names.contains ·.1)
    if tests.length != names.length && !names.isEmpty then
      IO.eprintln s!"owners-suite: tests are salon, tailor and bakery, got {names}"; return 2
    let writeTest (t : String) (seed : Nat) : IO (Option System.FilePath) := do
      let mut vs : List (Bool × Option Nat) := []
      for k in ["a", "b", "c"] do
        if SpecTools.Owners.suiteNext (vs.map (·.1)) == .write then
          let d := out / s!"{t}-{k}"
          unless ← (d / "text.md").pathExists do
            -- OUT-DIR/T-base.txt, a real owner's message, when present: the writing starts from it.
            let base := out / s!"{t}-base.txt"
            let basePath := if ← base.pathExists then base.toString else ""
            let _ ← spec #["owners-write", d.toString, toString seed, "prose", basePath, "claude-opus-5-5",
              s!"vocab={t}"] (out / s!"{t}-{k}.log") 5400
          vs := vs ++ [← verdict d]
      IO.println s!"{t}: Tells' verdicts (human, hundredths) {vs}"
      match SpecTools.Owners.suiteKeep best vs with
      | some i => return some (out / s!"{t}-{["a", "b", "c"].getD i ""}")
      | none => return none
    -- Every test's task is started before any is waited on, so the tests write at once.
    let writing ← tests.mapM fun (t, seed) => IO.asTask (writeTest t seed)
    let written ← writing.mapM fun task => do IO.ofExcept (← IO.wait task)
    let kept₀ := (tests.zip written).filterMap fun ((t, seed), d) => d.map (t, seed, ·)
    for ((t, _), d) in tests.zip written do
      IO.println s!"{t}: {match d with | some d => s!"kept {d}" | none => "no text Tells reads as a human's"}"
    -- A kept text owners-write didn't write (no writing.json beside it) gets the fidelity check
    -- here, in one call for all such texts; a test whose text is not read faithfully gets no table.
    let reused ← kept₀.filterM fun (_, _, d) => do return !(← (d / "writing.json").pathExists)
    if !reused.isEmpty then
      let _ ← spec (#["owners-fidelity"] ++ (reused.map (·.2.2.toString)).toArray) (out / "fidelity.log") 1800
      IO.println (← IO.FS.readFile (out / "fidelity.log"))
    let kept ← kept₀.filterM fun (t, _, d) => do
      let f := d / "fidelity.json"
      if !(← f.pathExists) then return true
      let faithful := ((Lean.Json.parse (← IO.FS.readFile f)).toOption.bind
        fun j => (j.getObjValAs? Bool "faithful").toOption).getD false
      unless faithful do IO.println s!"{t}: its text is not read faithfully, see {f}; no table"
      return faithful
    -- A row whose results file is complete (Owners.rowDone over the 12 variants) is not run again.
    let done (d : System.FilePath) (row : String) : IO Bool := do
      let f := d / s!"results-{row}.jsonl"
      if !(← f.pathExists) then return false
      return SpecTools.Owners.rowDone 12 ((← IO.FS.readFile f).splitOn "\n")
    let preparing ← kept.mapM fun (t, seed, d) => IO.asTask do
        unless ← (d / "key.jsonl").pathExists do
          let v ← spec #["owners-variants", d.toString, toString seed, "12", "2", s!"vocab={t}"]
            (out / s!"{t}-variants.log") 600
          if v != 0 then return false
        unless ← done d "gaps" do
          let _ ← spec #["gapsrun", toString seed, "5", d.toString, "claude-opus-5-5"] (out / s!"{t}-gaps.log") 3600
          unless ← done d "gaps" do
            IO.println s!"{t}: the gaps row is incomplete (a variant failed or is missing), see {out}/{t}-gaps.log"
        return true
    let prepared ← preparing.mapM fun task => do IO.ofExcept (← IO.wait task)
    for ((t, _, d), ok) in kept.zip prepared do
      unless ok do IO.println s!"{t}: variants failed, see {out}/{t}-variants.log"; continue
      for arm in ["baseline", "ledger", "tools"] do
        if ← done d arm then IO.println s!"{t} {arm}: results complete, not run again"; continue
        let e ← spec #["run", d.toString, "claude-opus-5-5", "claude-opus-5-5", arm] (out / s!"{t}-{arm}.log") 7200
        IO.println s!"{t} {arm}: exit {e}{if ← done d arm then "" else ", the row incomplete (a variant failed or is missing)"}"
      let o ← IO.Process.output { cmd := self.toString, args := #["synthetic", "owners-table", d.toString] }
      -- The table opens with Tells' verdict on its text, so a table on a text below the bar says so.
      let vf := d.withExtension "verdict.txt"
      let verdictText ← if ← vf.pathExists then IO.FS.readFile vf else pure ""
      let verdictLine := (verdictText.splitOn "\n").find? (fun l => (SpecTools.Owners.parseVerdict l).isSome)
      IO.FS.writeFile (out / s!"{t}-table.md")
        (s!"Tells' verdict on this test's text: {verdictLine.getD "none"}\n\n" ++ o.stdout)
      IO.println s!"{t}: table in {out}/{t}-table.md"
    return if kept.length == tests.length then 0 else 1
  | "owners-best" :: outDir :: dirs =>
    -- Of a test's writings in DIRS (each written by owners-write), the one the development judge
    -- scored highest (Owners.bestIndex) is copied to OUT-DIR, to go on to its variants.
    let scores ← dirs.mapM fun d => do
      let f := System.FilePath.mk d / "writing.json"
      if !(← f.pathExists) then return none
      let j ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile f))
      return (j.getObjValAs? Nat "dev_judge").toOption
    IO.println s!"development judge's scores: {scores}"
    match SpecTools.Owners.bestIndex scores with
    | none => IO.eprintln "no writing has a score"; return 1
    | some i =>
      let chosen := dirs.getD i ""
      let out ← IO.Process.output { cmd := "cp", args := #["-a", chosen, outDir] }
      if out.exitCode != 0 then IO.eprintln out.stderr; return 1
      IO.println s!"chose {chosen} for {outDir}"
      return 0
  | ["power"] =>
    for line in SpecTools.Power.table do IO.println line
    return 0
  | ["power-threshold"] =>
    for line in SpecTools.Power.thresholdTable do IO.println line
    return 0
  | ["owners-table", outDir] =>
    -- The five rows of the test in OUT-DIR from its saved results (Owners.table).
    let dir := System.FilePath.mk outDir
    let lines (f : String) : IO (List Lean.Json) := do
      if ← (dir / f).pathExists then
        return ((← IO.FS.readFile (dir / f)).splitOn "\n").filter (· ≠ "") |>.filterMap
          fun l => (Lean.Json.parse l).toOption
      else return []
    IO.println (SpecTools.Owners.table (← lines "results-gaps.jsonl")
      (← lines "results-baseline.jsonl") (← lines "results-ledger.jsonl") (← lines "results-tools.jsonl"))
    return 0
  | ["gapsrun", seed, n, outDir, model] =>
    -- `gaps` itself on each variant of a batch written by gvariants SEED N, three at a time, scored
    -- by row against the key (Generated.rowScore); the full output of each goes to vI/gaps.txt.
    let some seed := seed.toNat? | IO.eprintln "SEED is a number"; return 2
    let some n := n.toNat? | IO.eprintln "N is a number"; return 2
    let rs := SpecTools.Generated.rulesOf seed n (← batchVocab outDir)
    let keyText ← IO.FS.readFile (System.FilePath.mk outDir / "key.jsonl")
    let keys : List (List String) := (keyText.splitOn "\n").filter (· ≠ "") |>.filterMap fun l => do
      let j ← (Lean.Json.parse l).toOption
      let plants ← (j.getObjValAs? (Array Lean.Json) "plants").toOption
      plants.toList.mapM fun p => (p.getObjValAs? String "clause").toOption
    let root ← IO.currentDir
    let width := 3
    let jobs := keys.zipIdx
    let batches := (List.range ((jobs.length + width - 1) / width)).map fun j =>
      (jobs.drop (j * width)).take width
    let mut found := 0
    let mut planted := 0
    let mut alarms := 0
    let mut failed := 0
    let mut used : List SpecTools.Usage.Usage := []
    let shownAll := SpecTools.SyntheticRun.keyPresentations keyText
    let plantsAll := SpecTools.SyntheticRun.keyPlants keyText
    let mut byPres : List (String × Nat × Nat × Nat) := []
    -- A key whose every plant names its row (gvariants since rows, owners-variants) is scored by
    -- `Score.score` with each row `gaps` names as a finding, as the agents' arms are, so shared blind
    -- spots, an owner's flaws and false alarms count apart; each variant's line goes to
    -- results-gaps.jsonl. An older key is scored by `rowScore` as before.
    let byRow := !plantsAll.isEmpty && plantsAll.all (·.all (·.row.isSome))
    let resultsOut ← IO.FS.Handle.mk (System.FilePath.mk outDir / "results-gaps.jsonl") .write
    let mut split : List (Bool × Nat × Nat × Nat × Nat × Nat) := []
    for batch in batches do
      let tasks ← batch.mapM fun ((k, i) : List String × Nat) => IO.asTask do
        let dir := System.FilePath.mk outDir / s!"v{i}"
        -- The variant's `gaps` call records its usage here; a rerun starts it afresh.
        let usagePath := dir / "gaps-usage.jsonl"
        if ← usagePath.pathExists then IO.FS.removeFile usagePath
        -- Through the one path every lake run takes (SyntheticRun.leanOn, then viaArgs, which moves
        -- the variables into the arguments the launcher keeps).
        let passed ← ["SPEC_TOOLS_HOST", "SPEC_TOOLS_BACKEND"].filterMapM fun k => do
          return (← IO.getEnv k).map (s!"{k}=" ++ ·)
        let inv := (SpecTools.SyntheticRun.leanOn root.toString dir.toString #[("SPEC_TOOLS_GAPS", some model),
          ("SPEC_TOOLS_DIR", some dir.toString), ("SPEC_TOOLS_USAGE", some usagePath.toString)]).viaArgs passed
        let out ← IO.Process.output { cmd := inv.cmd, args := inv.args, cwd := some inv.cwd, env := inv.env }
        IO.FS.writeFile (dir / "gaps.txt") (out.stdout ++ out.stderr)
        return (k, i, out, ← SpecTools.Usage.readRecorded usagePath)
      for t in tasks do
        let (k, i, out, u) ← IO.ofExcept t.get
        used := used ++ [u]
        let lines := out.stdout.splitOn "\n"
        let rows := lines.filterMap fun l =>
          match l.splitOn ": " with
          | kind :: row :: _ =>
            if ["uncovered", "too weak", "undecided", "extra"].contains kind then some row else none
          | _ => none
        let summary := lines.filter fun l => (l.splitOn " gaps, ").length > 1
        if out.exitCode != 0 || summary.isEmpty then
          failed := failed + 1
          IO.println s!"v{i}: failed (exit {out.exitCode}); see v{i}/gaps.txt"
          resultsOut.putStrLn s!"\{\"variant\": {i}, \"arm\": \"gaps\", \"error\": \"exit {out.exitCode}\", \"usage\": {(SpecTools.Usage.asJson u).compress}}"
        else if byRow then
          let key := plantsAll.getD i []
          let s := SpecTools.Score.score key (rows.map fun r => { clause := "", kind := "", row := some r })
          let blindPlanted := (key.filter (·.kind == "shared blind spot")).length
          let blindFound := (s.found.filter (· == "shared blind spot")).length
          let flawsFound := (s.found.filter SpecTools.Owners.isFlawKind).length
          let flawsPlanted := (key.filter (SpecTools.Owners.isFlawKind ·.kind)).length
          found := found + s.found.length
          planted := planted + key.length
          alarms := alarms + s.falseAlarms
          split := split ++ [(blindPlanted == 0, blindPlanted, blindFound, flawsPlanted, flawsFound,
            s.falseAlarms)]
          IO.println s!"v{i}: blind spots {blindFound} of {blindPlanted}, imperfections {flawsFound} of {flawsPlanted}, false alarms {s.falseAlarms}; rows {rows}"
          resultsOut.putStrLn s!"\{\"variant\": {i}, \"arm\": \"gaps\", \"found\": {s.found.length}, \"missed\": {s.missed.length}, \"false_alarms\": {s.falseAlarms}, \"ms\": {u.millis}, \"usage\": {(SpecTools.Usage.asJson u).compress}, \"found_kinds\": {(s.found.map (·.quote)).toString}, \"missed_kinds\": {(s.missed.map (·.quote)).toString}, \"rows\": {(rows.map (·.quote)).toString}}"
          resultsOut.flush
        else
          let (f, a) := SpecTools.Generated.rowScore rs k rows
          found := found + f
          planted := planted + k.length
          alarms := alarms + a
          IO.println s!"v{i}: found {f} of {k.length}, false alarms {a}; rows {rows}"
          let shown := (shownAll.lookup i).getD []
          unless shown.isEmpty do
            let bp := SpecTools.Score.byPresentation shown (plantsAll.getD i [])
              (rows.map fun r => { clause := "", kind := "", row := some r })
            byPres := byPres ++ bp
            IO.println s!"v{i} by presentation (planted, found, false alarms): {bp}"
    IO.println s!"gaps: {keys.length - failed} variants scored, found {found} of {planted}, false alarms {alarms}, {failed} failed"
    for (empty, label) in [(false, "variants with blind spots"), (true, "variants with none")] do
      let rs := split.filter (·.1 == empty)
      unless rs.isEmpty do
        IO.println s!"gaps on {label} ({rs.length}): blind spots {(rs.map (·.2.2.1)).sum} of {(rs.map (·.2.1)).sum}, imperfections {(rs.map (·.2.2.2.2.1)).sum} of {(rs.map (·.2.2.2.1)).sum}, false alarms {(rs.map (·.2.2.2.2.2)).sum}"
    for n in (byPres.map (·.1)).eraseDups do
      let rs := byPres.filter (·.1 == n)
      IO.println s!"gaps {n}: planted {(rs.map (·.2.1)).sum}, found {(rs.map (·.2.2.1)).sum}, false alarms {(rs.map (·.2.2.2)).sum}"
    IO.println s!"gaps {SpecTools.Usage.line (SpecTools.Usage.total used) s!"model {model}"}"
    return if failed == 0 then 0 else 1
  | "control" :: dirs =>
    -- Each fixture's audit and `tests`, three at a time (each `tests` runs three pytest copies), and
    -- their summary lines; the full output of each goes to DIR/control.txt.
    if dirs.isEmpty then IO.eprintln "usage: spec-tools synthetic control DIR..."; return 2
    let root ← IO.currentDir
    let width := 3
    let batches := (List.range ((dirs.length + width - 1) / width)).map fun j =>
      (dirs.drop (j * width)).take width
    let mut failed := false
    for batch in batches do
      let tasks ← batch.mapM fun (dir : String) => IO.asTask do
        -- What `spec-tools check tests` runs, which asks no model.
        let some inv := SpecTools.SyntheticRun.checkInvocation root.toString dir "" "tests"
          | throw (IO.userError "check tests has no invocation")
        let inv := inv.viaArgs []
        let out ← IO.Process.output { cmd := inv.cmd, args := inv.args, cwd := some inv.cwd, env := inv.env }
        IO.FS.writeFile (System.FilePath.mk dir / "control.txt") (out.stdout ++ out.stderr)
        return (dir, out)
      for t in tasks do
        let (dir, out) ← IO.ofExcept t.get
        let summary := (out.stdout.splitOn "\n").filter fun l =>
          (l.splitOn " rows: ").length > 1 || (l.splitOn " guards, ").length > 1
        IO.println s!"{dir}: exit {out.exitCode}; {"; ".intercalate summary}"
        if out.exitCode != 0 || summary.length != 2 then failed := true
    return if failed then 1 else 0
  | ["each", fixtureDir, outDir] =>
    -- One variant per plant, to check each plant on its own.
    let fixture ← fixtureFiles.mapM fun (f : String) => do
      return (f, ← IO.FS.readFile (System.FilePath.mk fixtureDir / f))
    for (p, i) in SpecTools.LoansPlants.catalogue.zipIdx do
      match applyEdits fixture p.edits with
      | .error e => IO.eprintln s!"plant {i} ({p.kind}): {e}"; return 1
      | .ok files =>
        let dir := System.FilePath.mk outDir / s!"p{i}"
        IO.FS.createDirAll dir
        for (f, text) in files do IO.FS.writeFile (dir / f) text
    IO.println s!"{SpecTools.LoansPlants.catalogue.length} single-plant variants in {outDir}"
    return 0
  | ["run", outDir, agentModel, toolModel]
  | ["run", outDir, agentModel, toolModel, "baseline"]
  | ["run", outDir, agentModel, toolModel, "ledger"]
  | ["run", outDir, agentModel, toolModel, "workflow"]
  | ["run", outDir, agentModel, toolModel, "tools"] =>
    -- Each variant to the ledger's and the baseline's arms, or to the one arm named (the scaling
    -- measure, its comparison, the prompt-only control, the tools run first), `width` runs at a
    -- time (a batch of 10 in two waves); the key is read only to score. One arm's results go to
    -- results-ARM.jsonl, so a batch's two-arm results.jsonl stays.
    let arms : List SpecTools.SyntheticRun.Arm := match args.getLast? with
      | some "baseline" => [.baseline]
      | some "ledger" => [.ledger]
      | some "workflow" => [.workflow]
      | some "tools" => [.tools]
      | _ => [.ledger, .baseline]
    let resultsFile := if arms.length == 1 then s!"results-{(arms.headD .baseline).name}.jsonl"
      else "results.jsonl"
    let keyText ← IO.FS.readFile (System.FilePath.mk outDir / "key.jsonl")
    let keys := SpecTools.SyntheticRun.keyPlants keyText
    let shownAll := SpecTools.SyntheticRun.keyPresentations keyText
    let root ← IO.currentDir
    let backend ← SpecTools.Model.selectedBackend "configured" agentModel
    -- The tools arm starts each run's audit, tests and gaps at once: three controls together peaked
    -- at 2.037 GiB, so ten of its runs with their agents near the 10 GiB budget; five at a time.
    -- On SPEC_TOOLS_HOST the agents run on that shared machine: one Claude question peaked at
    -- 263060 kB there with 3 GiB available, so three agents at a time.
    let onHost := (← IO.getEnv "SPEC_TOOLS_HOST").isSome
    let width := if onHost then 3 else if arms == [.tools] then 5 else 10
    -- Each result is appended to the results file as its run ends, so a run stopped part way keeps
    -- what finished; a later run on the same directory skips each variant and arm the file holds a
    -- result for (a failed run is tried again) and counts the saved results in its totals.
    let resultsPath := System.FilePath.mk outDir / resultsFile
    let saved : List Lean.Json ← do
      if ← resultsPath.pathExists then
        let text ← IO.FS.readFile resultsPath
        pure ((text.splitOn "\n").filter (· ≠ "") |>.filterMap fun l => (Lean.Json.parse l).toOption)
      else pure []
    let savedResult (j : Lean.Json) : Option (Nat × SpecTools.SyntheticRun.Arm × Nat × Nat × Nat × Nat) := do
      let i ← (j.getObjValAs? Nat "variant").toOption
      let name ← (j.getObjValAs? String "arm").toOption
      let a ← arms.find? (·.name == name)
      let found ← (j.getObjValAs? Nat "found").toOption
      let missed ← (j.getObjValAs? Nat "missed").toOption
      let alarms ← (j.getObjValAs? Nat "false_alarms").toOption
      let kinds := ((j.getObjValAs? (List String) "found_kinds").toOption).getD []
      return (i, a, found, missed, alarms, (kinds.filter (· == "shared blind spot")).length)
    let previous := saved.filterMap savedResult
    -- A variant whose person-prose writing failed (`prose`'s LEFT_OUT) is not run.
    let leftOut ← keys.zipIdx.filterMapM fun (_, i) => do
      if ← (System.FilePath.mk outDir / s!"v{i}" / "LEFT_OUT").pathExists then pure (some i)
      else pure none
    unless leftOut.isEmpty do IO.println s!"variants left out by prose: {leftOut}"
    let jobs : List (List Plant × Nat × SpecTools.SyntheticRun.Arm) :=
      keys.zipIdx.flatMap fun (k, i) => if leftOut.contains i then [] else arms.filterMap fun a =>
        if previous.any (fun (j, b, _) => j == i && b == a) then none else some (k, i, a)
    if !previous.isEmpty then
      IO.println s!"{previous.length} results already in {resultsPath}; {jobs.length} runs left"
    let out ← IO.FS.Handle.mk resultsPath .append
    let stdout ← IO.getStdout
    let mut totals : List (SpecTools.SyntheticRun.Arm × Nat × Nat × Nat) :=
      previous.map fun (_, a, f, m, fa, _) => (a, f, m, fa)
    let mut blind : List (SpecTools.SyntheticRun.Arm × Nat) :=
      previous.map fun (_, a, _, _, _, b) => (a, b)
    -- `width` runs at a time, the next starting as soon as one ends, so a slow run holds only its
    -- own slot. Each run is stopped after 600 s: the slowest measured on Opus took 140 s (a ledger
    -- run on a 30-rule variant), and an agent stuck on a wait of its own makes no progress.
    let start (job : List Plant × Nat × SpecTools.SyntheticRun.Arm) := IO.asTask do
      let (k, i, a) := job
      let r ← SpecTools.SyntheticRun.runArm backend (System.FilePath.mk outDir / s!"v{i}") a
        root.toString toolModel 600000
      return (k, i, a, r)
    let mut pending := jobs
    let mut running := #[]
    -- Each run's agent and tools usage, and its score by presentation, this invocation's runs only.
    let mut used : List (SpecTools.SyntheticRun.Arm × SpecTools.Usage.Usage × SpecTools.Usage.Usage) := []
    let mut byPres : List (SpecTools.SyntheticRun.Arm × List (String × Nat × Nat × Nat)) := []
    while !pending.isEmpty || !running.isEmpty do
      while running.size < width do
        match pending with
        | [] => break
        | job :: rest => running := running.push (← start job); pending := rest
      if h : running.toList.length > 0 then
        let _ ← IO.waitAny running.toList h
      let mut still := #[]
      let mut ended := #[]
      for t in running do
        if ← IO.hasFinished t then ended := ended.push t else still := still.push t
      running := still
      for t in ended do
        let (k, i, a, (r, agentUsage, toolsUsage)) ← IO.ofExcept t.get
        let arm := a.name
        let usages := s!"\"usage\": {(SpecTools.Usage.asJson agentUsage).compress}, \"tools_usage\": {(SpecTools.Usage.asJson toolsUsage).compress}"
        used := (a, agentUsage, toolsUsage) :: used
        match r with
        | .error e =>
          IO.println s!"v{i} {arm}: failed: {e}"
          out.putStrLn s!"\{\"variant\": {i}, \"arm\": \"{arm}\", \"error\": {e.quote}, {usages}}"
          out.flush
          stdout.flush
        | .ok (fs, checks) =>
          let s := SpecTools.Score.score k fs
          let ms := agentUsage.millis
          let bp := SpecTools.Score.byPresentation ((shownAll.lookup i).getD []) k fs
          byPres := (a, bp) :: byPres
          IO.println s!"v{i} {arm}: found {s.found} missed {s.missed} false alarms {s.falseAlarms} ({ms} ms; check ran {checks})"
          unless ((shownAll.lookup i).getD []).isEmpty do
            IO.println s!"v{i} {arm} by presentation (planted, found, false alarms): {bp}"
          out.putStrLn s!"\{\"variant\": {i}, \"arm\": \"{arm}\", \"found\": {s.found.length}, \"missed\": {s.missed.length}, \"false_alarms\": {s.falseAlarms}, \"ms\": {ms}, {usages}, \"checks\": {(checks.map (·.quote)).toString}, \"found_kinds\": {(s.found.map (·.quote)).toString}, \"missed_kinds\": {(s.missed.map (·.quote)).toString}, \"findings\": {(Lean.Json.arr (fs.map SpecTools.SyntheticRun.savedFinding).toArray).compress}}"
          out.flush
          stdout.flush
          totals := (a, s.found.length, s.missed.length, s.falseAlarms) :: totals
          blind := (a, (s.found.filter (· == "shared blind spot")).length) :: blind
    for arm in arms do
      let ts := totals.filter (·.1 == arm)
      IO.println s!"{arm.name}: {ts.length} runs, found \
        {(ts.map (·.2.1)).sum}, missed {(ts.map (·.2.2.1)).sum}, false alarms {(ts.map (·.2.2.2)).sum}"
      let rows := ((byPres.filter (·.1 == arm)).flatMap (·.2))
      for n in (rows.map (·.1)).eraseDups do
        let rs := rows.filter (·.1 == n)
        IO.println s!"{arm.name} {n}: planted {(rs.map (·.2.1)).sum}, found {(rs.map (·.2.2.1)).sum}, false alarms {(rs.map (·.2.2.2)).sum}"
      let us := used.filter (·.1 == arm)
      unless us.isEmpty do
        IO.println s!"{arm.name} agents' {SpecTools.Usage.line (SpecTools.Usage.total (us.map (·.2.1))) (SpecTools.Usage.brief backend)}"
        IO.println s!"{arm.name} tools' {SpecTools.Usage.line (SpecTools.Usage.total (us.map (·.2.2))) s!"tools model {toolModel}"}"
    -- The bar (the theory's entry on how a tool is judged), when both arms ran on the variants.
    let arm (a : SpecTools.SyntheticRun.Arm) := totals.filter (·.1 == a)
    let led := arm .ledger
    let base := arm .baseline
    if !led.isEmpty && !base.isEmpty then
      let blindOf (a : SpecTools.SyntheticRun.Arm) := ((blind.filter (·.1 == a)).map (·.2)).sum
      let alarms (ts : List (SpecTools.SyntheticRun.Arm × Nat × Nat × Nat)) := (ts.map (·.2.2.2)).sum
      let bar := SpecTools.Score.barText (blindOf .ledger) (blindOf .baseline) (alarms led)
        (alarms base) led.length
      IO.println s!"bar: {bar}"
    return 0
  | ["rescore", outDir] =>
    -- Each arm's saved findings in DIR's results*.jsonl scored again against DIR/key.jsonl by the
    -- current scorer, per arm in total; a run that failed has no findings and is left out.
    let dir := System.FilePath.mk outDir
    let keyText ← IO.FS.readFile (dir / "key.jsonl")
    let keys := SpecTools.SyntheticRun.keyPlants keyText
    let files := ((← dir.readDir).map (·.fileName)).toList.filter fun n =>
      n.startsWith "results" && n.endsWith ".jsonl"
    let mut totals : List (String × Nat × Nat × Nat × Nat) := []
    for file in files.mergeSort (· ≤ ·) do
      for l in ((← IO.FS.readFile (dir / file)).splitOn "\n").filter (· ≠ "") do
        let some j := (Lean.Json.parse l).toOption | IO.eprintln s!"{file}: unparsed line"; return 1
        let some arm := (j.getObjValAs? String "arm").toOption | continue
        let some v := (j.getObjValAs? Nat "variant").toOption | continue
        let some fsJ := (j.getObjValAs? (Array Lean.Json) "findings").toOption | continue
        let fs := fsJ.toList.filterMap SpecTools.SyntheticRun.findingOfSaved
        let some k := keys[v]? | IO.eprintln s!"{file}: variant {v} not in the key"; return 1
        let s := SpecTools.Score.score k fs
        let blindFound := (s.found.filter (· == "shared blind spot")).length
        IO.println s!"{file} v{v} {arm}: found {s.found.length} of {k.length}, blind spots {blindFound}, false alarms {s.falseAlarms}"
        totals := (arm, 1, s.found.length, blindFound, s.falseAlarms) :: totals
    for arm in (totals.map (·.1)).eraseDups do
      let ts := totals.filter (·.1 == arm)
      IO.println s!"{arm}: {ts.length} runs, found {(ts.map (·.2.2.1)).sum}, blind spots {(ts.map (·.2.2.2.1)).sum}, false alarms {(ts.map (·.2.2.2.2)).sum}"
    return 0
  | [seed, count, empty, fixtureDir, outDir] =>
    let some seed := seed.toNat? | IO.eprintln "SEED is a number"; return 2
    let some count := count.toNat? | IO.eprintln "COUNT is a number"; return 2
    let some empty := empty.toNat? | IO.eprintln "EMPTY is a number"; return 2
    let fixture ← fixtureFiles.mapM fun (f : String) => do
      return (f, ← IO.FS.readFile (System.FilePath.mk fixtureDir / f))
    IO.FS.createDirAll outDir
    let mut key : List String := []
    for i in List.range count do
      match variant SpecTools.LoansPlants.catalogue fixture seed i empty with
      | .error e => IO.eprintln s!"variant {i}: {e}"; return 1
      | .ok v =>
        let dir := System.FilePath.mk outDir / s!"v{i}"
        IO.FS.createDirAll dir
        for (f, text) in v.files do IO.FS.writeFile (dir / f) text
        let plants := v.key.map fun p => s!"\{\"kind\": {p.kind.quote}, \"clause\": {p.clause.quote}}"
        key := key ++ [s!"\{\"variant\": {i}, \"plants\": [{", ".intercalate plants}]}"]
    IO.FS.writeFile (System.FilePath.mk outDir / "key.jsonl") ("\n".intercalate key ++ "\n")
    IO.println s!"{count} variants in {outDir}, the key in {outDir}/key.jsonl"
    return 0
  | _ => IO.eprintln "usage: spec-tools synthetic SEED COUNT EMPTY FIXTURE-DIR OUT-DIR"; return 2

open SpecTools.Model in
def clauses (args : List String) : IO UInt32 := do
  match args with
  | [harness, model, proseFile] | [harness, model, proseFile, _] =>
    let timeoutMs := (args.drop 3).head? |>.bind String.toNat? |>.getD 300000
    let backend ← selectedBackend harness model
    let scratch ← IO.FS.createTempDir
    let (result, used) ← SpecTools.Clauses.compare liveRunner [backend] backend
      (← IO.FS.readFile proseFile) scratch timeoutMs
    IO.FS.removeDirAll scratch
    let usageLine := SpecTools.Usage.line used (SpecTools.Usage.brief backend)
    match result with
    | .ok (first, second, diffs) =>
      IO.println s!"first extraction: {first.length} clauses; second: {second.length}"
      for c in first do IO.println s!"clause: {c}"
      for d in diffs do IO.println s!"to add: {d}"
      IO.println s!"{diffs.length} differences"
      IO.println usageLine
      return 0
    | .error failure => IO.eprintln failure.describe; IO.println usageLine; return 1
  | _ => IO.eprintln "usage: spec-tools clauses HARNESS MODEL PROSE-FILE [TIMEOUT-MS]"; return 2

def usage : String :=
  "usage: spec-tools COMMAND ...\n" ++ "\n".intercalate (commands.map fun (c, d) => s!"  {c}: {d}")

open SpecTools.Model in
def ask (args : List String) : IO UInt32 := do
  match args with
  | [harness, model, schemaFile, promptFile] | [harness, model, schemaFile, promptFile, _] =>
    let timeoutMs := (args.drop 4).head? |>.bind String.toNat? |>.getD 120000
    let backend ← selectedBackend harness model
    let schema ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile schemaFile))
    let scratch ← IO.FS.createTempDir
    let (result, used) ← SpecTools.Usage.askRecorded "ask" liveRunner [backend] backend
      { prompt := ← IO.FS.readFile promptFile, schema, timeoutMs } scratch
    IO.FS.removeDirAll scratch
    IO.eprintln (SpecTools.Usage.line used (SpecTools.Usage.brief backend))
    match result with
    | .ok outcome => IO.println outcome.answer.compress; return 0
    | .error failure => IO.eprintln failure.describe; return 1
  | _ => IO.eprintln usage; return 2

private def readJsonFile [Lean.FromJson α] (path : String) : IO α := do
  IO.ofExcept ((Lean.Json.parse (← IO.FS.readFile path)).bind Lean.fromJson?)

open SpecTools.Gaps SpecTools.Model in
def reviewCoverageDraft (args : List String) : IO UInt32 := do
  match args with
  | [harness, model, prosePath, inventoryPath, draftPath] =>
    let inventory : List DraftSource ← readJsonFile inventoryPath
    let draft : List DraftRow ← readJsonFile draftPath
    let backend ← selectedBackend harness model
    let prose ← IO.FS.readFile prosePath
    let scratch ← IO.FS.createTempDir
    let (result, used) ← try reviewDraft liveRunner [backend] backend inventory draft prose scratch
      finally IO.FS.removeDirAll scratch
    let usageLine := SpecTools.Usage.line used (SpecTools.Usage.brief backend)
    match result with
    | .error message => IO.eprintln message; IO.println usageLine; return 1
    | .ok report =>
      let gaps := kinds.flatMap report.byKind
      for gap in gaps do
        IO.println s!"{gap.kind.name}: {gap.row}: {gap.why}"
      for error in report.refused do IO.eprintln s!"Refused proposal: {error}"
      IO.println s!"{gaps.length} gaps, {report.refused.length} proposals refused"
      IO.println usageLine
      return if gaps.isEmpty && report.refused.isEmpty then 0 else 1
  | _ => IO.eprintln usage; return 2

open SpecTools.Gaps in
def checkCoverageDraft (args : List String) : IO UInt32 := do
  match args with
  | [inventoryPath, draftPath] =>
    let inventory : List DraftSource ← readJsonFile inventoryPath
    let draft : List DraftRow ← readJsonFile draftPath
    let issues := draftIssues inventory draft
    if issues.isEmpty then
      IO.println s!"Complete Coverage draft: {draft.length} rows."
      return 0
    IO.eprintln ("Submit the full Coverage draft together.\n" ++ "\n".intercalate issues)
    return 1
  | _ => IO.eprintln usage; return 2

def main (args : List String) : IO UInt32 := do
  match args with
  | "ask" :: rest => ask rest
  | "clauses" :: rest => clauses rest
  | "draft-check" :: rest => checkCoverageDraft rest
  | ["draft-hook", python, bridge] => SpecTools.DraftHook.run python bridge
  | ["draft-hook-json", python, bridge] => SpecTools.DraftHook.runJson python bridge
  | "draft-review" :: rest => reviewCoverageDraft rest
  | "synthetic" :: rest => synthetic rest
  | ["check", sub] => SpecTools.SyntheticRun.runCheck sub
  | [] => IO.eprintln usage; return 2
  | command :: _ => IO.eprintln s!"unknown command `{command}`\n{usage}"; return 2
