import SpecTools

/-- The commands, each with what it does. -/
def commands : List (String × String) := [
  ("ask", "ask one question of a backend: ask HARNESS MODEL SCHEMA-FILE PROMPT-FILE [TIMEOUT-MS]"),
  ("clauses", "extract a prose file's clauses twice and print the differences: \
    clauses HARNESS MODEL PROSE-FILE [TIMEOUT-MS]"),
  ("draft-check", "check complete coverage before model review: draft-check INVENTORY DRAFT"),
  ("draft-review", "review a complete coverage draft: draft-review HARNESS MODEL PROSE INVENTORY DRAFT"),
  ("synthetic", "write a batch of variants of the loans fixture with planted gaps, the key apart: \
    synthetic SEED COUNT EMPTY FIXTURE-DIR OUT-DIR"),
  ("check", "run one spec tool on the synthetic variant in the current directory, with the root and \
    model its spec-tools.json names: check audit|tests|gaps|clauses")
]

/-- The loans fixture's files a variant is made of. -/
def fixtureFiles : List String := ["loans.md", "Loans.lean", "loans.py", "test_loans.py"]

open SpecTools.Synthetic in
def synthetic (args : List String) : IO UInt32 := do
  match args with
  | ["generate", seeds, ns, outDir] =>
    -- The complete generated fixture of N rules from SEED, for each seed and N of the comma-separated
    -- lists, in OUT-DIR/sSEED-nN: the controls generated variants are made from.
    let some seeds := (seeds.splitOn ",").mapM String.toNat? | IO.eprintln "SEEDS are numbers"; return 2
    let some ns := (ns.splitOn ",").mapM String.toNat? | IO.eprintln "NS are numbers"; return 2
    for seed in seeds do
      for n in ns do
        let rs := SpecTools.Generated.rules seed n
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
    let all := SpecTools.Generated.rules seed (n + 1)
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
  | ["gvariants", seed, n, count, empty, outDir, "blind"] =>
    -- A batch of COUNT variants of the fixture of N rules from SEED, the first EMPTY with no plant,
    -- in the loans batches' layout, so `synthetic run` takes it; `blind` gives each three shared
    -- blind spots and nothing else (the scaling measure).
    let blindOnly := args.getLast? == some "blind"
    let some seed := seed.toNat? | IO.eprintln "SEED is a number"; return 2
    let some n := n.toNat? | IO.eprintln "N is a number"; return 2
    let some count := count.toNat? | IO.eprintln "COUNT is a number"; return 2
    let some empty := empty.toNat? | IO.eprintln "EMPTY is a number"; return 2
    let all := SpecTools.Generated.rules seed (n + 1)
    let rs := all.take n
    IO.FS.createDirAll outDir
    let mut key : List String := []
    for i in List.range count do
      let (vs, ps) := if blindOnly then
          SpecTools.Generated.gvariant rs (all.getLastD default) seed i empty
            SpecTools.Generated.blindShapes (some 3)
        else SpecTools.Generated.gvariant rs (all.getLastD default) seed i empty
      let dir := System.FilePath.mk outDir / s!"v{i}"
      IO.FS.createDirAll dir
      for (f, text) in SpecTools.Generated.files vs do IO.FS.writeFile (dir / f) text
      let plants := ps.map fun p => s!"\{\"kind\": {p.kind.quote}, \"clause\": {p.clause.quote}}"
      key := key ++ [s!"\{\"variant\": {i}, \"plants\": [{", ".intercalate plants}]}"]
    IO.FS.writeFile (System.FilePath.mk outDir / "key.jsonl") ("\n".intercalate key ++ "\n")
    IO.println s!"{count} variants of {n} rules in {outDir}, the key in {outDir}/key.jsonl"
    return 0
  | ["gapsrun", seed, n, outDir, model] =>
    -- `gaps` itself on each variant of a batch written by gvariants SEED N, three at a time, scored
    -- by row against the key (Generated.rowScore); the full output of each goes to vI/gaps.txt.
    let some seed := seed.toNat? | IO.eprintln "SEED is a number"; return 2
    let some n := n.toNat? | IO.eprintln "N is a number"; return 2
    let rs := SpecTools.Generated.rules seed n
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
    for batch in batches do
      let tasks ← batch.mapM fun ((k, i) : List String × Nat) => IO.asTask do
        let dir := System.FilePath.mk outDir / s!"v{i}"
        let out ← IO.Process.output {
          cmd := "lake", args := #["env", "lean", (dir / "Loans.lean").toString],
          cwd := some root.toString,
          env := #[("SPEC_TOOLS_GAPS", some model), ("SPEC_TOOLS_DIR", some dir.toString)] }
        IO.FS.writeFile (dir / "gaps.txt") (out.stdout ++ out.stderr)
        return (k, i, out)
      for t in tasks do
        let (k, i, out) ← IO.ofExcept t.get
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
        else
          let (f, a) := SpecTools.Generated.rowScore rs k rows
          found := found + f
          planted := planted + k.length
          alarms := alarms + a
          IO.println s!"v{i}: found {f} of {k.length}, false alarms {a}; rows {rows}"
    IO.println s!"gaps: {keys.length - failed} variants scored, found {found} of {planted}, false alarms {alarms}, {failed} failed"
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
    let keys := (keyText.splitOn "\n").filter (· ≠ "") |>.filterMap fun l => do
      let j ← (Lean.Json.parse l).toOption
      let plants ← (j.getObjValAs? (Array Lean.Json) "plants").toOption
      plants.toList.mapM fun p => do
        return ({ kind := ← (p.getObjValAs? String "kind").toOption,
                  clause := ← (p.getObjValAs? String "clause").toOption, edits := [] } : Plant)
    let root ← IO.currentDir
    let backend ← SpecTools.Model.selectedBackend "configured" agentModel
    -- The tools arm starts each run's audit, tests and gaps at once: three controls together peaked
    -- at 2.037 GiB, so ten of its runs with their agents near the 10 GiB budget; five at a time.
    let width := if arms == [.tools] then 5 else 10
    let jobs : List (List Plant × Nat × SpecTools.SyntheticRun.Arm) :=
      keys.zipIdx.flatMap fun (k, i) => arms.map fun a => (k, i, a)
    let batches := (List.range ((jobs.length + width - 1) / width)).map fun j =>
      (jobs.drop (j * width)).take width
    let mut results : Array String := #[]
    let mut totals : List (SpecTools.SyntheticRun.Arm × Nat × Nat × Nat) := []
    let mut blind : List (SpecTools.SyntheticRun.Arm × Nat) := []
    for batch in batches do
      let tasks ← batch.mapM fun ((k, i, a) : List Plant × Nat × SpecTools.SyntheticRun.Arm) =>
        IO.asTask do
          let r ← SpecTools.SyntheticRun.runArm backend (System.FilePath.mk outDir / s!"v{i}") a
            root.toString toolModel 1200000
          return (k, i, a, r)
      for t in tasks do
        let (k, i, a, r) ← IO.ofExcept t.get
        let arm := a.name
        match r with
        | .error e =>
          IO.println s!"v{i} {arm}: failed: {e}"
          results := results.push s!"\{\"variant\": {i}, \"arm\": \"{arm}\", \"error\": {e.quote}}"
        | .ok (fs, cost, checks) =>
          let s := SpecTools.Score.score k fs
          let ms := cost.millis
          let tokens := match cost.tokens with | some t => toString t | none => "null"
          IO.println s!"v{i} {arm}: found {s.found} missed {s.missed} false alarms {s.falseAlarms} ({ms} ms, {tokens} tokens; check ran {checks})"
          results := results.push s!"\{\"variant\": {i}, \"arm\": \"{arm}\", \"found\": {s.found.length}, \"missed\": {s.missed.length}, \"false_alarms\": {s.falseAlarms}, \"ms\": {ms}, \"tokens\": {tokens}, \"checks\": {(checks.map (·.quote)).toString}, \"found_kinds\": {(s.found.map (·.quote)).toString}, \"missed_kinds\": {(s.missed.map (·.quote)).toString}, \"findings\": {(fs.map fun f => s!"[{f.clause.quote}, {f.kind.quote}]").toString}}"
          totals := (a, s.found.length, s.missed.length, s.falseAlarms) :: totals
          blind := (a, (s.found.filter (· == "shared blind spot")).length) :: blind
    IO.FS.writeFile (System.FilePath.mk outDir / resultsFile) ("\n".intercalate results.toList ++ "\n")
    for arm in arms do
      let ts := totals.filter (·.1 == arm)
      IO.println s!"{arm.name}: {ts.length} runs, found \
        {(ts.map (·.2.1)).sum}, missed {(ts.map (·.2.2.1)).sum}, false alarms {(ts.map (·.2.2.2)).sum}"
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
    let keys := (keyText.splitOn "\n").filter (· ≠ "") |>.filterMap fun l => do
      let j ← (Lean.Json.parse l).toOption
      let plants ← (j.getObjValAs? (Array Lean.Json) "plants").toOption
      plants.toList.mapM fun p => do
        return ({ kind := ← (p.getObjValAs? String "kind").toOption,
                  clause := ← (p.getObjValAs? String "clause").toOption, edits := [] } : Plant)
    let files := ((← dir.readDir).map (·.fileName)).toList.filter fun n =>
      n.startsWith "results" && n.endsWith ".jsonl"
    let mut totals : List (String × Nat × Nat × Nat × Nat) := []
    for file in files.mergeSort (· ≤ ·) do
      for l in ((← IO.FS.readFile (dir / file)).splitOn "\n").filter (· ≠ "") do
        let some j := (Lean.Json.parse l).toOption | IO.eprintln s!"{file}: unparsed line"; return 1
        let some arm := (j.getObjValAs? String "arm").toOption | continue
        let some v := (j.getObjValAs? Nat "variant").toOption | continue
        let some fsJ := (j.getObjValAs? (Array Lean.Json) "findings").toOption | continue
        let fs : List SpecTools.Score.Finding := fsJ.toList.filterMap fun f => do
          let a ← (f.getArrVal? 0).toOption
          let b ← (f.getArrVal? 1).toOption
          return { clause := ← (Lean.Json.getStr? a).toOption, kind := ← (Lean.Json.getStr? b).toOption }
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
    let result ← SpecTools.Clauses.compare liveRunner [backend] backend
      (← IO.FS.readFile proseFile) scratch timeoutMs
    IO.FS.removeDirAll scratch
    match result with
    | .ok (first, second, diffs) =>
      IO.println s!"first extraction: {first.length} clauses; second: {second.length}"
      for c in first do IO.println s!"clause: {c}"
      for d in diffs do IO.println s!"to add: {d}"
      IO.println s!"{diffs.length} differences"
      return 0
    | .error failure => IO.eprintln failure.describe; return 1
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
    let result ← SpecTools.Model.ask liveRunner [backend] backend
      { prompt := ← IO.FS.readFile promptFile, schema, timeoutMs } scratch
    IO.FS.removeDirAll scratch
    match result with
    | .ok outcome =>
      IO.println outcome.answer.compress
      IO.eprintln s!"cost: {outcome.cost.millis} ms, tokens: {outcome.cost.tokens}"
      return 0
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
    let result ← try reviewDraft liveRunner [backend] backend inventory draft prose scratch
      finally IO.FS.removeDirAll scratch
    match result with
    | .error message => IO.eprintln message; return 1
    | .ok report =>
      let gaps := kinds.flatMap report.byKind
      for gap in gaps do
        IO.println s!"{gap.kind.name}: {gap.row}: {gap.why}"
      for error in report.refused do IO.eprintln s!"Refused proposal: {error}"
      IO.println s!"{gaps.length} gaps, {report.refused.length} proposals refused"
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
  | "draft-review" :: rest => reviewCoverageDraft rest
  | "synthetic" :: rest => synthetic rest
  | ["check", sub] => SpecTools.SyntheticRun.runCheck sub
  | [] => IO.eprintln usage; return 2
  | command :: _ => IO.eprintln s!"unknown command `{command}`\n{usage}"; return 2
