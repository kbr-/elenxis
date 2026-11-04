import SpecTools

/-- The commands, each with what it does. -/
def commands : List (String × String) := [
  ("ask", "ask one question of a backend: ask HARNESS MODEL SCHEMA-FILE PROMPT-FILE [TIMEOUT-MS]"),
  ("clauses", "extract a prose file's clauses twice and print the differences: \
    clauses HARNESS MODEL PROSE-FILE [TIMEOUT-MS]"),
  ("synthetic", "write a batch of variants of the loans fixture with planted gaps, the key apart: \
    synthetic SEED COUNT EMPTY FIXTURE-DIR OUT-DIR")
]

/-- The loans fixture's files a variant is made of. -/
def fixtureFiles : List String := ["loans.md", "Loans.lean", "loans.py", "test_loans.py"]

open SpecTools.Synthetic in
def synthetic (args : List String) : IO UInt32 := do
  match args with
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
  | ["run", outDir, agentModel, toolModel] =>
    -- Each variant to both arms, `width` runs at a time; the key is read only to score.
    let keyText ← IO.FS.readFile (System.FilePath.mk outDir / "key.jsonl")
    let keys := (keyText.splitOn "\n").filter (· ≠ "") |>.filterMap fun l => do
      let j ← (Lean.Json.parse l).toOption
      let plants ← (j.getObjValAs? (Array Lean.Json) "plants").toOption
      plants.toList.mapM fun p => do
        return ({ kind := ← (p.getObjValAs? String "kind").toOption,
                  clause := ← (p.getObjValAs? String "clause").toOption, edits := [] } : Plant)
    let root ← IO.currentDir
    let backend : SpecTools.Model.Backend :=
      { harness := .claudeCode, model := agentModel, dataGoesTo := "Anthropic" }
    let width := 6
    let jobs : List (List Plant × Nat × Bool) :=
      keys.zipIdx.flatMap fun (k, i) => [(k, i, true), (k, i, false)]
    let batches := (List.range ((jobs.length + width - 1) / width)).map fun j =>
      (jobs.drop (j * width)).take width
    let mut results : Array String := #[]
    let mut totals : List (Bool × Nat × Nat × Nat) := []
    for batch in batches do
      let tasks ← batch.mapM fun ((k, i, ledger) : List Plant × Nat × Bool) => IO.asTask do
        let r ← SpecTools.SyntheticRun.runArm backend (System.FilePath.mk outDir / s!"v{i}") ledger
          root.toString toolModel 1200000
        return (k, i, ledger, r)
      for t in tasks do
        let (k, i, ledger, r) ← IO.ofExcept t.get
        let arm := if ledger then "ledger" else "baseline"
        match r with
        | .error e =>
          IO.println s!"v{i} {arm}: failed: {e}"
          results := results.push s!"\{\"variant\": {i}, \"arm\": \"{arm}\", \"error\": {e.quote}}"
        | .ok (fs, cost) =>
          let s := SpecTools.Score.score k fs
          let ms := cost.millis
          let tokens := match cost.tokens with | some t => toString t | none => "null"
          IO.println s!"v{i} {arm}: found {s.found} missed {s.missed} false alarms {s.falseAlarms} ({ms} ms, {tokens} tokens)"
          results := results.push s!"\{\"variant\": {i}, \"arm\": \"{arm}\", \"found\": {s.found.length}, \"missed\": {s.missed.length}, \"false_alarms\": {s.falseAlarms}, \"ms\": {ms}, \"tokens\": {tokens}, \"found_kinds\": {(s.found.map (·.quote)).toString}, \"missed_kinds\": {(s.missed.map (·.quote)).toString}, \"findings\": {(fs.map fun f => s!"[{f.clause.quote}, {f.kind.quote}]").toString}}"
          totals := (ledger, s.found.length, s.missed.length, s.falseAlarms) :: totals
    IO.FS.writeFile (System.FilePath.mk outDir / "results.jsonl") ("\n".intercalate results.toList ++ "\n")
    for arm in [true, false] do
      let ts := totals.filter (·.1 == arm)
      IO.println s!"{if arm then "ledger" else "baseline"}: {ts.length} runs, found \
        {(ts.map (·.2.1)).sum}, missed {(ts.map (·.2.2.1)).sum}, false alarms {(ts.map (·.2.2.2)).sum}"
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
def harnessOf : String → Option Harness
  | "claude-code" => some .claudeCode
  | "codex" => some .codex
  | _ => none

open SpecTools.Model in
def clauses (args : List String) : IO UInt32 := do
  match args with
  | [harness, model, proseFile] | [harness, model, proseFile, _] =>
    let timeoutMs := (args.drop 3).head? |>.bind String.toNat? |>.getD 300000
    let some harness := harnessOf harness
      | IO.eprintln s!"unknown harness `{harness}`: claude-code or codex"; return 2
    let backend : Backend := { harness, model, dataGoesTo := s!"{harness.name}'s provider" }
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
    let harness ← match harness with
      | "claude-code" => pure Harness.claudeCode
      | "codex" => pure Harness.codex
      | other => do IO.eprintln s!"unknown harness `{other}`: claude-code or codex"; return 2
    let schema ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile schemaFile))
    let backend : Backend := { harness, model, dataGoesTo := s!"{harness.name}'s provider" }
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

def main (args : List String) : IO UInt32 := do
  match args with
  | "ask" :: rest => ask rest
  | "clauses" :: rest => clauses rest
  | "synthetic" :: rest => synthetic rest
  | [] => IO.eprintln usage; return 2
  | command :: _ => IO.eprintln s!"unknown command `{command}`\n{usage}"; return 2
