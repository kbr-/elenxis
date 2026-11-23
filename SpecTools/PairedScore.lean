import SpecTools.SyntheticRun

namespace SpecTools.PairedScore
open Lean Score Synthetic

structure Result where
  findings : List Finding := []
  agent : Usage.Usage := {}
  tools : Usage.Usage := {}

private def decoded (source : String) : Except String (List Json) :=
  ((source.splitOn "\n").filter (!·.trimAscii.isEmpty)).mapM Json.parse

private def readKey (source : String) : Except String (List (Nat × List Plant)) := do
  let records ← decoded source
  let keys ← records.mapM fun record => do
    let id ← record.getObjValAs? Nat "variant"
    let [plants] := SyntheticRun.keyPlants record.compress | throw s!"Invalid key for v{id}"
    return (id, plants)
  let ids := keys.map (·.1)
  if ids.isEmpty || ids != List.range ids.length then
    throw "The key needs variant IDs in order starting at zero"
  return keys

private def readArm (arm : String) (ids : List Nat) (source : String) :
    Except String (List (Nat × Result)) := do
  let mut results := []
  for record in ← decoded source do
    let id ← record.getObjValAs? Nat "variant"
    let actual ← record.getObjValAs? String "arm"
    unless ids.contains id && actual == arm do throw s!"Unexpected result for v{id} {actual}"
    if (record.getObjValAs? String "error").isOk then continue
    let entries ← record.getObjValAs? (Array Json) "findings"
    let some findings := entries.toList.mapM SyntheticRun.findingOfSaved |
      throw s!"Invalid finding in v{id} {arm}"
    let some agent := (record.getObjVal? "usage").toOption.bind Usage.fromJson? |
      throw s!"Invalid agent usage in v{id} {arm}"
    let some tools := (record.getObjVal? "tools_usage").toOption.bind Usage.fromJson? |
      throw s!"Invalid tool usage in v{id} {arm}"
    if (results.lookup id).isSome then throw s!"Duplicate success for v{id} {arm}"
    results := (id, ⟨findings, agent, tools⟩) :: results
  for id in ids do
    if (results.lookup id).isNone then throw s!"Missing successful result for v{id} {arm}"
  return results

def lostPlants (plants : List Plant) (baseline candidate : List Finding) : List Nat :=
  plants.zipIdx.filterMap fun (plant, index) =>
    if baseline.any (names · plant) && !candidate.any (names · plant) then some index else none

theorem lostPlants_covered (plants : List Plant) (baseline candidate : List Finding)
    (noLoss : ∀ plant ∈ plants, baseline.any (names · plant) = true →
      candidate.any (names · plant) = true) : lostPlants plants baseline candidate = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro index found
  obtain ⟨⟨plant, i⟩, source, selected⟩ := List.mem_filterMap.mp found
  have inPlants := List.mem_iff_getElem?.mpr ⟨i, List.mem_zipIdx_iff_getElem?.mp source⟩
  by_cases hit : baseline.any (names · plant) = true
  · have kept := noLoss plant inPlants hit
    simp [hit, kept] at selected
  · simp [hit] at selected

private def summarize (arm : String) (scores : List Score) (results : List (Nat × Result)) :
    List String :=
  [s!"{arm}: hits {(scores.map (·.found.length)).sum}, " ++
      s!"misses {(scores.map (·.missed.length)).sum}, alarms {(scores.map (·.falseAlarms)).sum}",
    Usage.line (Usage.total (results.map (·.2.agent))) s!"{arm} agent",
    Usage.line (Usage.total (results.map (·.2.tools))) s!"{arm} checks"]

structure Comparison where
  variants : Nat
  controls : Nat
  losses : Nat
  controlAlarms : Nat
  reports : List String

def acceptance (comparisons : List Comparison) : Bool :=
  (comparisons.map (·.controls)).sum > 0 &&
    comparisons.all fun result => result.losses == 0 && result.controlAlarms == 0

/-- Compare complete journals on the same key, including the identities of the retained plants. -/
def compare (key tools confirmed : String) : Except String Comparison := do
  let keys ← readKey key
  let ids := keys.map (·.1)
  let baseline ← readArm "tools" ids tools
  let candidate ← readArm "confirmed" ids confirmed
  let mut losses := 0
  let mut controlAlarms := 0
  let mut reports := []
  let mut baselineScores := []
  let mut candidateScores := []
  for (id, plants) in keys do
    let a := (baseline.lookup id).getD {}
    let b := (candidate.lookup id).getD {}
    let sa := score plants a.findings
    let sb := score plants b.findings
    let lost := lostPlants plants a.findings b.findings
    let control := if plants.isEmpty then sb.falseAlarms else 0
    losses := losses + lost.length
    controlAlarms := controlAlarms + control
    reports := (s!"v{id}: {plants.length} plants, tools {sa.found.length} hits and " ++
      s!"{sa.falseAlarms} alarms, confirmed {sb.found.length} hits and {sb.falseAlarms} alarms, " ++
      s!"lost plant indices {lost}") :: reports
    baselineScores := sa :: baselineScores
    candidateScores := sb :: candidateScores
  let controls := keys.countP (·.2.isEmpty)
  return ⟨keys.length, controls, losses, controlAlarms,
    reports.reverse ++ summarize "tools" baselineScores baseline ++
    summarize "confirmed" candidateScores candidate⟩

#guard acceptance [⟨2, 0, 0, 0, []⟩, ⟨1, 1, 0, 0, []⟩]
#guard !acceptance [⟨2, 0, 0, 0, []⟩]
#guard !acceptance [⟨2, 1, 1, 0, []⟩]
#guard !acceptance [⟨2, 1, 0, 1, []⟩]

section Controls

private def plants : List Plant :=
  [⟨"weak", "first clause", [], some "r0"⟩, ⟨"weak", "second clause", [], some "r1"⟩]

private def hitFirst : Finding := ⟨"first clause", "weak", some "r0"⟩
private def hitSecond : Finding := ⟨"second clause", "weak", some "r1"⟩

#guard lostPlants plants [hitFirst] [hitFirst, hitSecond] == []
#guard lostPlants plants [hitFirst] [hitSecond] == [0]
#guard (readArm "tools" [0] "").isOk == false
#guard !(readKey "{\"variant\":1,\"plants\":[]}\n{\"variant\":0,\"plants\":[]}").isOk

end Controls

end SpecTools.PairedScore
