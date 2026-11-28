-- SPDX-License-Identifier: Apache-2.0
import SpecTools.Evidence

namespace SpecTools.RequirementView
open Lean

/-- The companion is a replay of the same review in the current environment. -/
structure Input where
  report : Json
  current : Option Json := none
  deriving FromJson

private def schema (r : Json) := r.getObjValAs? String "schema"
private def records (r : Json) (key : String) := r.getObjValAs? (List Json) key
private def fieldIs (r : Json) (field value : String) := (r.getObjValAs? String field).toOption == some value
private def key (r : Json) := (r.getObjValAs? Evidence.Fingerprint "fingerprint").toOption

private def context (r : Json) : Option Evidence.Context := do
  let c ← (r.getObjValAs? Evidence.Context "specification").toOption
  guard (!c.project.trimAscii.isEmpty && !c.snapshot.trimAscii.isEmpty)
  return c

private def replayState (i : Input) : String := Id.run do
  let some replay := i.current | return "unknown"
  if (context i.report).isNone || (context replay).isNone then return "unknown"
  if (context i.report).map (·.project) != (context replay).map (·.project) then return "incompatible"
  if context i.report != context replay then return "stale"
  return Evidence.freshness (key i.report) (key replay)

def violatesExpectation (expected : Option Bool) (status : String) : Bool :=
  match expected with
  | some true => status == "refuted"
  | some false => status == "established"
  | none => false

theorem violatesExpectation_iff (expected : Option Bool) (status : String) :
    violatesExpectation expected status = true ↔
      (expected = some true ∧ status = "refuted") ∨ (expected = some false ∧ status = "established") := by
  cases expected with
  | none => simp [violatesExpectation]
  | some value => cases value <;> simp [violatesExpectation]

private def singleView (id : String) (inputs : List Input) : Except String Json := do
  if id.trimAscii.isEmpty then throw "An evidence view needs a requirement ID"
  let mut names := #[]
  for i in inputs do
    if (← schema i.report) == "elenxis.audit.v1" && !["stale", "incompatible"].contains (replayState i) then
      for row in ← records i.report "rows" do
        if fieldIs row "id" id then
          for decl in ← records row "declarations" do
            names := names.push (← decl.getObjValAs? String "name")
  let dimensions := ["formal", "domain", "realizability", "consistency", "semanticGaps", "adversarial",
    "mutation", "discrimination", "obligations", "ownerApproval", "pendingOwner", "defects",
    "refutedObjectives", "conflicts", "staleEvidence", "incompatibleEvidence", "associationIssues"]
  let mut rows := Json.mkObj (dimensions.map fun d => (d, Json.arr #[]))
  let mut sources := #[]
  for (i, index) in inputs.zipIdx do
    let r := i.report
    let s ← schema r
    if let some other := i.current then
      unless (← schema other) == s do throw "Replay schema differs from saved report"
    let mut items : Array (String × Json) := #[]
    match s with
    | "elenxis.audit.v1" =>
      for row in ← records r "rows" do
        if fieldIs row "id" id then
          items := items.push ("formal", row)
          for d in ← records row "applicability" do
            items := items.push ("domain", d)
            unless fieldIs d "status" "established" do items := items.push ("obligations", d)
    | "elenxis.relation.v1" =>
      let ids ← r.getObjValAs? (List String) "requirements"
      if ids.contains id then
        items := items.push (if ids.length > 1 then "consistency" else "realizability", r)
        if fieldIs r "status" "unresolved" then items := items.push ("obligations", r)
        if fieldIs r "status" "conflicting" then items := items.push ("conflicts", r)
        if fieldIs r "status" "refuted" then items := items.push ("refutedObjectives", r)
        let links := (records r "associations").toOption.getD []
        let validated := ids.all fun member => links.any fun l =>
          fieldIs l "id" member && fieldIs l "status" "validated"
        for link in links do
          unless fieldIs link "status" "validated" do items := items.push ("associationIssues", link)
        let expected := (r.getObjValAs? Bool "expected").toOption
        if validated && violatesExpectation expected (← r.getObjValAs? String "status") then
          items := items.push ("defects", r)
    | "elenxis.gaps.v1" =>
      if (← r.getObjValAs? (List String) "rows").contains id then
        let findings := (← records r "findings").filter (fieldIs · "row" id)
        items := items.push ("semanticGaps", Json.mkObj [("findings", toJson findings),
          ("completedReadings", ← r.getObjVal? "completedReadings"), ("semanticCompleteness", "unassessed")])
    | "elenxis.mutation.v1" =>
      for c in ← records r "candidates" do
        if fieldIs c "requirement" id then
          items := items.push ("mutation", c)
          let checks ← records c "checks"
          if checks.isEmpty then items := items.push ("obligations", c)
          for check in checks do
            unless fieldIs check "status" "established" do
              items := items.push ("obligations", Json.mkObj [("candidate", ← c.getObjVal? "id"), ("check", check)])
      for check in (← r.getObjValAs? (Option (List Json)) "missingScheduledChecks").getD [] do
        if fieldIs check "requirement" id then items := items.push ("obligations", check)
    | "elenxis.adversarial.v1" =>
      for c in ← records r "checkedClaims" do
        if names.contains (← c.getObjValAs? String "subject") then items := items.push ("adversarial", c)
    | "elenxis.discrimination.v1" =>
      let entries := (r.getObjValAs? (List Json) "distinguished").toOption.getD []
      for c in entries do
        if fieldIs c "property" id then items := items.push ("discrimination", c)
    | "elenxis.owner.v1" =>
      if (← r.getObjValAs? (List String) "requirements").contains id then
        let mut validity := "unassessed"
        if let some replay := i.current then
          if let .ok receipt := r.getObjValAs? String "receiptKey" then
            if !receipt.isEmpty && fieldIs replay "receiptKey" receipt &&
                (context r).isSome && (context r).map (·.project) == (context replay).map (·.project) then
              let observed ← replay.getObjValAs? String "ownerAcceptance"
              if ["verified", "invalid", "stale"].contains observed then
                validity := if observed == "verified" && context r != context replay then "stale" else observed
        let assessment := Json.mkObj [("historical", ← r.getObjVal? "ownerAcceptance"),
          ("currentValidity", toJson validity), ("receipt", r)]
        items := items.push ("ownerApproval", assessment)
        unless validity == "verified" do items := items.push ("pendingOwner", assessment)
    | _ => throw s!"Unsupported report schema {s}"
    if !items.isEmpty then
      sources := sources.push <| Json.mkObj [("source", toJson index), ("schema", toJson s),
        ("fingerprint", toJson (key r)), ("specification", toJson (context r)),
        ("freshness", toJson (replayState i))]
      let state := replayState i
      if ["stale", "incompatible"].contains state then
        let archive := if state == "stale" then "staleEvidence" else "incompatibleEvidence"
        items := items.filter (fun p => ["ownerApproval", "pendingOwner"].contains p.1) |>.push (archive, r)
    for (dimension, entry) in items do
      let prior ← rows.getObjValAs? (Array Json) dimension
      rows := rows.setObjVal! dimension <| .arr (prior.push <| Json.mkObj [("source", toJson index), ("evidence", entry)])
  return Json.mkObj [("schema", "elenxis.requirement.v1"), ("requirement", toJson id),
    ("dimensions", rows), ("sources", .arr sources)]

def view (id : String) (inputs : List Input) : Except String Json := do
  let mut groups : List (List Input) := []
  for i in inputs do
    if let some c := context i.report then
      if groups.any (fun g => (g.head?.bind fun j => context j.report) == some c) then
        groups := groups.map fun g =>
          if (g.head?.bind fun j => context j.report) == some c then g ++ [i] else g
        continue
    groups := groups ++ [[i]]
  let isolated ← groups.mapM fun g => do
    let ctx := g.head?.bind fun i => context i.report
    return (← singleView id g).setObjVal! "specification" (toJson ctx)
      |>.setObjVal! "provenance" (toJson (if ctx.isSome then "identified" else "unverifiable"))
  if let [one] := isolated then return one
  return (← singleView id []).setObjVal! "groups" (toJson isolated)
    |>.setObjVal! "provenance" (toJson (if inputs.isEmpty then "missing" else "isolated"))

end SpecTools.RequirementView
