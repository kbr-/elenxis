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

def view (id : String) (inputs : List Input) : Except String Json := do
  if id.trimAscii.isEmpty then throw "An evidence view needs a requirement ID"
  let mut names := #[]
  for i in inputs do
    if (← schema i.report) == "elenxis.audit.v1" then
      for row in ← records i.report "rows" do
        if fieldIs row "id" id then
          for decl in ← records row "declarations" do
            names := names.push (← decl.getObjValAs? String "name")
  let dimensions := ["formal", "domain", "realizability", "consistency", "semanticGaps", "adversarial",
    "mutation", "discrimination", "obligations", "ownerApproval"]
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
        if ["unresolved", "conflicting"].any (fieldIs r "status" ·) then items := items.push ("obligations", r)
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
      if (← r.getObjValAs? (List String) "requirements").contains id then items := items.push ("ownerApproval", r)
    | _ => throw s!"Unsupported report schema {s}"
    if !items.isEmpty then
      sources := sources.push <| Json.mkObj [("source", toJson index), ("schema", toJson s),
        ("fingerprint", toJson (key r)), ("freshness", toJson (Evidence.freshness (key r) (i.current.bind key)))]
    for (dimension, entry) in items do
      let prior ← rows.getObjValAs? (Array Json) dimension
      rows := rows.setObjVal! dimension <| .arr (prior.push <| Json.mkObj [("source", toJson index), ("evidence", entry)])
  return Json.mkObj [("schema", "elenxis.requirement.v1"), ("requirement", toJson id),
    ("dimensions", rows), ("sources", .arr sources)]

end SpecTools.RequirementView
