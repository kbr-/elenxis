-- SPDX-License-Identifier: Apache-2.0
module

public import Lean.Data.Json

/-!
What a model call used, as its harness reports it. Each count is known for some calls and lacking for
the others, never a zero standing for a count no report gave: a total over calls keeps the known sum
and how many calls lacked the field. The list price is the harness's, in billionths of a dollar; a
subscription's user doesn't pay it, so it is printed as a list price. The record's laws (the empty
total is the unit, totals combine associatively, a lacking field stays counted) are in
`SpecTools.UsageProofs`.
-/

public section

namespace SpecTools.Usage
open Lean

/-- A count over calls: the sum of the calls that reported it, and how many calls didn't. -/
structure Field where
  known : Nat := 0
  lacking : Nat := 0
  deriving Repr, BEq, DecidableEq

/-- One call's count: reported, or lacking. -/
def Field.of : Option Nat → Field
  | some n => { known := n }
  | none => { lacking := 1 }

instance : Add Field := ⟨fun a b => { known := a.known + b.known, lacking := a.lacking + b.lacking }⟩

/-- What one call used, or the total of several. Wall time is always measured, by the caller. -/
structure Usage where
  calls : Nat := 0
  input : Field := {}
  cacheWrite : Field := {}
  cacheRead : Field := {}
  output : Field := {}
  turns : Field := {}
  millis : Nat := 0
  apiMillis : Field := {}
  /-- The harness's list price, in billionths of a dollar. -/
  listPriceNano : Field := {}
  deriving Repr, BEq, DecidableEq

instance : Add Usage := ⟨fun a b =>
  { calls := a.calls + b.calls, input := a.input + b.input, cacheWrite := a.cacheWrite + b.cacheWrite,
    cacheRead := a.cacheRead + b.cacheRead, output := a.output + b.output, turns := a.turns + b.turns,
    millis := a.millis + b.millis, apiMillis := a.apiMillis + b.apiMillis,
    listPriceNano := a.listPriceNano + b.listPriceNano }⟩

/-- The total of several records. -/
def total (us : List Usage) : Usage := us.foldr (· + ·) {}

/-- One call whose harness reported nothing: every field lacking but its wall time. -/
def unreported (millis : Nat) : Usage :=
  { calls := 1, input := .of none, cacheWrite := .of none, cacheRead := .of none, output := .of none,
    turns := .of none, millis, apiMillis := .of none, listPriceNano := .of none }

/-- A JSON number as billionths, truncated: `0.0180018` is `18001800`. -/
def nanoOf (n : JsonNumber) : Option Nat :=
  if n.mantissa < 0 then none
  else
    let m := n.mantissa.toNat
    some (if n.exponent ≤ 9 then m * 10 ^ (9 - n.exponent) else m / 10 ^ (n.exponent - 9))

private def natAt (j : Json) (k : String) : Option Nat := (j.getObjValAs? Nat k).toOption

/-- One call's usage from Claude Code's JSON report (`--output-format json`). -/
def ofClaudeReport (report : Json) (millis : Nat) : Usage :=
  let usage := (report.getObjVal? "usage").toOption.getD Json.null
  let price := match report.getObjVal? "total_cost_usd" with
    | .ok (.num n) => nanoOf n
    | _ => none
  { calls := 1, input := .of (natAt usage "input_tokens"),
    cacheWrite := .of (natAt usage "cache_creation_input_tokens"),
    cacheRead := .of (natAt usage "cache_read_input_tokens"), output := .of (natAt usage "output_tokens"),
    turns := .of (natAt report "num_turns"), millis, apiMillis := .of (natAt report "duration_api_ms"),
    listPriceNano := .of price }

theorem ofClaudeReport_fields (report usage : Json) (millis input cacheWrite cacheRead output
    turns apiMillis : Nat) (price : JsonNumber)
    (hasUsage : report.getObjVal? "usage" = .ok usage)
    (hasInput : usage.getObjValAs? Nat "input_tokens" = .ok input)
    (hasWrite : usage.getObjValAs? Nat "cache_creation_input_tokens" = .ok cacheWrite)
    (hasRead : usage.getObjValAs? Nat "cache_read_input_tokens" = .ok cacheRead)
    (hasOutput : usage.getObjValAs? Nat "output_tokens" = .ok output)
    (hasTurns : report.getObjValAs? Nat "num_turns" = .ok turns)
    (hasApiMillis : report.getObjValAs? Nat "duration_api_ms" = .ok apiMillis)
    (hasPrice : report.getObjVal? "total_cost_usd" = .ok (.num price)) :
    ofClaudeReport report millis = {
      calls := 1, input := .of (some input), cacheWrite := .of (some cacheWrite),
      cacheRead := .of (some cacheRead), output := .of (some output), turns := .of (some turns),
      millis, apiMillis := .of (some apiMillis), listPriceNano := .of (nanoOf price) } := by
  simp [ofClaudeReport, natAt, hasUsage, hasInput, hasWrite, hasRead, hasOutput, hasTurns,
    hasApiMillis, hasPrice, Except.toOption]

/-- A line contributes usage only if it is a completed turn with a usage member. -/
def codexUsageEvent? (line : String) : Option Json := do
  let event ← (Json.parse line).toOption
  if (event.getObjValAs? String "type").toOption = some "turn.completed" then
    (event.getObjVal? "usage").toOption
  else none

theorem codexUsageEvent_iff (line : String) (usage : Json) :
    codexUsageEvent? line = some usage ↔
      ∃ event, Json.parse line = .ok event ∧
        event.getObjValAs? String "type" = .ok "turn.completed" ∧
        event.getObjVal? "usage" = .ok usage := by
  cases parsed : Json.parse line with
  | error error => simp [codexUsageEvent?, parsed, Except.toOption]
  | ok event =>
    cases kind : event.getObjValAs? String "type" <;>
      cases reported : event.getObjVal? "usage" <;>
      simp [codexUsageEvent?, parsed, kind, reported, Except.toOption, and_comm]

def ofCodexLines (lines : List String) (millis : Nat) : Usage :=
  match (lines.filterMap codexUsageEvent?).getLast? with
  | none => unreported millis
  | some usage =>
    { calls := 1, input := .of (natAt usage "input_tokens"),
      cacheWrite := .of (natAt usage "cache_write_input_tokens"),
      cacheRead := .of (natAt usage "cached_input_tokens"), output := .of (natAt usage "output_tokens"),
      turns := .of none, millis, apiMillis := .of none, listPriceNano := .of none }

/-- One call's usage from Codex's `--json` events: the last `turn.completed` event's `usage`. Codex
reports no turns count, API time or price. -/
def ofCodexEvents (events : String) (millis : Nat) : Usage :=
  ofCodexLines (events.splitOn "\n") millis

theorem ofCodexLines_no_report (lines : List String) (millis : Nat)
    (missing : ∀ line ∈ lines, codexUsageEvent? line = none) :
    ofCodexLines lines millis = unreported millis := by
  simp [ofCodexLines, List.filterMap_eq_nil_iff.mpr missing]

theorem ofCodexLines_last (before after : List String) (line : String) (usage : Json)
    (millis input cacheWrite cacheRead output : Nat)
    (reported : codexUsageEvent? line = some usage)
    (noLater : ∀ event ∈ after, codexUsageEvent? event = none)
    (hasInput : usage.getObjValAs? Nat "input_tokens" = .ok input)
    (hasWrite : usage.getObjValAs? Nat "cache_write_input_tokens" = .ok cacheWrite)
    (hasRead : usage.getObjValAs? Nat "cached_input_tokens" = .ok cacheRead)
    (hasOutput : usage.getObjValAs? Nat "output_tokens" = .ok output) :
    ofCodexLines (before ++ line :: after) millis = {
      calls := 1, input := .of (some input), cacheWrite := .of (some cacheWrite),
      cacheRead := .of (some cacheRead), output := .of (some output), turns := .of none,
      millis, apiMillis := .of none, listPriceNano := .of none } := by
  simp [ofCodexLines, List.filterMap_append, reported,
    List.filterMap_eq_nil_iff.mpr noLater, List.getLast?_append, natAt, hasInput, hasWrite, hasRead,
    hasOutput, Except.toOption]

/-- One call's usage from a command adapter's `usage.json`, whose fields are the record's names
(`input`, `cacheWrite`, `cacheRead`, `output`, `turns`, `apiMillis`, `listPriceUsd`); an absent field
is lacking, and an absent file is `unreported`. -/
def ofAdapterFile (file : Option Json) (millis : Nat) : Usage :=
  match file with
  | none => unreported millis
  | some j =>
    let price := match j.getObjVal? "listPriceUsd" with
      | .ok (.num n) => nanoOf n
      | _ => none
    { calls := 1, input := .of (natAt j "input"), cacheWrite := .of (natAt j "cacheWrite"),
      cacheRead := .of (natAt j "cacheRead"), output := .of (natAt j "output"), turns := .of (natAt j "turns"),
      millis, apiMillis := .of (natAt j "apiMillis"), listPriceNano := .of price }

/-- A count as printed: the known sum, and how many calls lacked it. -/
def Field.show (f : Field) : String :=
  if f.lacking == 0 then toString f.known
  else if f.known == 0 then s!"unknown ({f.lacking} unreported)"
  else s!"{f.known} + unknown ({f.lacking} unreported)"

/-- Billionths of a dollar as a decimal, seven places. -/
def dollars (nano : Nat) : String :=
  let tenthMicros := (nano + 50) / 100
  let whole := tenthMicros / 10000000
  let frac := toString (tenthMicros % 10000000)
  s!"${whole}.{String.ofList (List.replicate (7 - frac.length) '0')}{frac}"

/-- The line a command prints at its end. -/
def line (u : Usage) (backend : String) : String :=
  let price :=
    if u.listPriceNano.lacking == 0 then s!"; list price {dollars u.listPriceNano.known} (not billed under a subscription)"
    else if u.listPriceNano.known == 0 then ""
    else s!"; list price {dollars u.listPriceNano.known} + unknown ({u.listPriceNano.lacking} unreported)"
  s!"usage: {u.calls} calls; tokens input {u.input.show}, cache write {u.cacheWrite.show}, \
    cache read {u.cacheRead.show}, output {u.output.show}; {u.millis} ms; {backend}{price}"

/-- A record as JSON, for results files and the trace; a field is `{"known", "lacking"}`. -/
def asJson (u : Usage) : Json :=
  let f (x : Field) := Json.mkObj [("known", x.known), ("lacking", x.lacking)]
  Json.mkObj [("calls", u.calls), ("input", f u.input), ("cacheWrite", f u.cacheWrite),
    ("cacheRead", f u.cacheRead), ("output", f u.output), ("turns", f u.turns), ("millis", u.millis),
    ("apiMillis", f u.apiMillis), ("listPriceNano", f u.listPriceNano)]

/-- A record read back from `asJson`'s form. -/
def fromJson? (j : Json) : Option Usage := do
  let f (k : String) : Option Field := do
    let o ← (j.getObjVal? k).toOption
    return { known := ← natAt o "known", lacking := ← natAt o "lacking" }
  let calls ← natAt j "calls"
  let input ← f "input"
  let cacheWrite ← f "cacheWrite"
  let cacheRead ← f "cacheRead"
  let output ← f "output"
  let turns ← f "turns"
  let millis ← natAt j "millis"
  let apiMillis ← f "apiMillis"
  let listPriceNano ← f "listPriceNano"
  return { calls, input, cacheWrite, cacheRead, output, turns, millis, apiMillis, listPriceNano }

end SpecTools.Usage

end
