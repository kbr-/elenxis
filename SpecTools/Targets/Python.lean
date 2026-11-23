import SpecTools.Generated
import SpecTools.OwnersProofs

namespace SpecTools.Targets.Python
open SpecTools.Generated

def leanFile (vs : List View) : String :=
  "\n".intercalate [
    "import SpecTools.Audit", "import SpecTools.GapsRun", "import SpecTools.Tests", "",
    "/-! The generated synthetic fixture's Lean model: the rules as data, a request refused when one",
    "fires, a theorem per clause with a witness that its hypotheses hold, and the ledger. -/", "",
    "namespace Loans", "open SpecTools.Ledger", ""] ++ "\n" ++
  leanModel (vs.map (·.model)) ++ leanImplementation ++
  "\n\n".intercalate (vs.map leanTheorems) ++ "\n\n" ++
  "def pythonTest (id : String) : List String := [\"test_\" ++ id.replace \"-\" \"_\"]\n\n" ++
  s!"def rows : List Row := [\n{leanRows vs}\n]\n\n" ++
  "def ledger : List Row := rows.map fun r => { r with externalChecks := pythonTest r.id }\n\n" ++
  "end Loans\n\n#eval SpecTools.Audit.run Loans.ledger `Loans\n\n" ++
  "def fixtureDir : IO String := return (← IO.getEnv \"SPEC_TOOLS_DIR\").getD \"fixtures/loans\"\n" ++
  "def adapterPath : IO String :=\n  return (← IO.getEnv \"SPEC_TOOLS_ADAPTER\").getD \"../../adapters/python_guards.py\"\n\n" ++
  "#eval show IO Unit from do\n  if (← IO.getEnv \"SPEC_TOOLS_TESTS\").isSome then\n" ++
  "    SpecTools.Tests.run Loans.ledger (← adapterPath) \"loans.py\" \"test_loans.py\"\n      (cwd := some (← fixtureDir))\n\n" ++
  "#eval show Lean.Elab.Command.CommandElabM Unit from do\n  if let some model ← IO.getEnv \"SPEC_TOOLS_GAPS\" then\n" ++
  "    SpecTools.Gaps.run Loans.ledger (← IO.FS.readFile (System.FilePath.mk (← fixtureDir) / \"loans.md\"))\n" ++
  "      (← SpecTools.Model.selectedBackend \"configured\" model)\n"

/-! The Python: an `if` per rule, so each rule is a guard the adapter can remove. -/

def pyCond (r : Rule) : String :=
  let sum := " + ".intercalate (r.measures.map fun m => s!"req.get(\"{m}\")")
  let flag := match r.flag with | some f => s!" and not req.get(\"{f}\")" | none => ""
  s!"req.kind == \"{r.kind}\" and {sum} >= {r.bound}{flag}"

def pythonFile (vs : List View) : String :=
  "\"\"\"The generated synthetic fixture's Python: a request is refused (None) when a rule fires.\"\"\"\n\n" ++
  "from __future__ import annotations\n\nfrom dataclasses import dataclass, field\n\n\n" ++
  "@dataclass(frozen=True)\nclass Req:\n    kind: str\n    vals: dict[str, int] = field(default_factory=dict)\n\n" ++
  "    def get(self, k: str) -> int:\n        return self.vals.get(k, 0)\n\n\n" ++
  "def handle(req: Req) -> Req | None:\n" ++
  String.join (vs.map fun v => s!"    if {pyCond v.python}:\n        return None\n") ++
  "    return req\n"

/-! The tests: per rule, its case refused at and over the bound, accepted below it; per flag, the
flagged case accepted. Each sets only its rule's measures, which no other rule of its kind uses. -/

def pyTests (vs : List View) : String :=
  let one (v : View) : String := match v.test with
    | none => ""
    | some r =>
      let name := if v.testRenamed then s!"test_r{r.id}_case" else s!"test_r{r.id}"
      let vals (x : String) := "{" ++ ", ".intercalate (r.measures.zipIdx.map fun (m, i) =>
        s!"\"{m}\": {if i == 0 then x else "0"}") ++ "}"
      let reach := if v.testBelow then s!"st.integers(0, {r.bound - 1})" else s!"st.integers({r.bound}, {r.bound + 40})"
      let assertion := if v.testBelow then "is not None" else "is None"
      -- A sum's bound split across its two measures, at it and one below it, so a test reaches
      -- every term: with either term dropped the split at the bound falls below it.
      let split (total : Nat) : String := match r.measures with
        | [m1, m2] => s!"\{\"{m1}\": {total - total / 2}, \"{m2}\": {total / 2}}"
        | _ => ""
      let splitCases := match r.measures with
        | [_, _] =>
          let atBound := if v.testBelow then "is not None" else "is None"
          s!"    assert handle(Req(\"{r.kind}\", {split (if v.testBelow then r.bound - 1 else r.bound)})) {atBound}\n    assert handle(Req(\"{r.kind}\", {split (r.bound - 1)})) is not None\n"
        | _ => ""
      let base := s!"@given({reach})\ndef {name}(v):  # r{r.id}\n    assert handle(Req(\"{r.kind}\", {vals "v"})) {assertion}\n    assert handle(Req(\"{r.kind}\", {vals (toString (r.bound - 1))})) is not None\n{splitCases}"
      let exempt := match r.flag with
        | some f => s!"\n\n@given(st.integers({r.bound}, {r.bound + 40}))\ndef test_r{r.id}_exempt(v):  # r{r.id}-exempt\n    vals = {vals "v"}\n    vals[\"{f}\"] = 1\n    assert handle(Req(\"{r.kind}\", vals)) is not None\n"
        | none => ""
      base ++ exempt
  "\"\"\"Property tests of the generated fixture, one per clause, named by its ledger row.\"\"\"\n\n" ++
  "from hypothesis import given, settings, strategies as st\n\nfrom loans import Req, handle\n\n" ++
  "settings.register_profile(\"fixture\", database=None, max_examples=20)\nsettings.load_profile(\"fixture\")\n\n\n" ++
  "\n\n".intercalate ((vs.map one).filter (· ≠ "")) ++ "\n"

def files (vs : List View) : List (String × String) :=
  [("loans.md", prose vs), ("Loans.lean", leanFile vs), ("loans.py", pythonFile vs),
   ("test_loans.py", pyTests vs)]

open SpecTools.Owners in
/-- Every owners' blind spot plants something the agent reads: applied alone to the plain views,
it changes the artifacts' files other than the prose (`loans.md`, which the owner's text
replaces). Checked for each plant of each variant at each owner's seed. -/
example : ownerSeeds.all fun (v, seed) =>
      let all := ownerRules seed (ruleCount + 1) v
      let rs := all.take ruleCount
      let flawed := (imperfections seed rs v.flawKinds).map (·.rule)
      let plain := rs.map View.plain
      let artifacts (vs : List View) := (files vs).filter (·.1 != "loans.md")
      (List.range 12).all fun i =>
        (ownerVariant rs (all.getLastD default) flawed seed i 2).2.all fun p =>
          artifacts (p.apply plain) != artifacts plain := by
  native_decide

end SpecTools.Targets.Python
