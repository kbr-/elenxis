import SpecTools
import SpecTools.BenchmarkReview

namespace SpecTools.ProofInventory
open Lean Elab Command

/-- Named release obligations that must use the same foundations as the ledger. -/
def obligations : List Name := [
  ``Ledger.proved_declarations_and_premises,
  ``Ledger.unrelated_evidence_cannot_supply_domain,
  ``Ledger.contradiction_prevents_proved,
  ``Gaps.accept_exact,
  ``Gaps.proposal_cannot_be_proved,
  ``Gaps.mergeReadings_majority,
  ``Gaps.contractBindingIssues_empty_iff,
  ``Score.found_missed,
  ``Score.Observations.localized_nodup,
  ``Score.Observations.main_ne_exception,
  ``Score.Observations.classifies_exact,
  ``Score.Observations.classified_is_witnessed,
  ``Score.Observations.classifications_bounded,
  ``Score.Evidence.Counterexample.sound,
  ``Score.Evidence.directions_disjoint,
  ``Score.Evidence.searchExhaustive_none_iff,
  ``Score.Evidence.reviewed_attributed,
  ``FiniteGaps.search_sound,
  ``FiniteGaps.search_none_iff,
  ``Generated.gvariant_preserves,
  ``Generated.refusalBinding_has_declaration,
  ``Generated.emitted_refusal_has_binding,
  ``Generated.emitsRefusalAux_iff,
  ``Generated.exceptionBinding_iff,
  ``Generated.raisedBound_missing,
  ``Generated.droppedException_extra,
  ``Generated.twinException_extra,
  ``Generated.omittedMeasure_missing,
  ``Clauses.mem_differences,
  ``Replay.decode_ok_iff,
  ``Usage.total_append,
  ``Model.ask_refused_runs_nothing,
  ``Model.finish_nonzero_exit,
  ``Model.finish_answer_conforms,
  ``Model.codex_question_read_only,
  ``Model.nextEffect_schedules_iff,
  ``Model.observe_success_reuses,
  ``SyntheticRun.runLockedCheck_refused,
  ``OwnerApproval.accepts_iff,
  ``Benchmark.same_budget,
  ``Benchmark.Review.hit_iff,
  ``Benchmark.Review.hits_bounded]

def check (names : List Name) : CommandElabM Unit := do
  for name in names do
    let issues ← Adversarial.proofIssues name
    unless issues.isEmpty do
      throwError "{String.intercalate "\n" issues}"
    let axioms ← liftCoreM (collectAxioms name)
    IO.println s!"kernel: {name}: {axioms.toList}"

private def compilerAxiom (env : Environment) (name : Name) : Bool := Id.run do
  let some (.axiomInfo info) := env.find? name | return false
  let args := info.type.getAppArgs
  unless info.type.isAppOfArity ``Eq 3 && args[0]?.any (·.isConstOf ``Bool) &&
      args[2]?.any (·.isConstOf ``Bool.true) do
    return false
  return match (name.toString.splitOn ".").reverse with
  | suffix :: tactic :: "_native" :: _ =>
    match suffix.splitOn "_" with
    | "ax" :: indices@(_ :: _) =>
      indices.all (·.toNat?.isSome) && (tactic == "decide" || tactic == "native_decide")
    | _ => false
  | _ => false

/-- Imported executable definitions and proofs are checked for unclassified dependencies. -/
def checkProduct : CommandElabM Unit := do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let names := env.constants.fold (init := #[]) fun result name info =>
    let home := (env.getModuleIdxFor? name).bind fun idx => modules[idx.toNat]?
    if !home.any (fun moduleName => (`SpecTools : Name).isPrefixOf moduleName) then result else
      match info with
      | .thmInfo _ | .defnInfo _ | .opaqueInfo _ | .axiomInfo _ => result.push name
      | _ => result
  for name in names.qsort Name.lt do
    let axioms ← liftCoreM (collectAxioms name)
    let extra := axioms.filter (!Ledger.acceptedAxioms.contains ·)
    let unknown := extra.filter (!compilerAxiom env ·)
    unless unknown.isEmpty do
      throwError "{name}: unaccepted product axioms {unknown.toList}"
    unless extra.isEmpty do
      IO.println s!"compiler-dependent: {name}: {extra.toList}"
  IO.println s!"product declarations audited: {names.size}"

#eval show CommandElabM Unit from do
  check obligations
  checkProduct

end SpecTools.ProofInventory
