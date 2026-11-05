import SpecTools.Ledger

/-!
The audit's verdicts, proved over all facts and rows: a missing name, an unaccepted axiom, a
hypothesis without a witness and an unclaimed theorem each show; a second run with nothing changed
re-judges nothing, and a changed row is re-judged while unchanged ones aren't.
-/

namespace SpecTools.Ledger
open Lean

theorem firstMissing_none {facts : Facts} {names : List Name} (h : firstMissing facts names = none) :
    ∀ n ∈ names, (facts n).isSome := by
  induction names with
  | nil => simp
  | cons m ms ih =>
    simp only [firstMissing] at h
    split at h
    · cases h
    · rename_i hm
      intro n hn
      rcases List.mem_cons.mp hn with rfl | hn
      · cases hf : facts n <;> simp_all
      · exact ih h n hn

theorem firstMissing_some {facts : Facts} {names : List Name} {n : Name}
    (h : firstMissing facts names = some n) : n ∈ names ∧ facts n = none := by
  induction names with
  | nil => simp [firstMissing] at h
  | cons m ms ih =>
    simp only [firstMissing] at h
    split at h
    · rename_i hm
      cases h
      exact ⟨List.mem_cons_self, by simpa using hm⟩
    · exact ⟨List.mem_cons_of_mem _ (ih h).1, (ih h).2⟩

/-- A row naming something that is no theorem is refused, naming it. -/
theorem verdict_missing (facts : Facts) (row : Row) (n : Name) (hn : n ∈ row.theorems ++ row.witnesses)
    (h : facts n = none) : ∃ m, verdict facts row = .missing m ∧ m ∈ row.theorems ++ row.witnesses ∧
      facts m = none := by
  unfold verdict
  split
  · rename_i m hm
    exact ⟨m, rfl, firstMissing_some hm⟩
  · rename_i hm
    have := firstMissing_none hm n hn
    simp [h] at this

/-- A proved verdict means: every name is a theorem, there is at least one, none rests on an
unaccepted axiom, and a hypothesis comes with a witness. -/
theorem verdict_proved (facts : Facts) (row : Row) (h : verdict facts row = .proved) :
    (∀ n ∈ row.theorems ++ row.witnesses, (facts n).isSome) ∧ row.theorems ≠ [] ∧
      unaccepted facts (row.theorems ++ row.witnesses) = [] ∧
      (row.theorems.any (fun n => (facts n).any (·.hypotheses)) → row.witnesses ≠ []) := by
  unfold verdict at h
  split at h
  · cases h
  · rename_i hm
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · rename_i hne
          split at h
          · cases h
          · rename_i hu
            split at h
            · split at h
              · cases h
              · rename_i hw
                refine ⟨firstMissing_none hm, by simpa using hne, hu, ?_⟩
                intro hany hnil
                apply hw
                simp [hnil, hany]
            · cases h

theorem proof_kinds_exclude (facts : Facts) (names : List Name)
    (proofs : ∀ n ∈ names, (facts n).any (·.kind == .theoremStatement) = true)
    (kind : StatementKind) (different : kind ≠ .theoremStatement) :
    names.find? (fun n => (facts n).any (·.kind == kind)) = none ∧
      names.any (fun n => (facts n).any (·.kind == kind)) = false := by
  have absent (n : Name) (member : n ∈ names) : (facts n).any (·.kind == kind) = false := by
    have known := proofs n member
    cases value : facts n with
    | none => simp [value] at known
    | some fact =>
      have proofKind : fact.kind = .theoremStatement := by simpa [value] using known
      simp [proofKind, Ne.symm different]
  have never (n : Name) (member : n ∈ names) : ¬ (facts n).any (·.kind == kind) = true := by
    rw [absent n member]
    decide
  exact ⟨List.find?_eq_none.mpr never, List.any_eq_false.mpr never⟩

/-- An axiom outside the accepted three makes the row conditional. -/
theorem verdict_conditional (facts : Facts) (row : Row) (hall : firstMissing facts (row.theorems ++ row.witnesses) = none)
    (hne : row.theorems ≠ []) (a : Name) (as : List Name)
    (hu : unaccepted facts (row.theorems ++ row.witnesses) = a :: as)
    (proofs : ∀ n ∈ row.theorems ++ row.witnesses, (facts n).any (·.kind == .theoremStatement) = true) :
    verdict facts row = .conditional (a :: as) := by
  have : row.theorems.isEmpty = false := by simpa using hne
  have valid := proof_kinds_exclude facts _ proofs .notProposition (by decide)
  have visible := proof_kinds_exclude facts _ proofs .unavailableBody (by decide)
  simp only [verdict, hall, valid.1, visible.1, this, Bool.false_eq_true, ↓reduceIte, hu]

/-- Hypotheses with no witness make the row too weak or vacuous. -/
theorem verdict_vacuous (facts : Facts) (row : Row) (hall : firstMissing facts row.theorems = none)
    (hne : row.theorems ≠ []) (hw : row.witnesses = [])
    (hu : unaccepted facts row.theorems = [])
    (hyp : row.theorems.any (fun n => (facts n).any (·.hypotheses)) = true)
    (proofs : ∀ n ∈ row.theorems, (facts n).any (·.kind == .theoremStatement) = true) :
    verdict facts row = .tooWeakOrVacuous := by
  have : row.theorems.isEmpty = false := by simpa using hne
  have valid := proof_kinds_exclude facts _ proofs .notProposition (by decide)
  have visible := proof_kinds_exclude facts _ proofs .unavailableBody (by decide)
  have allProofs := List.all_eq_true.mpr proofs
  simp only [verdict, hw, List.append_nil, hall, valid.1, visible.1, this,
    Bool.false_eq_true, ↓reduceIte, hu, allProofs, List.isEmpty_nil, hyp, Bool.and_self]

theorem proved_requires_theorems (facts : Facts) (row : Row) (h : verdict facts row = .proved) :
    (row.theorems ++ row.witnesses).all (fun n => (facts n).any (·.kind == .theoremStatement)) = true := by
  unfold verdict at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · split at h
            · assumption
            · cases h

theorem unproved_requirement_never_proved (facts : Facts) (row : Row) (name : Name)
    (member : name ∈ row.theorems ++ row.witnesses) (fact : Fact)
    (found : facts name = some fact) (requirement : fact.kind = .requirement) :
    verdict facts row ≠ .proved := by
  intro claimed
  have kinds := List.all_eq_true.mp (proved_requires_theorems facts row claimed) name member
  simp [found, requirement] at kinds

theorem requirement_kind_exact (proposition body unsafeBody : Bool) :
    requirementKind proposition body unsafeBody = .requirement ↔
      proposition = true ∧ body = true ∧ unsafeBody = false := by
  cases proposition <;> cases body <;> cases unsafeBody <;> decide

theorem empty_specification_refuses (facts : Facts) :
    specificationIssues facts [] = ["the specification ledger is empty"] := rfl

theorem proof_audit_unchanged (facts : Facts) (rows : List Row) :
    auditIssues false facts rows = [] := rfl

theorem proof_summary_unchanged (specified : Nat) : specificationSuffix false specified = "" := rfl

theorem requirement_summary_explicit (specified : Nat) :
    specificationSuffix true specified = s!", {specified} specified (unproved)" := rfl

theorem declaration_finding_reported (facts : Facts) (rows : List Row) (row : Row)
    (name : Name) (finding : SpecificationFinding) (member : row ∈ rows)
    (named : name ∈ row.theorems ++ row.witnesses)
    (reported : declarationFinding facts row.id name = some finding) :
    finding ∈ specificationFindings facts rows := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨row, member, ?_⟩
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_right
  apply List.mem_filterMap.mpr
  exact ⟨name, by simpa using named, reported⟩

theorem missing_declaration_reported (facts : Facts) (rows : List Row) (row : Row)
    (name : Name) (member : row ∈ rows) (named : name ∈ row.theorems ++ row.witnesses)
    (missing : facts name = none) :
    SpecificationFinding.missing row.id name ∈ specificationFindings facts rows := by
  apply declaration_finding_reported facts rows row name _ member named
  simp [declarationFinding, missing]

theorem accepted_requirement_has_no_finding (facts : Facts) (id : String) (name : Name)
    (fact : Fact) (found : facts name = some fact) (requirement : fact.kind = .requirement)
    (trusted : fact.axioms = []) : declarationFinding facts id name = none := by
  simp [declarationFinding, found, requirement, Fact.unacceptedAxioms, trusted]

theorem non_proposition_reported (facts : Facts) (rows : List Row) (row : Row)
    (name : Name) (fact : Fact) (member : row ∈ rows)
    (named : name ∈ row.theorems ++ row.witnesses) (found : facts name = some fact)
    (wrong : fact.kind = .notProposition) :
    SpecificationFinding.notProposition row.id name ∈ specificationFindings facts rows := by
  apply declaration_finding_reported facts rows row name _ member named
  simp [declarationFinding, found, wrong]

theorem unavailable_body_reported (facts : Facts) (rows : List Row) (row : Row)
    (name : Name) (fact : Fact) (member : row ∈ rows)
    (named : name ∈ row.theorems ++ row.witnesses) (found : facts name = some fact)
    (unavailable : fact.kind = .unavailableBody) :
    SpecificationFinding.unavailableBody row.id name ∈ specificationFindings facts rows := by
  apply declaration_finding_reported facts rows row name _ member named
  simp [declarationFinding, found, unavailable]

theorem not_proposition_kind (body unsafeBody : Bool) :
    requirementKind false body unsafeBody = .notProposition := rfl

theorem missing_body_kind (unsafeBody : Bool) :
    requirementKind true false unsafeBody = .unavailableBody := rfl

theorem unsafe_body_kind (body : Bool) :
    requirementKind true body true = .unavailableBody := by cases body <;> rfl

theorem unproved_witness_finding (facts : Facts) (id : String) (name : Name) (fact : Fact)
    (found : facts name = some fact) (requirement : fact.kind = .requirement) :
    witnessFinding facts id name = some (.unprovedWitness id name) := by
  simp [witnessFinding, found, requirement]

theorem unproved_witness_reported (facts : Facts) (rows : List Row) (row : Row) (name : Name)
    (fact : Fact) (member : row ∈ rows) (named : name ∈ row.witnesses)
    (found : facts name = some fact) (requirement : fact.kind = .requirement) :
    SpecificationFinding.unprovedWitness row.id name ∈ specificationFindings facts rows := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨row, member, ?_⟩
  apply List.mem_append_left
  apply List.mem_append_right
  apply List.mem_filterMap.mpr
  exact ⟨name, by simpa using named, unproved_witness_finding facts row.id name fact found requirement⟩

theorem validation_exact (requirements : Bool) (facts : Facts) (rows : List Row) :
    validateRequirements requirements facts rows = .ok () ↔ auditIssues requirements facts rows = [] := by
  unfold validateRequirements
  split <;> simp_all

example : specificationFindings
    (fun _ => some { statement := "True", axioms := [], hypotheses := false, kind := .requirement })
    [{ id := "clause", clause := "required behavior", theorems := [`obligation] }] = [] := by decide

example : SpecificationFinding.missing "clause" `second ∈ specificationFindings (fun _ => none)
    [{ id := "clause", clause := "required behavior", theorems := [`first, `second] }] := by decide

/-- A written theorem is reported exactly when no row claims it. -/
theorem mem_unclaimed (rows : List Row) (written : List Name) (n : Name) :
    n ∈ unclaimed rows written ↔ n ∈ written ∧ ∀ r ∈ rows, n ∉ r.theorems ++ r.witnesses := by
  simp [unclaimed]

/-- A second run after storing a run's digests re-judges no row. -/
theorem toRejudge_after_store (facts : Facts) (rows : List Row) (hids : (rows.map (·.id)).Nodup) :
    toRejudge (digests facts rows) facts rows = [] := by
  rw [toRejudge, List.filter_eq_nil_iff]
  intro r hr
  simp only [bne_iff_ne, ne_eq, Decidable.not_not]
  induction rows with
  | nil => simp at hr
  | cons s ss ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hids
    simp only [digests, List.map_cons, List.lookup_cons]
    rcases List.mem_cons.mp hr with rfl | hr
    · simp
    · have hne : (r.id == s.id) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro he
        exact hids.1 ⟨r, hr, he⟩
      simp only [hne]
      exact ih hids.2 hr

/-- Only rows whose digest moved are re-judged: a row whose stored digest equals its current one is
not, and one whose digest changed is. -/
theorem mem_toRejudge (stored : List (String × UInt64)) (facts : Facts) (rows : List Row) (r : Row) :
    r ∈ toRejudge stored facts rows ↔ r ∈ rows ∧ stored.lookup r.id ≠ some (digest facts r) := by
  simp [toRejudge]

end SpecTools.Ledger
