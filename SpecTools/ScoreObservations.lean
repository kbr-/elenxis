import SpecTools.Gaps
import Std.Data.HashMap.Lemmas
import Std.Data.HashSet.Lemmas

/-!
Evidence for each scoring observation. The protected key names the properties in its own
namespace. A finding's evidence identity comes from its recorded source, and the matching fields
are independent of its free-form explanation.
-/

namespace SpecTools.Score.Observations
open SpecTools.Gaps
open Lean

inductive Part where
  | main
  | exception
  deriving Repr, BEq, ReflBEq, LawfulBEq, Hashable, DecidableEq, FromJson, ToJson

structure Location where
  rule : Nat
  part : Part
  deriving Repr, BEq, ReflBEq, LawfulBEq, Hashable, DecidableEq, FromJson, ToJson

structure Plant where
  id : Nat
  location : Location
  property : String
  kind : Kind
  deriving Repr

local instance : FromJson Kind where
  fromJson? json := do
    let name : String ← fromJson? json
    let some kind := Kind.parse name | throw "unknown defect category"
    pure kind

deriving instance FromJson for Plant

structure EvidenceFinding where
  evidenceId : String
  location : Option Location
  property : Option String
  kind : Option Kind
  deriving Repr, DecidableEq, FromJson

private inductive Slot where
  | single (finding : EvidenceFinding)
  | conflict

private def Slot.finding? : Slot → Option EvidenceFinding
  | .single finding => some finding
  | .conflict => none

private def update (finding : EvidenceFinding) : Option Slot → Option Slot
  | none => some (.single finding)
  | some (.single previous) => some (if previous = finding then .single finding else .conflict)
  | some .conflict => some .conflict

private def evidenceTable (findings : List EvidenceFinding) : Std.HashMap String Slot :=
  findings.foldr (fun finding table => table.alter finding.evidenceId (update finding)) ∅

private theorem table_cons (head : EvidenceFinding) (tail : List EvidenceFinding)
    (id : String) :
    (evidenceTable (head :: tail))[id]? =
      if head.evidenceId = id then update head (evidenceTable tail)[id]?
      else (evidenceTable tail)[id]? := by
  by_cases sameId : head.evidenceId = id
  · simp [evidenceTable, sameId]
  · simp [evidenceTable, Std.HashMap.getElem?_alter, sameId]

private theorem table_none (findings : List EvidenceFinding) (id : String) :
    (evidenceTable findings)[id]? = none ↔ ∀ finding ∈ findings, finding.evidenceId ≠ id := by
  induction findings with
  | nil => simp [evidenceTable]
  | cons head tail ih =>
    rw [table_cons]
    by_cases sameId : head.evidenceId = id
    · cases prior : (evidenceTable tail)[id]? with
      | none => simp [sameId, update]
      | some slot => cases slot <;> simp [sameId, update] <;> split <;> simp
    · simp [sameId, ih]

private theorem table_single (findings : List EvidenceFinding) (id : String)
    (finding : EvidenceFinding) :
    (evidenceTable findings)[id]? = some (.single finding) ↔
      finding ∈ findings ∧ finding.evidenceId = id ∧
        ∀ other ∈ findings, other.evidenceId = id → other = finding := by
  induction findings generalizing finding with
  | nil => simp [evidenceTable]
  | cons head tail ih =>
    rw [table_cons]
    by_cases sameId : head.evidenceId = id
    · cases prior : (evidenceTable tail)[id]? with
      | none =>
        have absent := (table_none tail id).mp prior
        simp only [ite_eq_left sameId, update, Option.some.injEq, Slot.single.injEq, List.mem_cons]
        grind
      | some slot =>
        cases slot with
        | single existing =>
          have verified := (ih existing).mp prior
          simp only [ite_eq_left sameId, update, List.mem_cons]
          split <;> grind
        | conflict =>
          simp only [ite_eq_left sameId, update, Option.some.injEq, reduceCtorEq, false_iff]
          intro ⟨_, hasId, agrees⟩
          have existing := agrees head List.mem_cons_self sameId
          have inTail : finding ∈ tail := by
            by_cases present : finding ∈ tail
            · exact present
            · have empty := (table_none tail id).mpr (by grind)
              simp [prior] at empty
          have single := (ih finding).mpr ⟨inTail, hasId, by grind⟩
          simp [prior] at single
    · simp only [ite_eq_right sameId, ih, List.mem_cons]
      grind

/-- An identity has one usable observation when its repeated occurrences agree. -/
def coherent (findings : List EvidenceFinding) : List EvidenceFinding :=
  (evidenceTable findings).toList.filterMap fun (_, slot) => slot.finding?

theorem coherent_exact (findings : List EvidenceFinding) (finding : EvidenceFinding) :
    finding ∈ coherent findings ↔ finding ∈ findings ∧
      ∀ other ∈ findings, other.evidenceId = finding.evidenceId → other = finding := by
  rw [coherent, List.mem_filterMap]
  constructor
  · rintro ⟨⟨id, slot⟩, member, found⟩
    cases slot with
    | conflict => simp [Slot.finding?] at found
    | single value =>
      simp [Slot.finding?] at found
      subst value
      have ⟨present, hasId, agrees⟩ := (table_single findings id finding).mp
        (Std.HashMap.mem_toList_iff_getElem?_eq_some.mp member)
      exact ⟨present, by simpa [hasId] using agrees⟩
  · intro ⟨present, agrees⟩
    exact ⟨(finding.evidenceId, .single finding),
      Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr
        ((table_single findings finding.evidenceId finding).mpr ⟨present, rfl, agrees⟩), rfl⟩

theorem coherent_ids_nodup (findings : List EvidenceFinding) :
    ((coherent findings).map EvidenceFinding.evidenceId).Nodup := by
  have hasId (id : String) (slot : Slot) (finding : EvidenceFinding)
      (member : (id, slot) ∈ (evidenceTable findings).toList)
      (selected : slot.finding? = some finding) : finding.evidenceId = id := by
    cases slot with
    | conflict => simp [Slot.finding?] at selected
    | single value =>
      simp [Slot.finding?] at selected
      subst value
      exact ((table_single findings id finding).mp
        (Std.HashMap.mem_toList_iff_getElem?_eq_some.mp member)).2.1
  rw [List.Nodup, List.pairwise_map, coherent, List.pairwise_filterMap]
  apply (evidenceTable findings).distinct_keys_toList.imp_of_mem
  rintro ⟨leftId, leftSlot⟩ ⟨rightId, rightSlot⟩ leftMember rightMember different
    left leftSelected right rightSelected equal
  have idEqual := (hasId leftId leftSlot left leftMember leftSelected).symm.trans
    (equal.trans (hasId rightId rightSlot right rightMember rightSelected))
  simp [idEqual] at different

def classifies (plant : Plant) (finding : EvidenceFinding) : Bool :=
  decide (finding.location = some plant.location ∧ finding.property = some plant.property ∧
    finding.kind = some plant.kind)

/-- The score key is indexed by public property identity. Its plant IDs stay in the scorer. -/
abbrev Key := Std.HashMap String Plant

structure KeyFile where
  version : Nat
  plants : List Plant
  deriving FromJson

structure FindingsFile where
  version : Nat
  findings : List EvidenceFinding
  deriving FromJson

def localized (key : Key) (findings : List EvidenceFinding) : List Location :=
  let locations := Std.HashSet.ofList (key.toList.map fun (_, plant) => plant.location)
  (Std.HashSet.ofList ((coherent findings).filterMap fun finding =>
    finding.location.filter (locations.contains ·))).toList

theorem localized_nodup (key : Key) (findings : List EvidenceFinding) :
    (localized key findings).Nodup := by
  let locations := Std.HashSet.ofList (key.toList.map fun (_, plant) => plant.location)
  let found := (coherent findings).filterMap fun finding =>
    finding.location.filter (locations.contains ·)
  simpa [localized, List.Nodup, locations, found] using (Std.HashSet.ofList found).distinct_toList

theorem localized_exact (key : Key) (findings : List EvidenceFinding) (location : Location) :
    location ∈ localized key findings ↔
      (∃ entry ∈ key.toList, entry.2.location = location) ∧
        ∃ finding ∈ coherent findings, finding.location = some location := by
  simp only [localized, Std.HashSet.mem_toList, Std.HashSet.mem_ofList,
    List.contains_iff_mem, List.mem_filterMap]
  constructor
  · rintro ⟨finding, present, filtered⟩
    cases found : finding.location with
    | none => simp [found] at filtered
    | some loc =>
      let locations := Std.HashSet.ofList (key.toList.map fun (_, plant) => plant.location)
      by_cases located : locations.contains loc
      · have equal : loc = location := by simpa [found, Option.filter, locations, located] using filtered
        subst loc
        exact ⟨List.mem_map.mp (List.contains_iff_mem.mp (Std.HashSet.mem_ofList.mp
          (Std.HashSet.contains_iff_mem.mp located))), finding, present, found⟩
      · simp [found, Option.filter, locations, located] at filtered
  · rintro ⟨located, finding, present, found⟩
    have contains : (Std.HashSet.ofList
        (key.toList.map fun (_, plant) => plant.location)).contains location = true :=
      Std.HashSet.contains_iff_mem.mpr
      (Std.HashSet.mem_ofList.mpr (List.contains_iff_mem.mpr (List.mem_map.mpr located)))
    exact ⟨finding, present, by simp [found, Option.filter, contains]⟩

private def classification (key : Key) (finding : EvidenceFinding) : Option Nat := do
  let property ← finding.property
  let plant ← key[property]?
  if classifies plant finding then some plant.id else none

def classified (key : Key) (findings : List EvidenceFinding) : List Nat :=
  (Std.HashSet.ofList ((coherent findings).filterMap (classification key))).toList

theorem main_ne_exception (rule : Nat) :
    (⟨rule, .main⟩ : Location) ≠ ⟨rule, .exception⟩ := by
  intro equal
  cases equal

theorem classifies_exact (plant : Plant) (finding : EvidenceFinding) :
    classifies plant finding = true ↔ finding.location = some plant.location ∧
      finding.property = some plant.property ∧ finding.kind = some plant.kind := by
  simp [classifies]

theorem classified_is_witnessed (key : Key) (findings : List EvidenceFinding) (id : Nat)
    (observed : id ∈ classified key findings) :
    ∃ plant ∈ key.toList.map Prod.snd, plant.id = id ∧
      ∃ finding ∈ coherent findings, classifies plant finding = true := by
  have matched := List.contains_iff_mem.mp
    (Std.HashSet.mem_ofList.mp (Std.HashSet.mem_toList.mp observed))
  obtain ⟨finding, coherentFinding, classifiedId⟩ := List.mem_filterMap.mp matched
  unfold classification at classifiedId
  cases property : finding.property with
  | none => simp [property] at classifiedId
  | some identity =>
    cases indexed : key[identity]? with
    | none => simp [property, indexed] at classifiedId
    | some plant =>
      by_cases conforms : classifies plant finding = true
      · have idEq : plant.id = id := by simpa [property, indexed, conforms] using classifiedId
        have member := Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr indexed
        exact ⟨plant, List.mem_map.mpr ⟨(identity, plant), member, rfl⟩, idEq,
          finding, coherentFinding, conforms⟩
      · simp [property, indexed, conforms] at classifiedId

theorem classifications_bounded (key : Key) (findings : List EvidenceFinding) :
    (classified key findings).Nodup ∧ (classified key findings).length ≤ (coherent findings).length := by
  constructor
  · exact (by simpa [classified, List.Nodup] using
      (Std.HashSet.ofList ((coherent findings).filterMap (classification key))).distinct_toList)
  · rw [classified, Std.HashSet.length_toList]
    exact Nat.le_trans Std.HashSet.size_ofList_le (List.length_filterMap_le _ _)

def report (key : KeyFile) (observations : FindingsFile) : Except String Json := do
  unless key.version == 1 && observations.version == 1 do
    throw "the score key and findings must both use version 1"
  let mut properties : Key := ∅
  let mut plantIds : Std.HashSet Nat := ∅
  for plant in key.plants do
    if plant.property.isEmpty || properties.contains plant.property || plantIds.contains plant.id then
      throw "the score key requires unique plant IDs and unique nonempty property identities"
    properties := properties.insert plant.property plant
    plantIds := plantIds.insert plant.id
  if observations.findings.any (·.evidenceId.isEmpty) then
    throw "a finding requires a nonempty evidence identity"
  return Json.mkObj [
    ("version", toJson key.version),
    ("located", toJson ((localized properties observations.findings).mergeSort fun left right =>
      left.rule < right.rule || (left.rule == right.rule &&
        (left.part == .main || right.part == .exception)))),
    ("classified", toJson ((classified properties observations.findings).mergeSort (· ≤ ·))),
    ("distinguished", toJson "unknown"),
    ("humanReviewed", toJson "unknown")]

end SpecTools.Score.Observations
