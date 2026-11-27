-- SPDX-License-Identifier: Apache-2.0
module

public import Lean.Data.Json

/-!
A subset of JSON Schema, enough to state the shape of a model's answer: `type`, `properties`,
`required`, `additionalProperties` (a boolean), `items` and `enum`. A schema using any other keyword
is refused when it is read, so a schema can't ask for a check this validator would skip.
-/

public section

namespace SpecTools.Schema
open Lean

/-- The keywords this validator understands. -/
def keywords : List String :=
  ["type", "properties", "required", "additionalProperties", "items", "enum", "description"]

/-- The value types `type` may name. -/
def typeNames : List String := ["object", "array", "string", "number", "integer", "boolean", "null"]

/-- Why a schema is outside the subset, or nothing when it is inside. -/
partial def unsupported (schema : Json) : Option String :=
  match schema with
  | .obj fields =>
    let found := fields.toList.map (·.1)
    match found.find? (!keywords.contains ·) with
    | some key => some s!"keyword `{key}` is outside the supported subset"
    | none =>
      let typeProblem := match schema.getObjVal? "type" with
        | .ok (.str name) => if typeNames.contains name then none else some s!"unknown type `{name}`"
        | .ok _ => some "`type` must be one type name"
        | .error _ => none
      let additional := match schema.getObjVal? "additionalProperties" with
        | .ok (.bool _) | .error _ => none
        | .ok _ => some "`additionalProperties` must be a boolean"
      let inner := match schema.getObjVal? "properties" with
        | .ok (.obj props) => props.toList.findSome? fun (_, sub) => unsupported sub
        | .ok _ => some "`properties` must be an object"
        | .error _ => none
      let items := match schema.getObjVal? "items" with
        | .ok sub => unsupported sub
        | .error _ => none
      typeProblem <|> additional <|> inner <|> items
  | _ => some "a schema must be an object"

private def typeOf : Json → String
  | .null => "null"
  | .bool _ => "boolean"
  | .num n => if n.exponent == 0 then "integer" else "number"
  | .str _ => "string"
  | .arr _ => "array"
  | .obj _ => "object"

private def matchesType (expected : String) (value : Json) : Bool :=
  let actual := typeOf value
  actual == expected || (expected == "number" && actual == "integer")

/-- The first place `value` breaks `schema`, as a path and a reason, or nothing when it conforms.
The schema is assumed inside the subset (`unsupported` is `none`). -/
partial def violation (schema value : Json) (path : String := "$") : Option String :=
  let typeCheck := match schema.getObjVal? "type" with
    | .ok (.str expected) =>
      if matchesType expected value then none else some s!"{path}: expected {expected}, got {typeOf value}"
    | _ => none
  let enumCheck := match schema.getObjVal? "enum" with
    | .ok (.arr allowed) => if allowed.contains value then none else some s!"{path}: not one of the allowed values"
    | _ => none
  let objectCheck := match value with
    | .obj fields =>
      let required := match schema.getObjVal? "required" with
        | .ok (.arr names) => names.toList.filterMap fun (j : Json) => match j with
          | .str n => some n
          | _ => none
        | _ => []
      let missing := required.find? fun name => (fields.get? name).isNone
      let props := match schema.getObjVal? "properties" with
        | .ok (.obj props) => props
        | _ => {}
      let closed := match schema.getObjVal? "additionalProperties" with
        | .ok (.bool false) => true
        | _ => false
      match missing with
      | some name => some s!"{path}: missing required `{name}`"
      | none =>
        fields.toList.findSome? fun (name, sub) =>
          match props.get? name with
          | some subSchema => violation subSchema sub s!"{path}.{name}"
          | none => if closed then some s!"{path}: unexpected `{name}`" else none
    | _ => none
  let arrayCheck := match value, schema.getObjVal? "items" with
    | .arr elems, .ok itemSchema =>
      (elems.toList.zipIdx).findSome? fun (elem, i) => violation itemSchema elem s!"{path}[{i}]"
    | _, _ => none
  typeCheck <|> enumCheck <|> objectCheck <|> arrayCheck

end SpecTools.Schema

end
