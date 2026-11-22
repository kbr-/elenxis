import SpecTools.OwnerCheck

namespace SpecTools.CheckMcp

open Lean OwnerCheck

private def tool (check : Check) : Json :=
  Json.mkObj [("name", toJson check.name), ("description", toJson s!"Run the {check.name} check"),
    ("inputSchema", Json.mkObj [("type", toJson "object"), ("properties", Json.mkObj []),
      ("additionalProperties", toJson false)])]

private def reply (id result : Json) : Json :=
  Json.mkObj [("jsonrpc", toJson "2.0"), ("id", id), ("result", result)]

private def failure (id : Json) (code : Int) (message : String) : Json :=
  Json.mkObj [("jsonrpc", toJson "2.0"), ("id", id),
    ("error", Json.mkObj [("code", toJson code), ("message", toJson message)])]

private def initialized : Json :=
  Json.mkObj [("protocolVersion", toJson "2025-06-18"),
    ("capabilities", Json.mkObj [("tools", Json.mkObj [])]),
    ("serverInfo", Json.mkObj [("name", toJson "elenxis"), ("version", toJson "1")])]

private def selectedCheck (params : Json) : Option Check := do
  let name ← (params.getObjValAs? String "name").toOption
  decode name (params.getObjVal? "arguments").toOption

example : selectedCheck (Json.mkObj [("name", toJson "gaps")]) = some .gaps := by native_decide
example : selectedCheck (Json.mkObj [("name", toJson "gaps"),
    ("arguments", Json.mkObj [("fixture", toJson "other")])]) = none := by native_decide
example : selectedCheck (Json.mkObj [("name", toJson "missing")]) = none := by native_decide

/-- Serve the four tools over line-delimited JSON-RPC. The caller binds the fixture and provides
the execution function. A malformed call is rejected before that function runs. -/
def serve (run : Check → IO (Bool × String)) : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let response ← match Json.parse line with
      | .error _ => pure (some (failure .null (-32700) "Invalid JSON"))
      | .ok request => do
        let method := request.getObjValAs? String "method"
        let version := (request.getObjValAs? String "jsonrpc").toOption
        let id := (request.getObjVal? "id").toOption
        if version != some "2.0" || method.toOption.isNone then
          pure (some (failure (id.getD .null) (-32600) "Invalid request"))
        else if let some id := id then
          let answer ← match method.toOption with
            | some "initialize" => pure (reply id initialized)
            | some "ping" => pure (reply id (Json.mkObj []))
            | some "tools/list" =>
              pure (reply id (Json.mkObj [("tools", toJson (Check.all.map tool))]))
            | some "tools/call" =>
              match (request.getObjVal? "params").toOption.bind selectedCheck with
              | none => pure (failure id (-32602) "Select audit, tests, gaps or clauses with no arguments")
              | some check => do
                let (ok, report) ← run check
                pure (reply id (Json.mkObj [("isError", toJson (!ok)), ("content", Json.arr #[
                  Json.mkObj [("type", toJson "text"), ("text", toJson report)]])]))
            | _ => pure (failure id (-32601) "Unknown method")
          pure (some answer)
        else pure none
    if let some result := response then
      output.putStrLn result.compress
      output.flush

end SpecTools.CheckMcp
