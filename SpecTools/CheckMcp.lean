-- SPDX-License-Identifier: Apache-2.0
import SpecTools.OwnerCheck

namespace SpecTools.CheckMcp

open Lean OwnerCheck

private def tool (name : String) : Json :=
  Json.mkObj [("name", toJson name), ("description", toJson s!"Run the {name} check"),
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

private def selectedCheck (profile : Profile) (params : Json) : Option String := do
  let name ← (params.getObjValAs? String "name").toOption
  if admitted profile name (params.getObjVal? "arguments").toOption then some name else none

/-- Serve a project's tools over line-delimited JSON-RPC. The caller binds the fixture and provides
the execution function. A malformed call is rejected before that function runs. -/
def serve (profile : Profile) (run : String → IO (Bool × String)) : IO Unit := do
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
              pure (reply id (Json.mkObj [("tools", toJson (profile.names.map tool))]))
            | some "tools/call" =>
              match (request.getObjVal? "params").toOption.bind (selectedCheck profile) with
              | none => pure (failure id (-32602)
                  s!"Select {String.intercalate ", " profile.names} with no arguments")
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
