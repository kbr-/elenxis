#!/usr/bin/env bash
# SPDX-License-Identifier: Apache-2.0
set -euo pipefail

# SSH and tar stage the synthetic input on the build host. Elenxis owns model routing.
if [[ $# -ne 6 ]]; then
  printf '%s\n' 'Usage: bash adapters/benchmark-with-caller-codex.sh BUILD-HOST BUILD-DIR COMPUTE CASES KEY TIMEOUT-MS' >&2
  exit 2
fi

build_host=$1
build_dir=$2
compute=$3
cases=$4
key=$5
timeout_ms=$6
caller_host=$(hostname)
caller_home=${CODEX_HOME:?Run from the active Codex session with CODEX_HOME set}
caller_thread=${CODEX_THREAD_ID:?Run from the active Codex session with CODEX_THREAD_ID set}

staged=$(mktemp -d)
trap 'rm -r -- "$staged"' EXIT
cp -- "$cases" "$staged/cases.json"
cp -- "$key" "$staged/key.json"

remote='
set -euo pipefail
cd "$HOME"
launcher=$(realpath -- "$2")
cd -- "$1"
staged=$(mktemp -d)
trap '\''rm -r -- "$staged"'\'' EXIT
tar -C "$staged" -xf -
status=0
"$launcher" --category external_tool --threads 4 --tail-bytes 1800 env \
  CODEX_HOME="$4" CODEX_THREAD_ID="$5" SPEC_TOOLS_HOST="$3" \
  .lake/build/bin/spec-tools benchmark "$staged/cases.json" "$staged/key.json" \
  "$staged/journal.jsonl" "$6" >&2 || status=$?
if [[ -f "$staged/journal.jsonl" ]]; then
  cat -- "$staged/journal.jsonl"
fi
exit "$status"
'
printf -v command 'bash -c %q _ %q %q %q %q %q %q' "$remote" \
  "$build_dir" "$compute" "$caller_host" "$caller_home" "$caller_thread" "$timeout_ms"
tar -C "$staged" -cf - cases.json key.json |
  ssh -o BatchMode=yes -o ConnectTimeout=8 -- "$build_host" "$command"
