#!/bin/sh
# Deterministic replies for the owner process-boundary control.
set -eu
fixture=$1
request=$2
stage=${PWD##*/}
printf '%s\n' "$stage" >> "$fixture/calls"

next_index() {
    counter="$fixture/$1.count"
    index=0
    if test -f "$counter"; then
        read -r index < "$counter"
    fi
    printf '%s\n' "$((index + 1))" > "$counter"
}

case "$stage" in
    reading1|reading2)
        parent=${PWD%/*}
        exec cat "$fixture/${parent##*/}/$stage.json"
        ;;
esac
if grep -Fq '# Text to judge' "$request"; then
    next_index review
    cp "$request" "$fixture/review-$index.json"
    if test "$((index % 6))" -eq 2; then
        exec cat "$fixture/review-empty.json"
    fi
    exec cat "$fixture/review-notes.json"
elif grep -Fq 'If you had to bet' "$request"; then
    next_index development
    if test -f "$fixture/development-$index.json"; then
        exec cat "$fixture/development-$index.json"
    fi
    exec cat "$fixture/development-default.json"
elif grep -Fq '`human_probability`' "$request"; then
    exec cat "$fixture/score.json"
elif grep -Fq '# The message' "$request"; then
    exec cat "$fixture/held-out.json"
fi
exec cat "$fixture/document.json"
