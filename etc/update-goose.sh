#!/bin/bash

set -e

usage() {
  echo "Usage: $0"
  echo
  echo "Runs goose on code in go/ and outputs to src/Goose."
}

while [[ $# -gt 0 ]]; do
  case "$1" in
  -h | -help | --help)
    usage
    exit 0
    ;;
  -*)
    usage
    exit 1
    ;;
  *)
    break
    ;;
  esac
done

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
# run from repository root
cd "$DIR/.."

GOOSE_OUTPUT=src/code
GOOSE_CONFIG_DIR=src/code
PROOFGEN_OUTPUT=src/generatedproof

if which goose 1>/dev/null 2>&1; then
  # NOTE: requires new goose
  GOOSE=("goose")
else
  GOOSE=("go" "run" "github.com/goose-lang/goose/cmd/goose@new")
fi
if which proofgen 1>/dev/null 2>&1; then
  PROOFGEN=("proofgen")
else
  PROOFGEN=("go" "run" "github.com/goose-lang/goose/cmd/proofgen@new")
fi

"${GOOSE[@]}" -out "$GOOSE_OUTPUT" -dir go ./...
"${PROOFGEN[@]}" -out "$PROOFGEN_OUTPUT" -configdir "$GOOSE_CONFIG_DIR" -dir go ./...
