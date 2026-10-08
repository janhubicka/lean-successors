#!/usr/bin/env bash
# Both CI entry points use this runner; named inventories live in the Lean files.
# Run after building SuccessorTree.EnvelopeTheorem.
set -euo pipefail
cd "$(dirname "$0")/.."
out=${1:-proof-audit}
mkdir -p "$out"

audit() {
    local source=$1 log=$2
    if ! lake env lean "$source" > "$out/$log" 2>&1; then
        cat "$out/$log"
        return 1
    fi
    if ! python3 scripts/check-axiom-log.py "$out/$log" "$source"; then
        cat "$out/$log"
        return 1
    fi
}

audit scripts/CheckEnvelope.lean envelope-axioms.log
audit scripts/CheckEnvelopeLevels.lean envelope-levels-axioms.log
