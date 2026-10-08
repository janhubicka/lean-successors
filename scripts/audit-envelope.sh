#!/usr/bin/env bash
# Both CI entry points use this runner; audit inventories are kept in one place.
# Run after building SuccessorTree.EnvelopeTheorem.
set -euo pipefail
cd "$(dirname "$0")/.."
out=${1:-proof-audit}
mkdir -p "$out"

audit() {
    local source=$1 log=$2 count=$3
    if ! lake env lean "$source" > "$out/$log" 2>&1; then
        cat "$out/$log"
        return 1
    fi
    if ! python3 scripts/check-axiom-log.py "$out/$log" "$count"; then
        cat "$out/$log"
        return 1
    fi
}

audit scripts/CheckEnvelope.lean envelope-axioms.log 31
audit scripts/CheckEnvelopeLevels.lean envelope-levels-axioms.log 8
