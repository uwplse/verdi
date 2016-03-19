#!/usr/bin/env bash

function find-line {
    DIR=$1; shift
    EXCLUDE_PATH_REGEX=$1; shift
    LINE=$1; shift

    find -E "$DIR" -name '*.v' \( -not -regex "$EXCLUDE_PATH_REGEX" \) -exec grep -Hni "$LINE" {} \+
}

function find-redundant-imports {
    FILE_OF_IMPORTS=$1; shift
    EXCLUDE_PATH_REGEX=$1; shift

    sed -nE '/^[[:space:]]*(Require)?[[:space:]]+(Export)/p' "$FILE_OF_IMPORTS" | while read line
    do
        find-line "." "$EXCLUDE_PATH_REGEX" "${line//Export/Import}"
    done
}

echo "Looking for redundant imports."
find-redundant-imports core/Verdi.v ".*/(core|lib)/.*"
find-redundant-imports raft/Raft.v "(.*/(core|lib|systems)/.*)|(.*/Raft.v)"


# Delete imports:
# find . -proofs/ -name '*.v' \( -not -path '*/core/*' \) \
#      -print -exec sed -ibak '/Require Import Net/d' {} \;

echo "Looking for orphaned imports."
find . -name '*.v' \( -not -path '*/lib/*' \)  -exec awk -f script/orphaned-imports.awk {} \;
