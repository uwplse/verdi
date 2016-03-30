#!/usr/bin/env bash

function find_unused_imports_of_file {
    FILE=$1; shift

    echo "Considering file $FILE"

    cp "$FILE" "${FILE}.bak"
    N=0
    while read line
    do
        N=$((N+1))
        echo "read line $N:"
        echo "$line"

        # We assume that all imports happen at the top of the file.
        # We allow blank lines and lines containing "Arguments" to be
        # contained in the imports section.
        if [[ "$line" =~ .*(Require|Import|Export|Arguments).*|^[[:space:]]*$ ]]
        then
            # Only check import statements for necessity, not blank
            # lines or Arguments commands.
            if [[ "$line" =~ .*(Require|Import|Export).* ]]
            then
                echo; echo; echo
                echo "Testing whether $line is necessary"

                sed -i "${N}d" "$FILE"

                TARGET="$(dirname $FILE)/$(basename $FILE .v).vo"
                rm -f "$TARGET"
                make -f Makefile.coq "$TARGET"
                exit_code=$?
                if [[ $exit_code -eq 0 ]]
                then
                    echo "Build still passed with line $N removed from $FILE: "
                    echo "$line"
                fi
                cp "${FILE}.bak" "$FILE"
            fi
        else
            break
        fi
    done < "$FILE.bak"
    rm -f "$FILE.bak"
}

git status | grep modified && { echo ERROR: working directory not clean; exit 1; }

export -f find_unused_imports_of_file
find . -name '*.v' -exec /bin/bash -c 'find_unused_imports_of_file "$0"' {} \;
