#!/bin/bash

### coqproject.sh
### Creates a _CoqProject file, including external dependencies.

## Configuration options

# External dependencies
DEPS=()

# Directories containing coq files
DIRS=(core lib systems raft raft-proofs extraction/vard/coq)

# Namespaces corresponding to directories. By default, everything is in "".
# To put "theories" in the "FermatsTheorem" namespace:
#   NAMESPACE_theories=FermatsTheorem
# Note that "." can't be part of a variable name, so it's replaced by "_".
# So, to put the current directory in the "FermatsTheorem" namespace:
#   NAMESPACE__=FermatsTheorem

# Extra files (e.g. automatically-generated .v files that won't be
# around at configure-time)
EXTRA=(raft/RaftState.v)

## Implementation

COQPROJECT_TMP=_CoqProject.tmp

rm -f $COQPROJECT_TMP

for dep in ${DEPS[@]}; do
    path_var="$dep"_PATH
    path=${!path_var:="../$dep"}
    if [ ! -d "$path" ]; then
        echo "$dep not found at $path."
        exit 1
    fi

    pushd "$path" > /dev/null
    path=$(pwd)
    popd > /dev/null
    echo "$dep found at $path"
    LINE="-Q $path $dep"
    echo $LINE >> $COQPROJECT_TMP
done

for dir in ${DIRS[@]}; do
    namespace_var=NAMESPACE_"$dir"
    namespace_var=${namespace_var//./_}
    namespace=${!namespace_var:="\"\""}
    LINE="-Q $dir $namespace"
    echo $LINE >> $COQPROJECT_TMP
done

for dir in ${DIRS[@]}; do
    echo >> $COQPROJECT_TMP
    find $dir -iname '*.v'  >> $COQPROJECT_TMP
done

for extra in ${EXTRA[@]}; do
    if ! grep --quiet "^$extra\$" $COQPROJECT_TMP; then
        echo >> $COQPROJECT_TMP
        echo $extra >> $COQPROJECT_TMP
    fi
done


mv $COQPROJECT_TMP _CoqProject
