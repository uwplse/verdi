#!/usr/bin/env bash

set -e

if ! [ -f _CoqProject ]; then
    exit 0
fi

if [ "${TRAVIS}x" != "x" ]; then
    exit 0
fi


grep '\.v' _CoqProject | sort > build.files
find . -name '*.v' | sed 's!^\./!!' | sort > files

comm -23 files build.files > files.missing.from.build
comm -13 files build.files > nonexistant.build.files

EXIT_CODE=0

if [ -s files.missing.from.build ]
then
    echo 'The following files are present but missing from Makefile.coq.'
    echo 'Perhaps you have added a new file and should rerun ./configure?'
    cat files.missing.from.build
    EXIT_CODE=1
fi

if [ -s nonexistant.build.files ]
then
    echo 'The following files are present in Makefile.coq but to not exist.'
    echo 'Perhaps you have deleted a file and should rerun ./configure?'
    cat nonexistant.build.files
    EXIT_CODE=1
fi

rm -f files build.files files.missing.from.build nonexistant.build.files
exit $EXIT_CODE
