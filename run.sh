#!/usr/bin/bash -ex

DO_RUN=1

INPUT_PATTERN="samples/test1.lisp"

if [ $DO_RUN = 1 ]; then
    echo "running..."

    for fname in $INPUT_PATTERN; do
        echo "===== K run => $fname ====="
        cat $fname
        echo ""

        krun --debug $fname

        echo "exit code => $?"
    done
fi
