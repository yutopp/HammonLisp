#!/usr/bin/bash -ex

DO_BUILD=1

if [ $DO_BUILD = 1 ]; then
    echo "compiling..."

    kompile --debug hammon-lisp.k && echo "compiled"
fi
