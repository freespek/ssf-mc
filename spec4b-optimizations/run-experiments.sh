#!/usr/bin/env bash

if [ "$APALACHE_HOME" == "" ]; then
    echo "set APALACHE_HOME to the Apalache installation directory"
    exit 1
fi

parallel --joblog joblog.txt --results out/ --colsep ',' \
    -a exp.csv \
    /usr/bin/time -f "'%Uuser %Ssystem %elapsed %Mmaxk'" ${APALACHE_HOME}/bin/apalache-mc check --init={2} --inv={3} {1}
