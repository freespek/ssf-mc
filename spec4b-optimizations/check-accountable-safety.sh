#!/usr/bin/env bash
#
# Run the experiments to check accountable safety.

if [ "$APALACHE_HOME" == "" ]; then
    echo "set APALACHE_HOME to the Apalache installation directory"
    exit 1
fi

parallel --joblog joblog-as.txt --results out/ --colsep ',' \
    -a experiments-accountable-safety.csv \
    /usr/bin/time -f "'%Uuser %Ssystem %elapsed %Mmaxk'" \
    ${APALACHE_HOME}/bin/apalache-mc check --length=0 --init={2} --inv={3} {1}
