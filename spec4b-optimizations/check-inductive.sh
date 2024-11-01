#!/usr/bin/env bash
#
# Run the experiments to check inductiveness.

if [ "$APALACHE_HOME" == "" ]; then
    echo "set APALACHE_HOME to the Apalache installation directory"
    exit 1
fi

parallel --joblog joblog-inductive.txt --results out/ --colsep ',' \
    -a experiments-inductive.csv \
    /usr/bin/time -f "'%Uuser %Ssystem %elapsed %Mmaxk'" \
    ${APALACHE_HOME}/bin/apalache-mc check --init={2} --length={3} --inv={4} {1}
