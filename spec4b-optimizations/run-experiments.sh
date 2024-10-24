#!/usr/bin/env bash

parallel --joblog joblog.txt --results out/ --colsep ',' \
    -a exp.csv \
    /usr/bin/time -f "'%Uuser %Ssystem %elapsed %Mmaxk'" apalache-mc check --init={2} --inv={3} {1}