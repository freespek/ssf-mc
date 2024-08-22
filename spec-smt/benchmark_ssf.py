#!/usr/bin/env python3

# Generate benchmarks for the 3SF problem and time CVC5 on them.
#
# This script generates benchmarks with increasing number of blocks and
# checkpoints, and times CVC5 on each of them. The output is written to
# stdout in CSV format.
#
# WARNING!  This simply replaces a few lines in the model file by offsets.
# BRITTLE!  If the model file has changed, this script will break!

MODEL_FILENAME = 'ssf.smt'
BENCHMARK_FILENAME = 'benchmark.smt'
DATATYPE_LINE_OFFSETS = (28, 32)    # (last line to print, last line to exclude)

NODE_NAMES = ['Alice', 'Bob', 'Charlie', 'David', 'Eve', 'Frank', 'Grace',
              'Hank', 'Ivy', 'Jill', 'Karl', 'Liam', 'Mona', 'Nora', 'Omar',
              'Pete', 'Quin', 'Ruth', 'Sven', 'Tina', 'Ulla', 'Vera', 'Wade',
              'Xena', 'Yara', 'Zack']

def write_benchmark(max_blocks=3, max_checkpoints=5, max_nodes=4):
    with open(MODEL_FILENAME, 'r') as file:
        lines = file.readlines()

    with open(BENCHMARK_FILENAME, 'w') as file:
        file.write(''.join(lines[0:DATATYPE_LINE_OFFSETS[0]]))

        hashes = [f'(Hash{i+1})' for i in range(max_blocks)]
        checkpoints = [f'(C{i+1})' for i in range(max_checkpoints)]
        nodes = [f'({NODE_NAMES[i]})' for i in range(max_nodes)]

        file.write('(declare-datatype Hash (' + ' '.join(hashes) + '))\n')
        file.write('(declare-datatype Checkpoint (' + ' '.join(checkpoints) + '))\n')
        file.write('(declare-datatype Node (' + ' '.join(nodes) + '))\n')
        file.write(f'(define-fun N () Int {max_nodes})\n')

        file.write(''.join(lines[DATATYPE_LINE_OFFSETS[1]:]))

def check_sat():
    import subprocess
    import time

    start = time.time()
    result = subprocess.run(['cvc5', BENCHMARK_FILENAME], capture_output=True)
    end = time.time()

    time = end - start
    output = result.stdout.decode().strip().split('\n')[-1]
    return (time, output)

print(f'blocks,checkpoints,result,time')
for blocks in range (3, 6):
    for checkpoints in range(5, 8):
        write_benchmark(blocks, checkpoints)
        time, output = check_sat()
        print(f'{blocks},{checkpoints},{output},{time}')
