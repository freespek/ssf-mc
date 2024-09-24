# Alloy specification of 3SF tuned towards AccountableSafety

This directory contains an [Alloy][] specification of the 3SF protocol, which
abstracts the features that are not important for checking `AccountableSafety`.

We have written this specification in an attempt to check `AccountableSafety`
for small yet reasonable configurations.

Even though Alloy specifications are not the easiest ones to write, Alloy allows
us to precisely control the size of the input parameters and run optimized
satisfiability solvers.

## Experimental Setup

Since the SAT solver SAT4j shipped with Alloy is not very performant, we run the
experiments with an award-winning SAT solver called [Kissat][] by Armin Biere et
al. To reproduce the experiments, you have to build Kissat from sources by
following the installation instructions.

To generate a CNF file -- which a SAT solver is able to consume:

 1. Open an experiment file such as [ffg-exp1][] in the Alloy IDE.
 
 1. Check `Options`/`Solver: Output CNF to file`/`Output CNF to file`.
 
 1. Generate the file via `Execute`/`Run noAccountableSafety...`.
 
 1. Copy the generated file in a convenient location. We accompany every .als
    file with the generated .cnf file.

Finally, run the SAT solver against the file:

```sh
$ kissat --unsat ffg-exp1.cnf
```

The expected output is:

```
s UNSATISFIABLE
```

This means that the property `noAccountableSafety` does not have a model.
Hence, we were not able to find a counterexample to `AccountableSafety`.

## Experimental Results

Similar to the experiments with a [direct SMT encoding][smt-enc] for CVC5, we
conduct experiments for the same kinds of inputs:

| Input      | #blocks | #checkpoints | #signatures | #ffg_votes | #votes | runtime | memory  |
|------------|--------:|-------------:|------------:|-----------:|-------:|--------:|--------:|
| [ffg-exp1] |    3    |      5       |      4      |      5     |   12   |  4 sec  |  35 MB  |
| [ffg-exp2] |    4    |      5       |      4      |      5     |   12   | 10 sec  |  40 MB  |
| [ffg-exp3] |    5    |      5       |      4      |      5     |   12   | 15 sec  |  45 MB  |
| [ffg-exp4] |    3    |      6       |      4      |      6     |   15   | 57 sec  |  52 MB  |
| [ffg-exp5] |    4    |      6       |      4      |      6     |   15   | 167 sec |  55 MB  |
| [ffg-exp6] |    5    |      6       |      4      |      6     |   15   | 245 sec |  57 MB  |
| [ffg-exp7] |    6    |      6       |      4      |      6     |   15   | 360 sec |  82 MB  |
| [ffg-exp8] |    5    |      7       |      4      |      6     |   24   | X sec |  Y MB  |

In addition to the above experiments, we ran a few experiments that would have
the inputs of the size comparable to those produced by our TLA+ specification:

| Input       | #blocks | #checkpoints | #signatures | #ffg_votes | #votes | runtime | memory  |
|-------------|--------:|-------------:|------------:|-----------:|-------:|--------:|--------:|
| [ffg-exp10] |    3    |      15      |      4      |      5     |   12   | 31 sec  | 56 MB   |
| [ffg-exp11] |    4    |      20      |      4      |      5     |   12   | 152 sec | 94 MB   |
| [ffg-exp12] |    5    |      25      |      4      |      5     |   12   | 234 sec | 117 MB  |
| [ffg-exp13] |    7    |      35      |      4      |      10    |   40   | X sec | X MB  |


<!-- References -->

[Alloy]: https://alloytools.org/
[Kissat]: https://github.com/arminbiere/kissat
[smt-enc]: ../smt-spec/README.md
[ffg-exp1]: ./ffg-exp1.als
[ffg-exp2]: ./ffg-exp2.als
[ffg-exp3]: ./ffg-exp3.als
[ffg-exp4]: ./ffg-exp4.als
[ffg-exp5]: ./ffg-exp5.als
[ffg-exp6]: ./ffg-exp6.als
[ffg-exp7]: ./ffg-exp7.als
[ffg-exp10]: ./ffg-exp10.als
[ffg-exp11]: ./ffg-exp11.als
[ffg-exp12]: ./ffg-exp11.als