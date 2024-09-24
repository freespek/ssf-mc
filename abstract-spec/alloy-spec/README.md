# Alloy specification of 3SF tuned towards AccountableSafety

This directory contains an [Alloy][] specification of the 3SF protocol, which
abstracts the features that are not important for checking `AccountableSafety`.

We have written this specification in an attempt to check `AccountableSafety`
for small but not nonsensical configurations.

## Experimental Setup

TODO

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
| [ffg-exp6] |    5    |      6       |      4      |      6     |   15   | 167 sec |  55 MB  |
| [ffg-exp7] |    6    |      6       |      4      |      6     |   15   | 167 sec |  55 MB  |



<!-- References -->

[Alloy]: https://alloytools.org/
[smt-enc]: ../smt-spec/README.md
[ffg-exp1]: ./ffg-exp1.als
[ffg-exp2]: ./ffg-exp2.als
[ffg-exp3]: ./ffg-exp3.als
[ffg-exp4]: ./ffg-exp4.als
[ffg-exp5]: ./ffg-exp5.als
[ffg-exp6]: ./ffg-exp6.als
[ffg-exp7]: ./ffg-exp7.als