# Alloy specification of 3SF tuned towards AccountableSafety

This directory contains an [Alloy][] specification of the 3SF protocol, which
abstracts the features that are not important for checking `AccountableSafety`.

We have written this specification in an attempt to check `AccountableSafety`
for small but not nonsensical configurations.

## Experimental Setup

TODO

## Experimental Results

| Input      | #blocks | #checkpoints | #signatures | #ffg_votes | #votes | runtime | memory |
|------------|--------:|-------------:|------------:|-----------:|-------:|--------:|-------:|
| [ffg-exp1] |    3    |      5       |      4      |      5     |   12   |  4 sec  |  35MB  |
| [ffg-exp2] |    4    |      5       |      4      |      5     |   12   | 10 sec  |  40MB  |
| [ffg-exp3] |    5    |      5       |      4      |      5     |   12   | 10 sec  |  40MB  |



<!-- References -->

[Alloy]: https://alloytools.org/
[ffg-exp1]: ./ffg-exp1.als
[ffg-exp2]: ./ffg-exp2.als
[ffg-exp3]: ./ffg-exp3.als