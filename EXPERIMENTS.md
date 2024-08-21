# Model checking experiments

**August 2024**

This page summarizes the experiments conducted in the project. While running times may vary between machines, we expect these experiments to be reproducible. More precisely, this means that if you run the experiments with the same parameters, you should obtain the same results.

The above statement about reproducibility comes with a caveat: When using
randomized symbolic execution, there is still a chance that you might find an
invariant violation later, unless we support the invariant with an inductive
proof in another experiment.

If you have any questions about our experimental setup and the experiments, feel
free to ask [Igor Konnov][].

## 1. Experimental setup

**Hardware**. We conducted the experiments on a dedicated AMD Ryzen 9 5950X
16-Core Processor with 128GB of RAM. This powerful machine allowed us to run
multiple experiments in parallel. Apalache is powered by the SMT solver [Z3][],
which is known to have significant variations in running times. Therefore,
instead of taking the time figures on this page literally, consider them as
estimates such as "minutes", "hours", or "days".

**Software**. We are using the symbolic model checker [Apalache][] for
TLA<sup>+</sup>. Check the Apalache [installation instructions][Apalache
installation] in the manual. For reproducibility, we recommend using the latest
release in the 0.45.x series. See [Apalache releases][]. The experiments were
run on Ubuntu Server 24.04.

In this document, we provide commands for running each experiment in a single
thread. We also have an experimental setup that runs individual experiments on
multiple CPU cores. If you are curious about this setup, please contact us.

## 2. Input specifications

<!-- TODO: this section should go into a separate high-level document in the
future -->

We have produced the following specifications in the project:
 
 - **Spec 1**. This is the specification [spec/ffg_recursive.tla][]. It is the
 result of a manual mechanical translation of the original executable
 specification in Python, which can be found in [ffg.py]. This specification is
 using mutually recursive operators, which are not supported by Apalache.  As a
 result, we are not checking this specification.

 - **Spec 2**. This is the specification [spec/ffg.tla][]. It is a manual
 adaptation of `Spec 1`. The main difference between `Spec 2` and `Spec 1` is
 that `Spec 2` uses "folds" (also known as "reduce") instead of recursion. We
 expect `Spec 2` to be equivalent to `Spec 1`, although we do not have a formal
 proof of this equivalence. This specification has high model-checking
 complexity, roughly speaking, as it contains multiple nested folds.
 
 - **Spec 3**. This is the specification [abstract-spec/ffg.tla][]. It is a
 manual abstraction of `Spec 2` that is highly optimized for constraint solving,
 especially with Apalache. In addition to that, Spec 3 describes a state machine
 that adds blocks and votes in every step.

 - **Spec 4**. This is an inductive invariant constructed for `Spec 3`. **TBD**
 
The specifications `Spec 2` and `Spec 3` come with model checking instances
[spec/MC_ffg.tla] and [abstract-spec/MC_ffg.tla], respectively. These instances
fix the specification parameters to small values for model checking purposes,
e.g.:

 - four validators,
 - from 4 to 10 slots,
 - up to 12 votes.

By using small values for the parameters, we are able to produce counterexamples
in a reasonable time when such examples exist. By increasing the parameter
values, we can increase our confidence in the specification and its properties.
While this restriction to small parameter values is dictated by the practicality
of our approach, it is informally supported by the "small scope hypothesis,"
which was popularized by tools such as [Alloy][].

## 3. All figures in one place

The following table summarizes the experimental figures in one place:

| Experiment | Specification | Property   | Time    | Memory |
|-----------:|---------------|------------|---------|--------|
| 4.1        | `Spec 2`      | Row 1      | TBD     | TBD    |
| 5.1        | `Spec 3`      | Row 2      | TBD     | TBD    |
| 5.2        | `Spec 3`      | Row 3      | TBD     | TBD    |
| 6.1        | `Spec 4`      | Row 4      | TBD     | TBD    |
| 6.2        | `Spec 4`      | Row 5      | TBD     | TBD    |

## 4. Model checking Spec 2

<!-- TODO: Thomas, please add a description of the experiments with MC_ffg_examples.tla -->

### 4.1. Bounded model checking of Accountable Safety

In this experiment, we are checking whether Accountable Safety holds true for
`Spec 2`. Since `Spec 2` presents a snapshot of a single validator and does not
make any steps, we have to check this property only in the initial states.

```sh
$ cd ./spec
$ JVM_ARGS=-Xmx20G apalache-mc check --length=0 \
  --inv=AccountableSafety MC_ffg.tla
```

Note that we have to extend the default JVM heap size from 4G to 20G.

Since `Spec 2` has high complexity, this experiment takes long. **TODO:** how
long.

## 5. Model checking Spec 3

### 5.1. Bounded model checking of Accountable Safety

In this experiment, we are checking whether Accountable Safety holds true for up
to 10 steps of `Spec 3`. Since `Spec 3` specifies the abstract state machine of
a single validator (alternatively, the network view), we have to check
executions up to some bound.

```sh
$ cd ./abstract-spec
$ JVM_ARGS=-Xmx20G apalache-mc check --inv=AccountableSafety MC_ffg.tla
```

This experiment takes about **TODO**.

### 5.2. Randomized symbolic execution for accountable safety

To obtain results faster, albeit at the cost of completeness, we analyze 100
random symbolic runs, each consisting of up to 10 steps:

```sh
$ cd ./abstract-spec
$ JVM_ARGS=-Xmx20G apalache-mc simulate \
  simulate --max-run=100 --length=10 --timeout-smt=10800 \
  --inv=AccountableSafety MC_ffg.tla
```

In addition, we bound the running time of individual SMT queries to 3 hours. If
the timeout is reached, the query is skipped. This command typically finds
counterexamples much quicker than `check`. Therefore, when `simulate` does not
find counterexamples, it gives us relatively good confidence that the property
holds true.

This experiment takes about **TODO** on a single node. The interesting thing is
that we can parallelize the enumeration of 100 runs across multiple cores. For
instance, we try 5 symbolic runs on 20 CPU cores.

## 6. Induction checking Spec 4

### 6.1. Inductiveness check

In this experiment, we show that `Inv0` is an inductive invariant for `Spec 3`:

```sh
$ apalache-mc check --length=1 --inv=Inv0 \
  --init=Init0 --next=Next0 MC_ffg.tla
```

This experiment takes about **TODO**.

### 6.2. Inductive checking of Accountable Safety

```sh
$ cd ./abstract-spec
$ JVM_ARGS=-Xmx20G ~/devl/apalache/bin/apalache-mc check \
  --length=0 --init=Init0 --inv=AccountableSafety \
  MC_ffg.tla
```

This experiment took 19 hours 48 min 29 sec.


[Apalache]: https://apalache-mc.org/
[Apalache installation]: https://apalache-mc.org/docs/apalache/installation/index.html
[Apalache releases]: https://github.com/apalache-mc/apalache/releases
[Igor Konnov]: https://www.konnov.phd
[Z3]: https://github.com/Z3Prover/z3
[spec/ffg]: ./spec/ffg.tla
[spec/MC_ffg]: ./spec/MC_ffg.tla
[abstract-spec/MC_ffg]: ./abstract-spec/MC_ffg.tla
[abstract-spec/ffg]: ./abstract-spec/ffg.tla
[ffg.py]: https://github.com/saltiniroberto/ssf/blob/ad3ba2c21bc1cd554a870a6e0e4d87040558e129/high_level/common/ffg.py
[spec/ffg_recursive.tla]: ./spec/ffg-recursive.tla
[spec/ffg.tla]: ./spec/ffg.tla
[abstract-spec/ffg.tla]: ./abstract-spec/ffg.tla
[spec/MC_ffg.tla]: ./spec/MC_ffg.tla
[abstract-spec/MC_ffg.tla]: ./abstract-spec/MC_ffg.tla
[Alloy]: https://en.wikipedia.org/wiki/Alloy_(specification_language)