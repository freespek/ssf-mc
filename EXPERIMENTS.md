# Model checking experiments

**August 2024**

This page summarizes the experiments conducted throughout the project.

## 1. Experimental setup

### Reproducibility

We expect all our experiments to be reproducible in a qualitative sense.
This means that if you run them with the same parameters, you should
obtain the same results; running times may however vary between machines.

The above statement comes with a caveat: When using randomized symbolic
execution (`apalache simulate`), there is still a chance that you might find an
invariant violation later, unless we support the invariant with an inductive
proof in another experiment.

### Environment

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
 using mutually recursive operators, which are [not supported by Apalache][recursive].  As a
 result, we are not checking this specification. This specification is the result
 of our work in [Milestone 1][].

 - **Spec 2**. This is the specification [spec/ffg.tla][]. It is a manual
 adaptation of `Spec 1`. The main difference between `Spec 2` and `Spec 1` is
 that `Spec 2` uses ["folds"][fold] (also known as "reduce") instead of
 recursion. We expect `Spec 2` to be equivalent to `Spec 1`, although we do not
 have a formal proof of this equivalence. This specification has high
 model-checking complexity, roughly speaking, as it contains multiple nested
 folds. In [Milestone 2][], we have introduced an optimization that avoids
 repetitive recursive computations by memorization in the initial states, see
 [PR #38][].  This specification also contains a preliminary construction that
 could help us in proving `AccountableSafety`. Even considering all the
 optimization, the model checker is still consuming a lot of resources (>40G)
 and computing for over 40h. This specification is the result of our work in
 [Milestone 1][] and [Milestone 2][].
 
 - **Spec 3**. This is the specification [abstract-spec/ffg.tla][]. It is a
 manual abstraction of `Spec 2` that is further optimized for constraint solving,
 especially with Apalache. `Spec 3` describes a state machine that adds blocks
 and votes in every step, and thus enables bounded model-checking. `Spec 3`
 contains a preliminary inductive construction in the initial-state predicate.
 This is ongoing work in [Milestone 4][].

 - **Spec 4**. Our experiments in [Milestone 2][] and [Milestone 4][] have shown
 that all specs to this point encode a graph problem of intractable complexity.
 We experimentally support this claim by providing specifications in Alloy and
 SMT, which are both are geared at proving relational properties over (small)
 finite sets and relations.
 `Spec 4` is a manual reformulation of the problem that avoids expensive graph
 constructions and is highly optimized for model checking. We expect that this
 specification allows us to us to prove `AccountableSafety` inductively.
 This is ongoing work in [Milestone 4][].
 
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

| Experiment | Specification            | Property             | Time    |
|-----------:|--------------------------|----------------------|---------|
| 4.1        | `Spec 2` (w/o [PR #38])  | `AccountableSafety`  | out of memory (>20GB)[^1] |
| 4.2.1.     | `Spec 2` (with [PR #38]) | `AccountableSafety`  | timeout (>40h) |
| 4.2.2.     | `Spec 2` (with [PR #38]) | reachable states     | timeout (>40h) |
| 5.1        | `Spec 3`                 | Row 2                | TBD     |
| 5.2        | `Spec 3`                 | Row 3                | TBD     |
| 6.1        | `Spec 4`                 | Row 4                | TBD     |
| 6.2        | `Spec 4`                 | Row 5                | TBD     |

Incomplete results on fixed chains:

| Experiment | Specification            | Graph         | Property              | Time          |
|-----------:|--------------------------|---------------| ----------------------|---------------|
| 4.2.3.1.   | `Spec 2` (with [PR #38]) | `SingleChain` | `Conflicting_Example` | 1 min 3 sec   |
| 4.2.3.1.   | `Spec 2` (with [PR #38]) | `ShortFork`   | `Conflicting_Example` | 52s           |
| 4.2.3.1.   | `Spec 2` (with [PR #38]) | `Forest`      | `Conflicting_Example` | 2 min 21 sec  |

## 4. Model checking Spec 2

We describe model checking experiments with `Spec 2`, that is [spec/ffg.tla][].

### 4.1. Model checking the initial Python translation

`Spec 2` is a manual adaptation of `Spec 1`, that introduces (equivalent) fold
operations instead of recursion (which is not supported by Apalache).

Initial experiments showed that this naive translation quickly[^1] goes out of
memory even with the JVM heap size increased to 20GB (from Apalche's default of
4GB), due to the number of constraints emitted for nested folds (originating
from nested recursion in the Python specification). In our experience, it does
not help to increase the JVM heap size even further, since for that many
constraints, solving time would be prohibitive.

### 4.2. Flattening nested folds

Therefore, we introduced a further manual optimization that flattens nested fold
operations, and allows Apalache to run within 20GB of JVM heap memory.  To
flatten nested folds, we introduce TLA+ state variables that memorize the
fold-based operations `is_ancestor_descendant_relationship` and
`is_justified_checkpoint` (`is_complete_chain` is expressed in terms of ancestry
of genesis).

We evaluated 3 startegies for expressing these precomputed state variables and
continued with the most efficient one. For details on these experiments, see the
[description of PR #38][PR #38].

#### 4.2.1. Bounded model checking of Accountable Safety

In this experiment, we are checking whether Accountable Safety holds true for
the flattened version of `Spec 2`.

```sh
$ cd ./spec
$ JVM_ARGS=-Xmx20G apalache-mc check --length=0 --inv=AccountableSafety MC_ffg.tla
```

> [!NOTE]
> Since `Spec 2` presents a snapshot of a single validator and does not make any
steps, we only have to check properties on the initial states (`--length=0`).
>
> Also, note that we have to extend the default JVM heap size from 4G to 20G (`JVM_ARGS=-Xmx20G`).

Since `Spec 2` has high complexity, this experiment times out after 40 hours.

#### 4.2.2. Bounded model checking to find reachable protocol states

Given the result above, we decided to further evaluate `Spec 2` on a simpler
problem: finding reachable protocol states.

This serves two purposes:
 - to check the correctness of the specification (protocol states that we know to be reachable should be found),
 - to evaluate `Spec 2` on a simpler problem (the underlying SMT query is SAT, not UNSAT).

To this end, we introduce falsy invariants describing reachable protocol states
in [spec/MC_ffg_examples.tla]. Apalache should report these example states as
counterexamples to the supplied property.

For example, to find a protocol state with two conflicting blocks, we can run:

```sh
$ cd ./spec
$ JVM_ARGS=-Xmx20G apalache-mc check --length=0 --inv=Conflicting_Example MC_ffg_examples.tla
```

To find a protocol state with two conflicting finalized blocks, we can run:

```sh
$ cd ./spec
$ JVM_ARGS=-Xmx20G apalache-mc check --length=0 --inv=Finalized_And_Conflicting_Blocks_Example MC_ffg_examples.tla
```

Since `Spec 2` has high complexity, even these experiments time out after 40 hours.

#### 4.2.3. Bounded model checking on fixed graphs

The results above are not surprising – the solver has to consider both
reachability properties for all possible block graphs, and all possible FFG
voting scenarios on top of these graphs.

To further evaluate `Spec 2`, we fixed the block graph – this way the solver
only has to reason about voting. Example fixed block graphs are encoded in
[spec/MC_ffg_examples.tla].

We consider
  - a single, linear chain (`SingleChain`)
  - a short chain with a fork (`ShortFork`)
  - a forest of disconnected chains (`Forest`)

> [!NOTE]
> We supply these alternative states to Apalache via `--init`.

##### 4.2.3.1. Conflicting blocks

To find a protocol state with two conflicting blocks, run:

```sh
$ cd ./spec
$ JVM_ARGS=-Xmx20G apalache-mc check --length=0 --init=Init_ShortFork --inv=Conflicting_Example MC_ffg_examples.tla
```

This experiment took 52 sec.

```sh
$ cd ./spec
$ JVM_ARGS=-Xmx20G apalache-mc check --length=0 --init=Init_Forest --inv=Conflicting_Example MC_ffg_examples.tla
```
This experiment took 2 min 21 sec.

```sh
$ cd ./spec
$ JVM_ARGS=-Xmx20G apalache-mc check --length=0 --init=Init_SingleChain --inv=Conflicting_Example MC_ffg_examples.tla
```

This experiment took 1 min  3 sec.

> [!NOTE]
> There cannot be any conflicting blocks in a single linear chain, so the solver
> (correctly) does not report a counterexample with `Init_SingleChain`.

##### 4.2.3.1. Conflicting blocks

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
find counterexamples, it gives us relatively high confidence that the property
holds true.

This experiment takes about **TODO** on a single node. The interesting thing is
that we can parallelize the enumeration of 100 runs across multiple cores. For
instance, we use 20 CPU cores to check 5 symbolic runs each.

## 6. Induction checking Spec 4

### 6.1. Inductiveness check

In this experiment, we show that `Inv0` is an inductive invariant for `Spec 3`:

```sh
$ cd ./abstract-spec
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
[spec/MC_ffg_examples.tla]: ./spec/MC_ffg_examples.tla
[abstract-spec/MC_ffg.tla]: ./abstract-spec/MC_ffg.tla
[Alloy]: https://en.wikipedia.org/wiki/Alloy_(specification_language)
[Milestone 1]: https://github.com/freespek/ssf-mc/milestone/1?closed=1
[Milestone 2]: https://github.com/freespek/ssf-mc/milestone/2?closed=1
[Milestone 3]: https://github.com/freespek/ssf-mc/milestone/3?closed=1
[Milestone 4]: https://github.com/freespek/ssf-mc/milestone/4?closed=1
[Milestone 5]: https://github.com/freespek/ssf-mc/milestone/5?closed=1
[PR #38]: https://github.com/freespek/ssf-mc/pull/38
[recursive]: https://apalache-mc.org/docs/apalache/principles/recursive.html
[fold]: https://en.wikipedia.org/wiki/Fold_(higher-order_function)

[^1]: Apalache runs out of memory after 49 minutes, but heavy CPU use due to excessive JVM garbage collection already starts after 10 minutes of runtime.
