# 3SF Automated Model-Checking

EF project for model-checking Accountable Safety on the [3SF protocol]()
proposal by D'Amato, Saltini, Tran, and Zanolini.

## TLA+ Specifications

**Spec 1.**: This is the specification
[spec1-2/ffg_recursive.tla](./spec1-2/ffg_recursive.tla). It is the result of a
manual mechanical translation of the original executable specification in
Python, which can be found in [ffg.py](./spec1-2/ffg.tla). This specification is
using mutually recursive operators, which are not supported by Apalache. As a
result, we are not checking this specification.

**Spec 2.** This is the specification [spec1-2/ffg](./spec1-2/ffg.tla). It is a
manual adaptation of Spec 1. The main difference between Spec 2 and Spec 1 is
that Spec 2 uses "folds" (also known as "reduce") instead of recursion.  Check
the model checking instance in [spec1-2/MC_ffg](./spec1-2/MC_ffg.tla).

**Spec 3.** This is the further abstraction of Spec 2 that uses the concept of
a state machine, instead of a purely sequential specification (such as the
Python code). Check [spec3/ffg](./spec3/ffg.tla) and the model checking instance
in [spec3/MC_ffg](./spec3/MC_ffg.tla).

**Spec 3b.** This is a specification in SMT using the theory of
finite sets and cardinalities. In combination with the solver CVC5, this
specification allows us to push verification of accountable safety even further.
Check [the description](./spec3b-smt/README.md).

**Spec 3c.** This is a specification in
Alloy. With this specification, we manage to check all small configurations that
cover the base case and one inductive step of the definitions.
Check [the description](./spec3c-alloy/README.md).

**Spec 4.** This is an extension of Spec 3 that contains an inductive invariant
in [spec4/ffg_inductive.tla](./spec4/ffg_inductive.tla). See the model checking
instances in [MC_ffg_b3_ffg5_v12](./spec4/MC_ffg_b3_ffg5_v12.tla) and
[MC_ffg_b3_ffg5_v12](./spec4/MC_ffg_b3_ffg5_v12.tla).

**Spec 4b.** This spec
contains further abstractions and decomposition of configurations. This is the
first TLA<sup>+</spec> specification that allowed us to show accountable safety
for models of very small size. Check [ffg](./spec4b-optimizations/ffg.tla),
[MC_ffg_b3_ffg5_v12](./spec4b-optimizations/MC_ffg_b3_ffg5_v12.tla), and
[MC_ffg_b5_ffg10_v20](./spec4b-optimizations/MC_ffg_b5_ffg10_v20.tla).

## Translation Rules

Our translation rules from executable Python specifications to TLA+ can be found in [Translation.md].

## Experimental Results

Experimental results are reported in [EXPERIMENTS.md].

[spec1-2/ffg]: ./spec1-2/ffg.tla
[spec1-2/MC_ffg]: ./spec1-2/MC_ffg.tla
[spec3/MC_ffg]: ./spec3/MC_ffg.tla
[spec3/ffg]: ./spec3/ffg.tla
[ffg.py]: ./ssf/high_level/common/ffg.py
[spec1-2/ffg_recursive.tla]: ./spec1-2/ffg-recursive.tla
[spec1-2/ffg.tla]: ./spec1-2/ffg.tla
[spec3/ffg.tla]: ./spec3/ffg.tla
[spec4/ffg_inductive.tla]: ./spec3/ffg.tla
[spec1-2/MC_ffg.tla]: ./spec1-2/MC_ffg.tla
[spec1-2/MC_ffg_examples.tla]: ./spec1-2/MC_ffg_examples.tla
[spec3/MC_ffg.tla]: ./spec3/MC_ffg.tla
[Translation.md]: ./Translation.md
[EXPERIMENTS.md]: ./EXPERIMENTS.md
[3SF protocol]: https://arxiv.org/abs/2411.00558