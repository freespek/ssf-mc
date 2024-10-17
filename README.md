# 3SF Automated Model-Checking

EF project for model-checking Accountable Safety on the 3SF protocol proposal by D'Amato, Saltini, Tran, and Zanolini.

## TLA+ Specifications

**Spec 1.** [spec1-2/ffg_recursive.tla][]. The result of a manual mechanical translation of the original executable specification in Python, which can be found in [ffg.py].

**Spec 2.** [spec1-2/ffg.tla][]. A manual adaptation of `Spec 1`, using folds instead of recursion and introducing a memorization optimization.

**Spec 3.** [spec3/ffg.tla][]. A manual abstraction of `Spec 2` that is further optimized for constraint solving, especially with Apalache.

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
[spec1-2/MC_ffg.tla]: ./spec1-2/MC_ffg.tla
[spec1-2/MC_ffg_examples.tla]: ./spec1-2/MC_ffg_examples.tla
[spec3/MC_ffg.tla]: ./spec3/MC_ffg.tla
[Translation.md]: ./Translation.md
[EXPERIMENTS.md]: ./EXPERIMENTS.md
