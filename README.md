# 3SF Automated Model-Checking

EF project for model-checking Accountable Safety on the 3SF protocol proposal by D'Amato, Saltini, Tran, and Zanolini.

## TLA+ Specifications

**Spec 1.** [spec/ffg_recursive.tla][]. The result of a manual mechanical translation of the original executable specification in Python, which can be found in [ffg.py].

**Spec 2.** [spec/ffg.tla][]. A manual adaptation of `Spec 1`, using folds instead of recursion and introducing a memorization optimization.

**Spec 3.** [abstract-spec/ffg.tla][]. A manual abstraction of `Spec 2` that is further optimized for constraint solving, especially with Apalache.

## Translation Rules

Our translation rules from executable Python specifications to TLA+ can be found in [Translation.md].

## Experimental Results

Experimental results are reported in [EXPERIMENTS.md].

[spec/ffg]: ./spec/ffg.tla
[spec/MC_ffg]: ./spec/MC_ffg.tla
[abstract-spec/MC_ffg]: ./abstract-spec/MC_ffg.tla
[abstract-spec/ffg]: ./abstract-spec/ffg.tla
[ffg.py]: ./ssf/high_level/common/ffg.py
[spec/ffg_recursive.tla]: ./spec/ffg-recursive.tla
[spec/ffg.tla]: ./spec/ffg.tla
[abstract-spec/ffg.tla]: ./abstract-spec/ffg.tla
[spec/MC_ffg.tla]: ./spec/MC_ffg.tla
[spec/MC_ffg_examples.tla]: ./spec/MC_ffg_examples.tla
[abstract-spec/MC_ffg.tla]: ./abstract-spec/MC_ffg.tla
[Translation.md]: ./Translation.md
[EXPERIMENTS.md]: ./EXPERIMENTS.md
