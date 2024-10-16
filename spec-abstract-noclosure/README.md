This is an abstraction of `Spec3`. In contrast to `Spec 3`, we explicitly model
two chains, instead of modeling an arbitrary graph of blocks. Thus, this
specification is more tuned towards Accountable Safety, which requires us to
reason about two chains.

The main idea is that chain 1 contains blocks that are simply increasing
positive integers 0, 1, 2, 3, ..., with block 0 being the genesis block. Chain
two starts with a subsequence of blocks on chain 1 and then it may fork at the
index `chain2_fork_block_number`. After the fork, the blocks on chain 2 are
negative numbers such as -4, -5, -6, ...

By using this encoding of two chains, we hope to decrease complexity for the SMT
solver.