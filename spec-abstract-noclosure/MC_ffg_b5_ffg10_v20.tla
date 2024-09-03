----------------------- MODULE MC_ffg_b5_ffg10_v20 -----------------------------

EXTENDS FiniteSets

\* @type: Int;
MAX_BLOCK_SLOT == 5
\* @type: Int;
MAX_BLOCK_BODY == 3

\* @type: Set(Str);
VALIDATORS == {"V1", "V2", "V3", "V4"}

N == 4

VARIABLES
    \* the set of all_blocks
    \* @type: Set($block);
    all_blocks,
    \* the set of blocks on chain 1
    \* @type: Set($block);
    chain1,
    \* the latest block on chain 1
    \* @type: $block;
    chain1_tip,
    \* the set of blocks on chain 2
    \* @type: Set($block);
    chain2,
    \* the latest block on chain 2
    \* @type: $block;
    chain2_tip,
    \* If chain2_fork_block_number is not equal to 0,
    \* then chain2 is a fork of chain1 starting at chain2_fork_block_number
    \* @type: Int;
    chain2_fork_block_number,
    \* @type: Set($ffgVote);
    ffg_votes,
    \* @type: Set($vote);
    votes,
    \* The set of the checkpoints that were announced so far.
    \* @type: Set($checkpoint);
    checkpoints,
    \* @type: Set($checkpoint);
    justified_checkpoints


INSTANCE ffg_inductive

IndInit ==
    \* We choose two different bounds for creating chain1 and chain2 with Gen.
    \* See Apalache issue #2973.
    /\ all_blocks = Gen(10)
    /\ chain1 = Gen(5)
    /\ chain1_tip \in chain1
    /\ chain2 = Gen(6)
    /\ chain2_tip \in chain2
    /\ ffg_votes = Gen(10) \* must be >= 4 to observe disagreement
    /\ votes = Gen(20)    \* must be >= 12 to observe disagreement
    /\ \E fork_number \in Int:
        /\ fork_number \in -MAX_BLOCK_BODY..0
        /\ chain2_fork_block_number = fork_number
    /\ checkpoints = Gen(10)
    /\ justified_checkpoints = Gen(10)
    /\ IndInv

=============================================================================
