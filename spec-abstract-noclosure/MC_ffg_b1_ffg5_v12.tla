------------------------- MODULE MC_ffg_b1_ffg5_v12 ----------------------------

EXTENDS FiniteSets

\* We set it to 3 to generate the smallest counterexample that contains two
\* conflicting finalized blocks without equivocation.
\* @type: Int;
MAX_BLOCK_SLOT == 3
\* @type: Int;
MAX_BLOCK_BODY == 1

\* @type: Set(Str);
VALIDATORS == {"V1", "V2", "V3", "V4"}

N == 4
T == 1

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
    \* @type: Set($checkpoint);
    justified_checkpoints


INSTANCE ffg_inductive

IndInit ==
    \* We choose two different bounds for creating chain1 and chain2 with Gen.
    \* See Apalache issue #2973.
    /\ all_blocks = Gen(6)
    /\ chain1 = Gen(2)
    /\ chain1_tip \in chain1
    /\ chain2 = Gen(3)
    /\ chain2_tip \in chain2
    /\ ffg_votes = Gen(5) \* must be >= 4 to observe disagreement
    /\ votes = Gen(12)    \* must be >= 12 to observe disagreement
    /\ \E fork_number \in Int:
        /\ fork_number \in -MAX_BLOCK_BODY..0
        /\ chain2_fork_block_number = fork_number
    /\ justified_checkpoints = Gen(5)
    /\ InitAccountableSafety
    /\ IndInv

IndInit_C1 ==
    \E i, j \in 0..MAX_BLOCK_SLOT:
      LET b1 == [ body |-> 1, slot |-> i ]
          b2 == [ body |-> -1, slot |-> j ]
      IN
      /\ all_blocks = { GenesisBlock, b1, b2 }
      /\ chain1 = { GenesisBlock, b1 }
      /\ chain1_tip = b1
      /\ chain2 = { GenesisBlock, b2 }
      /\ chain2_tip = b2
      /\ chain2_fork_block_number = -1
      \* the rest has to be generated
      /\ ffg_votes = Gen(5) \* must be >= 4 to observe disagreement
      /\ votes = Gen(12)    \* must be >= 12 to observe disagreement
      /\ justified_checkpoints = Gen(5)
      /\ InitAccountableSafety
      /\ VotesInv
      /\ CheckpointsInv

=============================================================================
