------------------------- MODULE MC_ffg_b3_ffg5_v12 ----------------------------

EXTENDS FiniteSets

\* We set it to 3 to generate the smallest counterexample that contains two
\* conflicting finalized blocks without equivocation.
\* @type: Int;
MAX_BLOCK_SLOT == 3
\* @type: Int;
MAX_BLOCK_BODY == 3

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

IndInit_C1 ==
    (*
           / [+1] - [+2]
        [0]
           \ [-1] - [-2]
     *)
    \E i1_1, i1_2, i2_1, i2_2 \in 0..MAX_BLOCK_SLOT:
      LET b1_1 == [ body |-> 1, slot |-> i1_1 ]
          b1_2 == [ body |-> 2, slot |-> i1_2 ]
          b2_1 == [ body |-> -1, slot |-> i2_1 ]
          b2_2 == [ body |-> -2, slot |-> i2_2 ]
      IN
      /\ all_blocks = { GenesisBlock, b1_1, b1_2, b2_1, b2_2 }
      /\ chain1 = { GenesisBlock, b1_1, b1_2 }
      /\ chain1_tip = b1_2
      /\ chain2 = { GenesisBlock, b2_1, b2_2 }
      /\ chain2_tip = b2_2
      /\ chain2_fork_block_number = -1
      \* the rest has to be generated
      /\ ffg_votes = Gen(5) \* must be >= 4 to observe disagreement
      /\ votes = Gen(12)    \* must be >= 12 to observe disagreement
      /\ justified_checkpoints = Gen(5)
      /\ InitAccountableSafety
      /\ VotesInv
      /\ CheckpointsInv

IndInit_C2 ==
    (*
           / [+1]
        [0]
           \ [-1] - [-2]
     *)
    \E i1_1, i2_1, i2_2 \in 0..MAX_BLOCK_SLOT:
      LET b1_1 == [ body |-> 1, slot |-> i1_1 ]
          b2_1 == [ body |-> -1, slot |-> i2_1 ]
          b2_2 == [ body |-> -2, slot |-> i2_2 ]
      IN
      /\ all_blocks = { GenesisBlock, b1_1, b2_1, b2_2 }
      /\ chain1 = { GenesisBlock, b1_1 }
      /\ chain1_tip = b1_1
      /\ chain2 = { GenesisBlock, b2_1, b2_2 }
      /\ chain2_tip = b2_2
      /\ chain2_fork_block_number = -1
      \* the rest has to be generated
      /\ ffg_votes = Gen(5) \* must be >= 4 to observe disagreement
      /\ votes = Gen(12)    \* must be >= 12 to observe disagreement
      /\ justified_checkpoints = Gen(5)
      /\ InitAccountableSafety
      /\ VotesInv
      /\ CheckpointsInv

IndInit_C3 ==
    (*
                  / [+2]
        [0] - [+1] 
                  \ [-2]
     *)
    \E i1, i1_2, i2_2 \in 0..MAX_BLOCK_SLOT:
      LET b1 == [ body |-> 1, slot |-> i1 ]
          b1_2 == [ body |-> 2, slot |-> i1_2 ]
          b2_2 == [ body |-> -2, slot |-> i2_2 ]
      IN
      /\ all_blocks = { GenesisBlock, b1, b1, b1_2, b2_2 }
      /\ chain1 = { GenesisBlock, b1, b1_2 }
      /\ chain1_tip = b1_2
      /\ chain2 = { GenesisBlock, b1, b2_2 }
      /\ chain2_tip = b2_2
      /\ chain2_fork_block_number = -2
      \* the rest has to be generated
      /\ ffg_votes = Gen(5) \* must be >= 4 to observe disagreement
      /\ votes = Gen(12)    \* must be >= 12 to observe disagreement
      /\ justified_checkpoints = Gen(5)
      /\ InitAccountableSafety
      /\ VotesInv
      /\ CheckpointsInv

IndInit_C4 ==
    (*
           / [+1] - [+2]
        [0]
           \ [-1]
     *)
    \E i1_1, i2_1, i1_2 \in 0..MAX_BLOCK_SLOT:
      LET b1_1 == [ body |-> 1, slot |-> i1_1 ]
          b1_2 == [ body |-> 2, slot |-> i1_2 ]
          b2_1 == [ body |-> -1, slot |-> i2_1 ]
      IN
      /\ all_blocks = { GenesisBlock, b1_1, b1_2, b2_1 }
      /\ chain1 = { GenesisBlock, b1_1, b_1_2 }
      /\ chain1_tip = b1_2
      /\ chain2 = { GenesisBlock, b2_1 }
      /\ chain2_tip = b2_1
      /\ chain2_fork_block_number = -1
      \* the rest has to be generated
      /\ ffg_votes = Gen(5) \* must be >= 4 to observe disagreement
      /\ votes = Gen(12)    \* must be >= 12 to observe disagreement
      /\ justified_checkpoints = Gen(5)
      /\ InitAccountableSafety
      /\ VotesInv
      /\ CheckpointsInv

=============================================================================
