----------------------------- MODULE MC_ffg -----------------------------

EXTENDS FiniteSets

\* @type: Int;
MAX_BLOCK_SLOT == 5

\* @type: Seq(Int);
BLOCK_BODIES1 == <<0, 1, 2, 3, 4, 5>>
\* @type: Seq(Int);
BLOCK_BODIES2 == <<0, 11, 12, 13, 14, 15>>
\* @type: Set(Int);
ALL_BLOCK_BODIES == { 0, 1, 2, 3, 4, 5, 11, 12, 13, 14, 15 }

\* @type: Set(Str);
VALIDATORS == {"V1", "V2", "V3", "V4"}

N == 4

VARIABLES
    \* @type: Set($block);
    all_blocks,
    \* @type: Set($block);
    chain1,
    \* @type: Int;
    chain1_tip_slot,
    \* @type: Int;
    chain1_next_idx,
    \* @type: Set($block);
    chain2,
    \* @type: Int;
    chain2_tip_slot,
    \* @type: Int;
    chain2_next_idx,
    \* @type: Bool;
    chain2_forked,
    \* @type: Set($ffgVote);
    ffg_votes,
    \* @type: Set($vote);
    votes,
    \* @type: Set($checkpoint);
    justified_checkpoints

INSTANCE ffg

IndInit ==
    /\ chain1 = Gen(MAX_BLOCK_SLOT + 1)
    /\ \A block \in chain1: IsValidBlock(block)
    /\ chain2 = Gen(MAX_BLOCK_SLOT + 1)
    /\ \A block \in chain2: IsValidBlock(block)
    /\ all_blocks = chain1 \union chain2
    /\ GenesisBlock \in chain1
    /\ GenesisBlock \in chain2
    /\ chain1_tip_slot = 
        LET blockWithLargestSlot == CHOOSE block \in chain1: \A otherBlock \in chain1: block.slot >= otherBlock.slot
        IN blockWithLargestSlot.slot
    /\ chain2_tip_slot = 
        LET blockWithLargestSlot == CHOOSE block \in chain2: \A otherBlock \in chain2: block.slot >= otherBlock.slot
        IN blockWithLargestSlot.slot
    /\ chain1_next_idx = Cardinality(chain1) + 1
    /\ chain2_next_idx = Cardinality(chain2) + 1
    /\ chain2_forked = (chain1 /= chain2)
    /\ ffg_votes = Gen(5) \* must be >= 4 to create two finalized conflicting blocks 
    /\ \A ffgVote \in ffg_votes: IsValidFFGVote(ffgVote)
    /\ votes = Gen(12) \* Must be >= 12 to observe disagreement
    /\ \A vote \in votes:
        /\ vote.ffg_vote \in ffg_votes
        /\ vote.validator \in VALIDATORS
    /\ justified_checkpoints = JustifiedCheckpoints


=============================================================================
