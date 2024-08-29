----------------------------- MODULE MC_ffg -----------------------------

EXTENDS FiniteSets

\* @type: Int;
MAX_BLOCK_SLOT == 5

\* @type: Seq(Int);
BLOCK_BODIES1 == <<0, 1, 2, 3, 4, 5>>
\* @type: Set(Int);
BLOCK_BODIES1_SET == {0, 1, 2, 3, 4, 5}
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
    \* We avoid creating chain1 and chain2 with Gen. See Apalache issue #2973.
    /\ chain1 \in SUBSET [slot: BlockSlots, body: BLOCK_BODIES1_SET]
    /\ chain2 \in SUBSET [slot: BlockSlots, body: ALL_BLOCK_BODIES]
    /\ all_blocks = chain1 \union chain2
    \* There are no two blocks on chain1 and chain2 with the same slot
    /\ \A b1, b2 \in chain1: b1 /= b2 => b1.slot /= b2.slot
    /\ \A b1, b2 \in chain2: b1 /= b2 => b1.slot /= b2.slot
    \* The only blocks chain1 and chain2 have in common are the ones up to the highest common prefix slot
    /\ \E highestCommonPrefixSlot \in BlockSlots: \A block \in all_blocks:
        IF block.slot <= highestCommonPrefixSlot THEN block \in chain1 \intersect chain2
        ELSE block \notin chain1 \/ block \notin chain2
    /\ GenesisBlock \in chain1
    /\ GenesisBlock \in chain2
    /\ \E blockWithLargestSlot \in chain1: 
        /\ chain1_tip_slot = blockWithLargestSlot.slot
        /\ \A otherBlock \in chain1: blockWithLargestSlot.slot >= otherBlock.slot
    /\ \E blockWithLargestSlot \in chain2: 
        /\ chain2_tip_slot = blockWithLargestSlot.slot
        /\ \A otherBlock \in chain2: blockWithLargestSlot.slot >= otherBlock.slot
    /\ chain1_next_idx = Cardinality(chain1) + 1
    /\ chain2_next_idx = Cardinality(chain2) + 1
    /\ chain2_forked = (chain1 /= chain2)
    /\ ffg_votes = Gen(5) \* must be >= 4 to create two finalized conflicting blocks 
    /\ \A ffgVote \in ffg_votes: IsValidFFGVote(ffgVote)
    /\ votes = Gen(12) \* Must be >= 12 to observe disagreement
    /\ \A vote \in votes:
        /\ vote.ffg_vote \in ffg_votes
        /\ vote.validator \in VALIDATORS
    /\ justified_checkpoints = JustifiedCheckpoints(votes)

=============================================================================
