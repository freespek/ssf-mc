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

\* We avoid creating chain1 and chain2 with Gen. See Apalache issue #2973.
IndInit ==
    /\ \E chain1Len \in DOMAIN BLOCK_BODIES1: \* if we know how long chain1 is, we know the exact sequence of block bodies
        /\ chain1 \in SUBSET [slot: BlockSlots, body: BLOCK_BODIES1_SET]
        \* Below, B gives us at least one block per body, A additionally constrains it to _exactly_ one block per body:
        /\ Cardinality(chain1) = chain1Len \* A
        /\ \A i \in DOMAIN BLOCK_BODIES1: (i <= chain1Len) => \E block \in chain1: block.body = BLOCK_BODIES1[i] \* B
        \* well-ordered blocks
        /\ \A b1,b2 \in chain1: b1.body < b2.body => b1.slot < b2.slot
    /\ \E chain2Len, prefixLen \in DOMAIN BLOCK_BODIES1: \* if we know how long chain2 is, we know the _relative_ sequence of block bodies
        /\ prefixLen <= chain2Len
        /\ chain2 \in SUBSET [slot: BlockSlots, body: ALL_BLOCK_BODIES]
        /\ Cardinality(chain1) = chain2Len
        /\ \A i \in DOMAIN BLOCK_BODIES1: 
            \* shared prefix with chain1
            /\ (i <= prefixLen) => \E block \in (chain2 \intersect chain1): block.body = BLOCK_BODIES1[i]
            /\ (prefixLen < i /\ i <= chain2Len) => \E block \in (chain2 \ chain1): block.body = BLOCK_BODIES2[i]
        /\ \A b1,b2 \in chain2: b1.body < b2.body => b1.slot < b2.slot
    /\ all_blocks = chain1 \union chain2
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
    /\ justified_checkpoints = JustifiedCheckpoints


=============================================================================
