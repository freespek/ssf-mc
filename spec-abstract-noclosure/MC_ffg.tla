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

=============================================================================
