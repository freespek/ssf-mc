----------------------------- MODULE MC_ffg -----------------------------

EXTENDS FiniteSets

\* @type: Int;
MAX_BLOCK_SLOT == 5

\* @type: Set(Str);
BLOCK_BODIES == {"A", "B", "C", "D", "E"}

\* @type: Set(Str);
VALIDATORS == {"V1", "V2", "V3", "V4"}

N == 4

VARIABLES
    \* @type: Set($block);
    blocks,
    \* @type: Int -> $block;
    chain1,
    \* @type: Int;
    chain1_tip_index,
    \* @type: Int -> $block;
    chain2,
    \* @type: Int;
    chain2_tip_index,
    \* @type: Bool;
    forked,
    \* @type: $block -> Set($block);
    ancestors,
    \* @type: Set($ffgVote);
    ffg_votes,
    \* @type: Set($vote);
    votes,
    \* @type: Set($checkpoint);
    justified_checkpoints

INSTANCE ffg

=============================================================================
