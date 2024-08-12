----------------------------- MODULE MC_ffg -----------------------------

\* @type: Int;
MAX_BLOCK_SLOT == 10

\* @type: Set(Str);
BLOCK_BODIES == {"A", "B", "C", "D", "E"}

VARIABLES
    \* @type: Set($block);
    blocks,
    \* @type: Set(<<$block,$block>>);
    block_graph

INSTANCE ffg

=============================================================================