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
    \* @type: Set(<<$block,$block>>);
    block_graph,
    \* @type: Set(<<$block, $block>>);
    block_graph_closure,
    \* @type: Set($ffgVote);
    ffg_votes,
    \* @type: Set($vote);
    votes,
    \* @type: Set($checkpoint);
    justified_checkpoints

INSTANCE ffg

ExistsJustifiedNonGenesisInv == Cardinality(justified_checkpoints) <= 1

ExistTwoFinalizedConflictingBlocks == 
    LET disagreement == \E c1, c2 \in justified_checkpoints: 
        /\ IsFinalized(c1, votes, justified_checkpoints)
        /\ IsFinalized(c2, votes, justified_checkpoints)
        /\ AreConflictingBlocks(c1[1], c2[1])
    IN ~disagreement

AccountableSafety ==
    LET disagreement == \E c1, c2 \in justified_checkpoints: 
            /\ IsFinalized(c1, votes, justified_checkpoints)
            /\ IsFinalized(c2, votes, justified_checkpoints)
            /\ AreConflictingBlocks(c1[1], c2[1])
    IN ~disagreement \/ Cardinality(SlashableNodes) * 3 >= N

Inv == ExistTwoFinalizedConflictingBlocks

=============================================================================
