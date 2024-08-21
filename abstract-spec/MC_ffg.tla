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
    
\* `block_graph` forms a tree. Assumes RealClosureInv for brevity (to be used in conjunction)
GraphIsTreeInv ==
    /\ \A <<child, parent>> \in block_graph: \A <<ochild, oparent>> \in block_graph:
        \* 1 parent per child
        child = ochild => parent = oparent
    \* No cycles (RealClosureInv assumed for the formulation below)
    /\ \A block1, block2 \in blocks:
        \/ block1 = block2
        \/ <<block1,block2>> \notin block_graph_closure
        \/ <<block2,block1>> \notin block_graph_closure
    \* Tree, not forest
    /\ \A block \in blocks: <<block, GenesisBlock>> \in block_graph_closure

GraphWellFormedInv == 
    /\ \A block \in blocks: IsValidBlock(block)
    /\ \A <<child, parent>> \in block_graph:  
        /\ child \in blocks
        /\ parent \in blocks
        /\ child.slot > parent.slot

\* `block_graph_closure` is the closure of the relation `block_graph`
RealClosureInv ==
    \* MUST contain
    \* Would be trivially true for block_graph_closure = blocks^2
    /\ \A block \in blocks: <<block, block>> \in block_graph_closure
    /\ block_graph \subseteq block_graph_closure
    /\ \A <<descendant, midpoint1>> \in block_graph_closure: \A <<midpoint2, ancestor>> \in block_graph_closure:
        midpoint1 = midpoint2 => <<descendant, ancestor>> \in block_graph_closure
    \* MAY contain
    \* Would be trivially true for block_graph_closure = {}
    /\ \A <<descendant, ancestor>> \in block_graph_closure:
        \/ descendant = ancestor
        \/ <<descendant, ancestor>> \in block_graph
        \/ \E block \in blocks: 
            /\ <<descendant, block>> \in block_graph
            /\ <<block, ancestor>> \in block_graph_closure 

GraphInv ==
    /\ GraphIsTreeInv
    /\ GraphWellFormedInv
    /\ RealClosureInv

JustifiedCheckpointsInv == 
    /\ \A c \in justified_checkpoints: 
        /\ IsValidCheckpoint(c)
        /\ IsJustified(c, votes, justified_checkpoints)
    /\ LET allCheckpoints == {Checkpoint(block, i): block \in blocks, i \in CheckpointSlots} 
       IN \A c \in (allCheckpoints \ justified_checkpoints): ~IsJustified(c, votes, justified_checkpoints)

VotesWellFormedInv ==
    /\ \A ffgVote \in ffg_votes: IsValidFFGVote(ffgVote)
    /\ \A vote \in votes: 
        /\ vote.ffg_vote \in ffg_votes
        /\ vote.validator \in VALIDATORS

VoteAndCheckpointInv ==
    /\ JustifiedCheckpointsInv
    /\ VotesWellFormedInv

InductiveInv == GraphInv /\ VoteAndCheckpointInv

Init0 ==
    /\ ffg_votes = Gen(5)
    /\ votes = Gen(5)
    /\ justified_checkpoints = Gen(5)
    /\ blocks = Gen(MAX_BLOCK_SLOT)
    /\ block_graph = Gen(MAX_BLOCK_SLOT)
    /\ block_graph_closure = Gen(MAX_BLOCK_SLOT * MAX_BLOCK_SLOT)
    /\ InductiveInv

Next0 == Next

Inv0 == InductiveInv
    
=============================================================================
