----------------------------- MODULE ffg -----------------------------
(*
 * Translation of the `ffg.py` Python module to TLA+.
 *
 * Igor Konnov, Jure Kukovec, Thomas Pani, 2024.
 *
 * Subject to Apache 2.0. See `LICENSE.md`.
 *)

EXTENDS Apalache, Integers, Sequences, typedefs

CONSTANT 
    \* @type: Int;
    MAX_BLOCK_SLOT,
    \* @type: Set(BODY);
    BLOCK_BODIES


BlockSlots == 0..MAX_BLOCK_SLOT
CheckpointSlots == 0..(MAX_BLOCK_SLOT+2)

VARIABLES
    \* @type: Set($block);
    blocks,
    \* @type: Set(<<$block, $block>>);
    block_graph,
    \* @type: Set(<<$block, $block>>);
    block_graph_closure,
    \* @type: Set($ffgVote);
    ffg_votes,
    \* @type: Set($checkpoint);
    justified_checkpoints

\* @type: (Int, Str) => $block;
Block(slot, body) ==
    [
        slot |-> slot,
        body |-> body
    ]

NoParent == ""
GenesisBlockBody == "genesis"
GenesisBlock == Block(0, GenesisBlockBody)

\* @type: ($block, Int) => $checkpoint;
Checkpoint(block, checkpoint_slot) == <<block, checkpoint_slot>>    

GenesisCheckpoint == Checkpoint(GenesisBlock, 0)

\* @type: ($checkpoint) => Bool;
IsValidCheckpoint(checkpoint) == 
    LET block == checkpoint[1]
        checkpoint_slot == checkpoint[2]
    IN
        \/ checkpoint = GenesisCheckpoint
        \* Section 3.Checkpoints: "Importantly, the slot c for the checkpoint occurs after the slot B.p where the block was proposed"
        \//\ checkpoint_slot \in CheckpointSlots
          /\ checkpoint_slot > block.slot


\* @type: ($block, $block) => <<$block, $block>>;
Edge(b1, b2) == <<b1,b2>>

\* @type: ($block, Int, Str) => Bool;
ProposeBlock(parent, slot, body) ==
    LET this == Block(slot, body) IN
    /\ slot > parent.slot
    /\ blocks' = blocks \union {this}
    /\ block_graph' = block_graph \union {Edge(this, parent)}
    /\ block_graph_closure' = 
        LET 
            \* @type: Set(<<$block, $block>>);
            inheritedFromParent == 
            { 
                Edge(this, ancestorRelOfParent[2]): ancestorRelOfParent \in { edge \in block_graph_closure: edge[1] = parent } 
            }
        IN block_graph_closure \union inheritedFromParent \union {Edge(this, this)}
    /\ UNCHANGED <<ffg_votes, justified_checkpoints>>


\* @type: ($ffgVote) => Bool;
IsValidFFGVote(vote) ==
    /\ IsValidCheckpoint(vote.source)
    /\ IsValidCheckpoint(vote.target)
    /\ Edge(vote.target[1], vote.source[1]) \in block_graph_closure
    /\ vote.source[2] < vote.target[2]
    

\* @type: ($checkpoint, Set($ffgVote), Set($checkpoint)) => Bool;
IsJustified(checkpoint, ffgVotes, fixpoint) == 
    \/ checkpoint = GenesisCheckpoint
    \/ \E vote \in ffgVotes:
        /\ vote.source \in fixpoint
        /\ vote.target[2] = checkpoint[2]
        /\ <<vote.target[1], checkpoint[1]>> \in block_graph_closure
        /\ <<checkpoint[1], vote.source[1]>> \in block_graph_closure

\* @type: ($checkpoint, Set($ffgVote), Set($checkpoint)) => Bool;
IsFinalized(checkpoint, ffgVotes, justifiedCheckpoints) ==
    /\ checkpoint \in justifiedCheckpoints
    /\ \E vote \in ffgVotes:
        /\ vote.source = checkpoint
        /\ vote.target[2] = checkpoint[2] + 1

AreConflictingBlocks(b1, b2) ==
    /\ Edge(b1,b2) \notin block_graph_closure
    /\ Edge(b2,b1) \notin block_graph_closure


\* @type: ($checkpoint, $checkpoint) => Bool;
CastFFGVote(source, target) ==
    LET ffgVote == [ source |-> source, target |-> target ] IN
    /\ UNCHANGED <<blocks, block_graph, block_graph_closure>>
    /\ IsValidFFGVote(ffgVote)
    /\ ffg_votes' = ffg_votes \union { ffgVote }
    /\ LET allCheckpoints == {Checkpoint(block, i): block \in blocks, i \in CheckpointSlots}
       IN \E allJustifiedCheckpoints \in SUBSET allCheckpoints:
        /\ justified_checkpoints' = allJustifiedCheckpoints
        /\ \A c \in allJustifiedCheckpoints: IsJustified(c, ffg_votes', allJustifiedCheckpoints)
        /\ \A c \in (allCheckpoints \ allJustifiedCheckpoints): ~IsJustified(c, ffg_votes', allJustifiedCheckpoints)

    
Init == 
    /\ blocks = {GenesisBlock}
    /\ block_graph_closure = { Edge(GenesisBlock,GenesisBlock) }
    /\ block_graph = {}
    /\ ffg_votes = {}
    /\ justified_checkpoints = {GenesisCheckpoint}

Next == 
    \/ \E parent \in blocks, slot \in BlockSlots, body \in BLOCK_BODIES: ProposeBlock(parent, slot, body)
    \/ \E <<targetBlock, sourceBlock>> \in block_graph_closure, srcSlot, tgtSlot \in CheckpointSlots: 
        CastFFGVote(
            Checkpoint(sourceBlock, srcSlot), 
            Checkpoint(targetBlock, tgtSlot)
        )

=============================================================================