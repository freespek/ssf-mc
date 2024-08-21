----------------------------- MODULE ffg -----------------------------
(*
 * Translation of the `ffg.py` Python module to TLA+.
 *
 * Igor Konnov, Jure Kukovec, Thomas Pani, 2024.
 *
 * Subject to Apache 2.0. See `LICENSE.md`.
 *)

EXTENDS Apalache, Integers, FiniteSets, Sequences, typedefs

CONSTANT 
    \* @type: Int;
    MAX_BLOCK_SLOT,
    \* @type: Set(Str);
    BLOCK_BODIES,
    \* @type: Set(Str);
    VALIDATORS,
    \* N = Cardinality(VALIDATORS)
    \* @type: Int;
    N

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
    \* @type: Set($vote);
    votes,
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

\* @type: ($block) => Bool;
IsValidBlock(block) ==
    /\ block.body \in (BLOCK_BODIES \union {GenesisBlockBody})
    /\ block.slot \in BlockSlots

\* @type: ($checkpoint) => Bool;
IsValidCheckpoint(checkpoint) == 
    LET block == checkpoint[1]
        checkpoint_slot == checkpoint[2]
    IN
        /\ IsValidBlock(block)
        /\\/ checkpoint = GenesisCheckpoint
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
    \* no block can have two parents
    /\ \A <<ochild, oparent>> \in block_graph:
        ochild /= this
    /\ block_graph' = block_graph \union {Edge(this, parent)}
    /\ block_graph_closure' = 
        LET 
            \* @type: Set(<<$block, $block>>);
            inheritedFromParent == 
            { 
                Edge(this, ancestorRelOfParent[2]): ancestorRelOfParent \in { edge \in block_graph_closure: edge[1] = parent } 
            }
        IN block_graph_closure \union inheritedFromParent \union {Edge(this, this)}
    /\ UNCHANGED <<ffg_votes, votes, justified_checkpoints>>

\* Like ProposeBlock, but adds any number of children to one parent
\* @type: ($block, Set(<<Int, Str>>)) => Bool;
ProposeBlocks(parent, slotsAndBodies) ==
    LET newBlocks == { Block(slot, body): <<slot,body>> \in slotsAndBodies } IN
    /\ \A newBlock \in newBlocks:
        /\ newBlock.slot > parent.slot
        \* no block can have two parents
        /\ \A <<ochild, oparent>> \in block_graph: ochild /= newBlock
    /\ blocks' = blocks \union newBlocks
    /\ block_graph' = block_graph \union {Edge(newBlock, parent): newBlock \in newBlocks }
    /\ block_graph_closure' = 
        LET 
            \* @type: Set(<<$block, $block>>);
            inheritedFromParent == 
            UNION { 
                { 
                    Edge(newBlock, ancestorRelOfParent[2]): ancestorRelOfParent \in { edge \in block_graph_closure: edge[1] = parent } 
                }: newBlock \in newBlocks
            }
        IN block_graph_closure \union inheritedFromParent \union {Edge(newBlock, newBlock): newBlock \in newBlocks}
    /\ UNCHANGED <<ffg_votes, votes, justified_checkpoints>>


\* @type: ($ffgVote) => Bool;
IsValidFFGVote(vote) ==
    /\ IsValidCheckpoint(vote.source)
    /\ IsValidCheckpoint(vote.target)
    /\ Edge(vote.target[1], vote.source[1]) \in block_graph_closure
    /\ vote.source[2] < vote.target[2]
    

\* @type: ($checkpoint, Set($vote), Set($checkpoint)) => Bool;
IsJustified(checkpoint, viewVotes, fixpoint) == 
    \/ checkpoint = GenesisCheckpoint
    \/ LET validatorsWhoCastJustifyingVote == { 
        v \in VALIDATORS: \E justifyingVote \in viewVotes:
            /\ justifyingVote.validator = v
            /\ LET ffgVote == justifyingVote.ffg_vote IN
                \* L6:
                /\ ffgVote.source \in fixpoint
                \* L7:
                /\ <<ffgVote.target[1], checkpoint[1]>> \in block_graph_closure
                /\ <<checkpoint[1], ffgVote.source[1]>> \in block_graph_closure
                \* L8:
                /\ ffgVote.target[2] = checkpoint[2] }    
        IN 3 * Cardinality(validatorsWhoCastJustifyingVote) >= 2 * N

\* @type: ($checkpoint, Set($vote), Set($checkpoint)) => Bool;
IsFinalized(checkpoint, viewVotes, justifiedCheckpoints) ==
    /\ checkpoint \in justifiedCheckpoints
    /\ LET validatorsWhoCastFinalizingVote == { 
        v \in VALIDATORS: \E finalizingVote \in viewVotes:
            /\ finalizingVote.validator = v
            /\ LET ffgVote == finalizingVote.ffg_vote IN
                \* L14:
                /\ ffgVote.source = checkpoint
                \* L15:
                /\ ffgVote.target[2] = checkpoint[2] + 1 }
        IN 3 * Cardinality(validatorsWhoCastFinalizingVote) >= 2 * N

AreConflictingBlocks(b1, b2) ==
    /\ Edge(b1,b2) \notin block_graph_closure
    /\ Edge(b2,b1) \notin block_graph_closure


Vote(validator, ffgVote) == [
    validator |-> validator,
    ffg_vote |-> ffgVote
]

\* @type: ($checkpoint, $checkpoint, Set(Str)) => Bool;
CastVotes(source, target, validators) ==
    LET ffgVote == [ source |-> source, target |-> target ] IN
    /\ UNCHANGED <<blocks, block_graph, block_graph_closure>>
    /\ IsValidFFGVote(ffgVote)
    /\ validators /= {}
    /\ ffg_votes' = ffg_votes \union { ffgVote }
    /\ votes' = votes \union { Vote(v, ffgVote): v \in validators }
    /\ LET allCheckpoints == {Checkpoint(block, i): block \in blocks, i \in CheckpointSlots}
       IN \E allJustifiedCheckpoints \in SUBSET allCheckpoints:
        /\ justified_checkpoints' = allJustifiedCheckpoints
        /\ \A c \in allJustifiedCheckpoints: IsJustified(c, votes', allJustifiedCheckpoints)
        /\ \A c \in (allCheckpoints \ allJustifiedCheckpoints): ~IsJustified(c, votes', allJustifiedCheckpoints)

SlashableNodes ==
    LET slashable_votes == { vote1 \in votes: \E vote2 \in votes:
        \* equivocation
        \/ /\ vote1.validator = vote2.validator
           /\ vote1 /= vote2
           /\ vote1.ffg_vote.target[2] = vote2.ffg_vote.target[2]
        \* surround voting
        \/ /\ vote1.validator = vote2.validator
           /\ \/ vote1.ffg_vote.source[2] < vote2.ffg_vote.source[2]
              \/ /\ vote1.ffg_vote.source[2] = vote2.ffg_vote.source[2]
                 /\ vote1.ffg_vote.source[1].slot < vote2.ffg_vote.source[1].slot
           /\ vote2.ffg_vote.target[2] < vote1.ffg_vote.target[2]
    } IN { v.validator: v \in slashable_votes }
    
Init == 
    /\ blocks = {GenesisBlock}
    /\ block_graph_closure = { Edge(GenesisBlock,GenesisBlock) }
    /\ block_graph = {}
    /\ ffg_votes = {}
    /\ votes = {}
    /\ justified_checkpoints = {GenesisCheckpoint}

Next == 
    \/ \E parent \in blocks, slot \in BlockSlots, body \in BLOCK_BODIES: ProposeBlock(parent, slot, body)
    \* ConstSimplifier throws StackOverflowError
    \* \/ \E parent \in blocks, slotsAndBodies \in SUBSET (BlockSlots \X BLOCK_BODIES): ProposeBlocks(parent, slotsAndBodies)
    \/ \E <<targetBlock, sourceBlock>> \in block_graph_closure, srcSlot, tgtSlot \in CheckpointSlots, validators \in SUBSET VALIDATORS: 
        CastVotes(
            Checkpoint(sourceBlock, srcSlot), 
            Checkpoint(targetBlock, tgtSlot),
            validators
        )

=============================================================================