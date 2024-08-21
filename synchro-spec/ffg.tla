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
    justified_checkpoints,
    \* @type: Int;
    current_slot

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

\* @type: ($block, Str) => Bool;
ProposeBlock(parent, body) ==
    LET this == Block(current_slot, body) IN
    /\ current_slot > parent.slot
    \* no block gets proposed twice (e.g. with different parents)
    /\ this \notin blocks
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

(*
The most notable difference in the synchronous spec is that 
If, at current_slot, a checkpoint with a slot number i < current_slot
has not been justified, there will never be a vote justifying it in the future,
because the votes are always cast s.t. the target checkpoint slot is current_slot.

This allows us to compute justified_checkpoints incrementally.
*)
\* @type: ($checkpoint, $checkpoint, Set(Str)) => Bool;
CastVotes(source, target, validators) ==
    LET ffgVote == [ source |-> source, target |-> target ] IN
    /\ UNCHANGED <<blocks, block_graph, block_graph_closure>>
    /\ IsValidFFGVote(ffgVote)
    /\ validators /= {}
    /\ ffg_votes' = ffg_votes \union { ffgVote }
    /\ votes' = votes \union { Vote(v, ffgVote): v \in validators }
    \* The ffg vote (b1, s1) -> (b2, s2) can justify (b,s2), for all blocks b1 <= b <= b2 in the block graph
    \* We branch, based on whether there is a quorum of the ffg vote
    /\ 
        IF (3 * Cardinality({v \in VALIDATORS: Vote(v, ffgVote) \in votes'}) >= 2 * N /\ source \in justified_checkpoints)
        THEN LET newJustifiedBlocks == { b \in blocks: 
                /\ <<target[1], b>> \in block_graph_closure
                /\ <<b, source[1]>> \in block_graph_closure } 
            IN justified_checkpoints' = justified_checkpoints \union {Checkpoint(b, target[2]): b \in newJustifiedBlocks}
        ELSE UNCHANGED justified_checkpoints

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

MayAdvanceSlot ==
    \E i \in Int:
        /\ i >= current_slot
        /\ current_slot' = i
    
Init == 
    /\ blocks = {GenesisBlock}
    /\ block_graph_closure = { Edge(GenesisBlock,GenesisBlock) }
    /\ block_graph = {}
    /\ ffg_votes = {}
    /\ votes = {}
    /\ justified_checkpoints = {GenesisCheckpoint}
    /\ current_slot = 1

Next == 
    /\ MayAdvanceSlot
    /\ \/ \E parent \in blocks, body \in BLOCK_BODIES: ProposeBlock(parent, body)
       \/ \E <<targetBlock, sourceBlock>> \in block_graph_closure, srcSlot\in CheckpointSlots, validators \in SUBSET VALIDATORS: 
        CastVotes(
            Checkpoint(sourceBlock, srcSlot), 
            Checkpoint(targetBlock, current_slot),
            validators
        )

=============================================================================