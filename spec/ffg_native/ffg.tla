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
    block_graph

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

IsValidCheckpoint(checkpoint) == 
    LET block == checkpoint[1]
        checkpoint_slot == checkpoint[2]
    IN
        \/ checkpoint = GenesisCheckpoint
        \* Section 3.Checkpoints: "Importantly, the slot c for the checkpoint occurs after the slot B.p where the block was proposed"
        \//\ checkpoint_slot \in CheckpointSlots
          /\ checkpoint_slot > block.slot


\* @type: ($block, Int, Str) => Bool;
ProposeBlock(parent, slot, body) ==
    LET this == Block(slot, body) IN
    /\ slot > parent.slot
    /\ blocks' = blocks \union {this}
    /\ block_graph' = block_graph \union {<<this, parent>>}

CastFFGVote(vote_slot, source, target)


Init == 
    /\ blocks = {GenesisBlock}
    /\ block_graph = {}

Next == 
    \/ \E parent \in blocks, slot \in BlockSlots, body \in BLOCK_BODIES: ProposeBlock(parent, slot, body)

GraphIsATree == TRUE

Inv == 
    GraphIsATree


=============================================================================