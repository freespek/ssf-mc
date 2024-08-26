----------------------------- MODULE ffg -----------------------------
(*
 * TODO
 *
 * Thomas Pani, 2024.
 *
 * Subject to Apache 2.0. See `LICENSE.md`.
 *)

EXTENDS FiniteSets, Integers, TLC, typedefs

CONSTANT 
    \* @type: Int;
    MAX_BLOCK_SLOT,
    \* @type: Set($body);
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
    all_blocks,
    \* the set of all_blocks
    \* @type: Set($block);
    chain1,
    \* @type: Int;
    chain1_tip_slot,
    \* the set of all_blocks
    \* @type: Set($block);
    chain2,
    \* @type: Int;
    chain2_tip_slot,
    \* @type: Set($ffgVote);
    ffg_votes,
    \* @type: Set($vote);
    votes,
    \* @type: Set($checkpoint);
    justified_checkpoints

\* @type: (Int, Str) => $block;
Block(slot, body) == [ slot |-> slot, body |-> body ]
\* @type: ($block, Int) => $checkpoint;
Checkpoint(block, checkpoint_slot) == <<block, checkpoint_slot>>
\* @type: (Str, $ffgVote) => $vote;
Vote(validator, ffgVote) == [ validator |-> validator, ffg_vote |-> ffgVote ]

GenesisBlockBody == "genesis"
GenesisBlock == Block(0, GenesisBlockBody)
GenesisCheckpoint == Checkpoint(GenesisBlock, 0)

\* @type: $block => Bool;
IsOnChain1(b) == b \in chain1

\* @type: $block => Bool;
IsOnChain2(b) == b \in chain2

\* @type: ($block, $block) => Bool;
IsLeftAncestorOfRight(before, after) ==
   /\ before.slot < after.slot
   /\ \/ IsOnChain1(before) /\ IsOnChain1(after)
      \/ IsOnChain2(before) /\ IsOnChain2(after)

\* @type: ($block, $block) => Bool;
AreConflictingBlocks(b1, b2) ==
    LET b1_on_chain1 == IsOnChain1(b1)
        b1_on_chain2 == IsOnChain2(b1)
        b2_on_chain1 == IsOnChain1(b2)
        b2_on_chain2 == IsOnChain2(b2)
    IN
    \/ b1_on_chain1 /\ ~b1_on_chain2 /\ b2_on_chain2
    \/ b1_on_chain2 /\ ~b1_on_chain1 /\ b2_on_chain1

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

\* @type: ($ffgVote) => Bool;
IsValidFFGVote(vote) ==
    /\ IsValidCheckpoint(vote.source)
    /\ IsValidCheckpoint(vote.target)
    /\ vote.source[2] < vote.target[2]
    /\ IsLeftAncestorOfRight(vote.source[1], vote.target[1])

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
                /\ IsLeftAncestorOfRight(checkpoint[1], ffgVote.target[1])
                /\ IsLeftAncestorOfRight(ffgVote.source[1], checkpoint[1])
                \* L8:
                /\ ffgVote.target[2] = checkpoint[2] }    
        IN 3 * Cardinality(validatorsWhoCastJustifyingVote) >= 2 * N

\* @type: ($checkpoint, Set($vote), Set($checkpoint)) => Bool;
IsFinalized(checkpoint, viewVotes, justifiedCheckpoints) ==
    \/ checkpoint = GenesisCheckpoint
    \/ /\ checkpoint \in justifiedCheckpoints
       /\ LET validatorsWhoCastFinalizingVote == { 
            v \in VALIDATORS: \E finalizingVote \in viewVotes:
                /\ finalizingVote.validator = v
                /\ LET ffgVote == finalizingVote.ffg_vote IN
                    \* L14:
                    /\ ffgVote.source = checkpoint
                    \* L15:
                    /\ ffgVote.target[2] = checkpoint[2] + 1 }
        IN 3 * Cardinality(validatorsWhoCastFinalizingVote) >= 2 * N

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

\* Append a block to chain 1.
\* @type: (Int, Str) => Bool;
ProposeBlockOnChain1(slot, body) ==
    LET new_block == Block(slot, body) IN
    /\ slot > chain1_tip_slot
    /\ all_blocks' = all_blocks \union { new_block }
    /\ chain1' = chain1 \union { new_block }
    /\ chain1_tip_slot' = slot
    /\ UNCHANGED <<chain2, chain2_tip_slot, ffg_votes, votes, justified_checkpoints>>

\* Append a block to chain 2.
\* @type: (Int, Str) => Bool;
ProposeBlockOnChain2(slot, body) ==
    LET new_block == Block(slot, body) IN
    /\ slot > chain2_tip_slot
    /\ all_blocks' = all_blocks \union { new_block }
    /\ chain2' = chain2 \union { new_block }
    /\ chain2_tip_slot' = slot
    /\ UNCHANGED <<chain1, chain1_tip_slot, ffg_votes, votes, justified_checkpoints>>

\* @type: ($checkpoint, $checkpoint, Set(Str)) => Bool;
CastVotes(source, target, validators) ==
    LET ffgVote == [ source |-> source, target |-> target ] IN
    /\ IsValidFFGVote(ffgVote)
    /\ validators /= {}
    /\ ffg_votes' = ffg_votes \union { ffgVote }
    /\ votes' = votes \union { Vote(v, ffgVote): v \in validators }
    /\ LET allCheckpoints == {Checkpoint(block, i): block \in all_blocks, i \in CheckpointSlots}
       IN \E allJustifiedCheckpoints \in SUBSET allCheckpoints:
        /\ justified_checkpoints' = allJustifiedCheckpoints
        /\ \A c \in allJustifiedCheckpoints: IsJustified(c, votes', allJustifiedCheckpoints)
        /\ \A c \in (allCheckpoints \ allJustifiedCheckpoints): ~IsJustified(c, votes', allJustifiedCheckpoints)
    /\ UNCHANGED <<all_blocks, chain1, chain1_tip_slot, chain2, chain2_tip_slot>>

ExistTwoConflictingBlocks == \A b1, b2 \in all_blocks: ~AreConflictingBlocks(b1, b2)
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

Init == 
    /\ all_blocks = { GenesisBlock }
    /\ chain1_tip_slot = 0
    /\ chain2_tip_slot = 0
    /\ chain1 = { GenesisBlock }
    /\ chain2 = { GenesisBlock }
    /\ ffg_votes = {}
    /\ votes = {}
    /\ justified_checkpoints = { GenesisCheckpoint }

Next == 
    \/ \E slot \in BlockSlots, body \in BLOCK_BODIES:
        \/ ProposeBlockOnChain1(slot, body)
        \/ ProposeBlockOnChain2(slot, body)
    \/ \E sourceBlock, targetBlock \in all_blocks, srcSlot, tgtSlot \in CheckpointSlots, validators \in SUBSET VALIDATORS: 
        CastVotes(
            Checkpoint(sourceBlock, srcSlot), 
            Checkpoint(targetBlock, tgtSlot),
            validators
        )

=============================================================================
