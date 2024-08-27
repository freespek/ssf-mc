----------------------------- MODULE ffg -----------------------------
(*
 * TODO
 *
 * Thomas Pani, 2024.
 *
 * Subject to Apache 2.0. See `LICENSE.md`.
 *)

EXTENDS FiniteSets, Integers, Sequences, typedefs

CONSTANT 
    \* @type: Int;
    MAX_BLOCK_SLOT,
    \* @type: Set($body);
    ALL_BLOCK_BODIES,
    \* @type: Seq($body);
    BLOCK_BODIES1,
    \* @type: Seq($body);
    BLOCK_BODIES2,
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
    \* @type: Int;
    chain1_next_idx,
    \* the set of all_blocks
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

\* @type: (Int, $body) => $block;
Block(slot, body) == [ slot |-> slot, body |-> body ]
\* @type: ($block, Int) => $checkpoint;
Checkpoint(block, checkpoint_slot) == <<block, checkpoint_slot>>
\* @type: (Str, $ffgVote) => $vote;
Vote(validator, ffgVote) == [ validator |-> validator, ffg_vote |-> ffgVote ]

GenesisBlockBody == 0
GenesisBlock == Block(0, GenesisBlockBody)
GenesisCheckpoint == Checkpoint(GenesisBlock, 0)

\* @type: $block => Bool;
IsOnChain1(b) == b \in chain1

\* @type: $block => Bool;
IsOnChain2(b) == b \in chain2

\* @type: ($block, $block) => Bool;
IsLeftAncestorOfRight(before, after) ==
   /\ before.slot <= after.slot
   /\ \/ IsOnChain1(before) /\ IsOnChain1(after)
      \/ IsOnChain2(before) /\ IsOnChain2(after)

\* @type: ($block, $block) => Bool;
AreConflictingBlocks(b1, b2) ==
    LET b1_on_chain1 == IsOnChain1(b1)
        b1_on_chain2 == IsOnChain2(b1)
        b2_on_chain1 == IsOnChain1(b2)
        b2_on_chain2 == IsOnChain2(b2)
    IN
    \/ b1_on_chain1 /\ ~b1_on_chain2 /\ b2_on_chain2 /\ ~b2_on_chain1
    \/ b1_on_chain2 /\ ~b1_on_chain1 /\ b2_on_chain1 /\ ~b2_on_chain2

\* @type: ($block) => Bool;
IsValidBlock(block) ==
    /\ block.body \in (ALL_BLOCK_BODIES \union {GenesisBlockBody})
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
\* @type: Int => Bool;
ProposeBlockOnChain1(slot) ==
    LET body == BLOCK_BODIES1[chain1_next_idx] IN
    LET new_block == Block(slot, body) IN
    /\ chain1_next_idx <= Len(BLOCK_BODIES1)
    /\ slot > chain1_tip_slot
    /\ all_blocks' = all_blocks \union { new_block }
    /\ chain1' = chain1 \union { new_block }
    /\ chain1_tip_slot' = slot
    /\ chain1_next_idx' = chain1_next_idx + 1
    /\ IF chain2_forked
       THEN UNCHANGED <<chain2, chain2_tip_slot, chain2_next_idx>>
       ELSE
         /\ chain2' = chain2 \union { new_block }
         /\ chain2_tip_slot' = slot
         /\ chain2_next_idx' = chain2_next_idx + 1
    /\ UNCHANGED <<ffg_votes, votes, justified_checkpoints, chain2_forked>>

\* Append a block to chain 2.
\* @type: Int => Bool;
ProposeBlockOnChain2(slot) ==
    LET body == BLOCK_BODIES2[chain2_next_idx]
        new_block == Block(slot, body)
    IN
    /\ chain2_forked' = TRUE
    /\ chain2_next_idx <= Len(BLOCK_BODIES2)
    /\ slot > chain2_tip_slot
    /\ all_blocks' = all_blocks \union { new_block }
    /\ chain2' = chain2 \union { new_block }
    /\ chain2_tip_slot' = slot
    /\ chain2_next_idx' = chain2_next_idx + 1
    /\ UNCHANGED <<chain1, chain1_tip_slot, chain1_next_idx, ffg_votes, votes, justified_checkpoints>>

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
    /\ UNCHANGED <<all_blocks, chain1, chain1_tip_slot, chain2, chain2_tip_slot, chain1_next_idx, chain2_next_idx, chain2_forked>>

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
    /\ chain1_next_idx = 2
    /\ chain2_next_idx = 2
    /\ chain2_forked \in BOOLEAN
    /\ ffg_votes = {}
    /\ votes = {}
    /\ justified_checkpoints = { GenesisCheckpoint }

Next == 
    \/ \E slot \in BlockSlots:
        \/ ProposeBlockOnChain1(slot)
        \/ ProposeBlockOnChain2(slot)
    \/ \E sourceBlock, targetBlock \in all_blocks, srcSlot, tgtSlot \in CheckpointSlots, validators \in SUBSET VALIDATORS: 
        CastVotes(
            Checkpoint(sourceBlock, srcSlot), 
            Checkpoint(targetBlock, tgtSlot),
            validators
        )

=============================================================================
