----------------------------- MODULE ffg -----------------------------
(*
 * TODO
 *
 * Thomas Pani, Igor Konnov, Jure Kukovec, 2024.
 *
 * Subject to Apache 2.0. See `LICENSE.md`.
 *)

EXTENDS Apalache, FiniteSets, Integers, Sequences, typedefs

CONSTANT 
    \* the maximal slot number
    \* @type: Int;
    MAX_BLOCK_SLOT,
    \* the maximal number in the block body
    \* @type: Int;
    MAX_BLOCK_BODY,
    \* the set of all validators (that can cast votes)
    \* @type: Set(Str);
    VALIDATORS,
    \* N = Cardinality(VALIDATORS)
    \* @type: Int;
    N

BlockSlots == 0..MAX_BLOCK_SLOT
CheckpointSlots == 0..(MAX_BLOCK_SLOT+2)

VARIABLES
    \* the set of all_blocks
    \* @type: Set($block);
    all_blocks,
    \* the set of blocks on chain 1
    \* @type: Set($block);
    chain1,
    \* the latest block on chain 1
    \* @type: $block;
    chain1_tip,
    \* the set of blocks on chain 2
    \* @type: Set($block);
    chain2,
    \* the latest block on chain 2
    \* @type: $block;
    chain2_tip,
    \* If chain2_fork_block_number is not equal to 0,
    \* then chain2 is a fork of chain1 starting at chain2_fork_block_number
    \* @type: Int;
    chain2_fork_block_number,
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
IsOnMainPath(b) == b.body >= 0

\* @type: $block => Bool;
IsOnForkPath(b) == b.body < 0

\* Has chain2 forked from chain1?
IsForked == chain2_fork_block_number /= 0

\* Compute the next body for a block and a path "main" or "fork".
\* @type: ($block, Str) => $body;
NextBody(b, path) ==
    IF IsOnMainPath(b) /\ path = "main"
    THEN b.body + 1           \* continue on the main path
    ELSE IF IsOnForkPath(b)
         THEN b.body - 1      \* continue on fork
         ELSE (-b.body) - 1     \* switch from main to fork

\* @type: ($block, $block) => Bool;
IsLeftAncestorOfRight(before, after) ==
   /\ before.slot <= after.slot
   /\ \/ before.body >= 0 /\ after.body >= 0 /\ before.body <= after.body
      \/ before.body < 0 /\ after.body < 0 /\ -before.body <= -after.body

\* @type: ($block, $block) => Bool;
AreConflictingBlocks(b1, b2) ==
    ~IsLeftAncestorOfRight(b1, b2) /\ ~IsLeftAncestorOfRight(b2, b1)

\* @type: ($block) => Bool;
IsValidBlock(block) ==
    /\ block.body \in (-MAX_BLOCK_BODY)..MAX_BLOCK_BODY
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
    LET new_block == Block(slot, NextBody(chain1_tip, "main")) IN
    /\ IsValidBlock(new_block)
    /\ slot > chain1_tip.slot
    /\ all_blocks' = all_blocks \union { new_block }
    /\ chain1' = chain1 \union { new_block }
    /\ chain1_tip' = new_block
    /\ IF IsForked
       THEN UNCHANGED <<chain2, chain2_tip>>
       ELSE
         /\ chain2' = chain2 \union { new_block }
         /\ chain2_tip' = new_block
    /\ UNCHANGED <<ffg_votes, votes, justified_checkpoints, chain2_fork_block_number>>

\* Append a block to chain 2.
\* @type: Int => Bool;
ProposeBlockOnChain2(slot) ==
    LET new_block == Block(slot, NextBody(chain2_tip, "fork")) IN
    /\ IsValidBlock(new_block)
    /\ slot > chain2_tip.slot
    /\ chain2_fork_block_number' =
        IF IsForked THEN chain2_fork_block_number ELSE new_block.body
    /\ all_blocks' = all_blocks \union { new_block }
    /\ chain2' = chain2 \union { new_block }
    /\ chain2_tip' = new_block
    /\ UNCHANGED <<chain1, chain1_tip, ffg_votes, votes, justified_checkpoints>>

JustifiedCheckpoints(viewVotes) ==
    \* @type: Set($checkpoint) => Set($checkpoint);
    LET AccJustified(justifiedSoFar, justifiedCheckpointSlot) ==
        LET candidateCheckpoints == { Checkpoint(block, justifiedCheckpointSlot): block \in all_blocks } IN
        LET newJustifiedCheckpoints == { c \in candidateCheckpoints: IsJustified(c, viewVotes, justifiedSoFar) } IN
        justifiedSoFar \union newJustifiedCheckpoints
    IN ApaFoldSeqLeft(AccJustified, { GenesisCheckpoint }, MkSeq(MAX_BLOCK_SLOT+2, (* @type: Int => Int; *) LAMBDA i: i))

\* @type: ($checkpoint, $checkpoint, Set(Str)) => Bool;
CastVotes(source, target, validators) ==
    LET ffgVote == [ source |-> source, target |-> target ] IN
    /\ IsValidFFGVote(ffgVote)
    /\ validators /= {}
    /\ ffg_votes' = ffg_votes \union { ffgVote }
    /\ votes' = votes \union { Vote(v, ffgVote): v \in validators }
    /\ justified_checkpoints' = JustifiedCheckpoints(votes')
    /\ UNCHANGED <<all_blocks, chain1, chain1_tip, chain2, chain2_tip, chain2_fork_block_number>>

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
    /\ chain1_tip = [ slot |-> 0, body |-> 0 ]
    /\ chain2_tip = [ slot |-> 0, body |-> 0 ]
    /\ chain1 = { GenesisBlock }
    /\ chain2 = { GenesisBlock }
    /\ chain2_fork_block_number = 0
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
