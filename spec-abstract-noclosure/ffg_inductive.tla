---------------------------- MODULE ffg_inductive -----------------------------
(**
 * An inductive invariant for the FFG module.
 *)
EXTENDS ffg

LOCAL Abs(x) == IF x >= 0 THEN x ELSE -x

\* inject an instance of AccountableSafety right in the initial state
InitAccountableSafety ==
    \* assume that there is a disagreement
    /\ \E c1, c2 \in justified_checkpoints:
        /\ IsFinalized(c1, votes, justified_checkpoints)
        /\ IsFinalized(c2, votes, justified_checkpoints)
        /\ AreConflictingBlocks(c1[1], c2[1])
    \* there is no way to identify the violating validators
    /\ ~SlashableNodesOver

BlocksInv ==
    /\ -MAX_BLOCK_BODY <= chain2_fork_block_number /\ chain2_fork_block_number <= 0
    /\ all_blocks = chain1 \union chain2
    \* chain1_tip is the maximum block in chain 1
    /\ \A b \in chain1: b.body <= chain1_tip.body
    \* block numbers on chain 1 simply go from 0 to chain1_tip.body
    /\ \A b1, b2 \in chain1:
        /\ b1.body >= 0 /\ b1.body <= chain1_tip.body
        /\ (b1.body >= b2.body) <=> (b1.slot >= b2.slot)
    \* there are no gaps in the block numbers
    /\ \A i \in 0..MAX_BLOCK_BODY:
        i <= chain1_tip.body => \E b \in chain1: b.body = i
    \* chain2_tip is the maximum block in chain 2
    /\ \A b \in chain2: Abs(b.body) <= Abs(chain2_tip.body)
    \* Positive block numbers on chain 2 go from 0 to -chain2_fork_block_number - 1, if there was a fork.
    \* Negative block numbers on chain 2 go from -chain2_fork_block_number to chain2_tip.body, if there was a fork.
    \* If there was no fork, all block numbers on chain 2 are non-negative.
    /\ \A b1, b2 \in chain2:
        /\ (b1.body >= 0) => (b1.body < -chain2_fork_block_number) \/ ~IsForked
        /\ (b1.body < 0)  => (b1.body <= chain2_fork_block_number) /\ IsForked
        /\ (Abs(b1.body) >= Abs(b2.body)) <=> (b1.slot >= b2.slot)
    \* there are no gaps in the block numbers (some of them are negative)
    /\ \A i \in 0..MAX_BLOCK_BODY:
        i <= Abs(chain2_tip.body) => \E b \in chain2: Abs(b.body) = i
    \* chain2_fork_block_number has to be in chain2
    /\ \E b \in chain2: b.body = chain2_fork_block_number
    \* when there is no fork, the tips coincide
    /\ ~IsForked => chain2_tip = chain1_tip
    \* before the fork point, chain2 and chain1 coincide
    /\ \A b \in chain2:
        b.body >= 0 => b \in chain1
    /\ GenesisBlock \in chain1
    /\ GenesisBlock \in chain2
    
VotesInv ==
    /\ \A ffgVote \in ffg_votes: IsValidFFGVote(ffgVote)
    /\ \A vote \in votes:
        /\ vote.ffg_vote \in ffg_votes
        /\ vote.validator \in VALIDATORS

CheckpointsInv ==        
    \*/\ justified_checkpoints = JustifiedCheckpoints(votes)
    /\ GenesisCheckpoint \in justified_checkpoints
    /\ \A c \in justified_checkpoints: IsJustified(c, votes, justified_checkpoints)
    /\ LET allCheckpoints == {Checkpoint(block, i): block \in all_blocks, i \in CheckpointSlots} IN
       \A c \in (allCheckpoints \ justified_checkpoints):
         ~IsJustified(c, votes, justified_checkpoints)

IndInv ==
    /\ BlocksInv
    /\ VotesInv
    /\ CheckpointsInv

===============================================================================
