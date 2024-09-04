----------------------------- MODULE accountable_safety_all_cases -----------------------------


EXTENDS FiniteSets, Integers, typedefs, TLC

CONSTANTS
            \* @type: Int;
            N,
            \* @type: Set(Int);
            Validators,
            \* @type: Int;
            MAX_BLOCK_SLOT,
            \* @type: Int;
            MAX_BLOCK_BODY,
            \* @type: Int;
            NUMBER_OF_CHECKPOINTS,
            \* @type: Int;
            LEN_1,
            \* @type: Int;
            LEN_2

\* @type: Set(Int);
Block_Slots == 0..MAX_BLOCK_SLOT

\* @type: Set(Int);
Block_Bodies == 0..MAX_BLOCK_BODY

\* @type: (Int, Int) => $block;
Block(slot, body) ==
    [
        slot |-> slot,
        body |-> body
    ]

Genesis_Block == Block(0, 0)
All_Blocks == {Block(slot, body): slot \in Block_Slots, body \in Block_Bodies} 

\* @type: Set(Int);
Checkpoint_Slots == 0..MAX_BLOCK_SLOT+2

\* @type: ($block, Int) => $checkpoint;
Checkpoint(block, checkpoint_slot) == [ chkp_block |-> block, chkp_slot |-> checkpoint_slot ]    

Genesis_Checkpoint == Checkpoint(Genesis_Block, 0)
All_Checkpoints == {Checkpoint(block, i): block \in All_Blocks, i \in Checkpoint_Slots}

\* @type: ($checkpoint, $checkpoint) => $ffgVote;
FFGVote(source, target) == [ source |-> source, target |-> target ]

\* All_FFG_Votes == {FFGVote(s, t) : s \in All_Checkpoints, t \in All_Checkpoints} 

\* @type: (Int, $ffgVote) => $vote;
Vote(v, ffgVote) == [validator |-> v, ffg_vote |-> ffgVote] 

\* All_Votes == {Vote(v, ffgVote) : v \in Validators, ffgVote \in All_FFG_Votes} 

VARIABLES
    \* @type: Int -> $block;
    chain_1,
    \* @type: Int -> $block;
    chain_2,
    \* @type: Set($checkpoint);
    set_of_checkpoints,
    \* @type: Int;
    fork_idx,
    \* @type: Int;
    idx_of_B_f_1,
    \* @type: $block;
    B_f_1,
    \* @type: $checkpoint;
    C_f_1,                      (*  C_f in Lemma 1. Assume C_f_1 in chain_1  *)
    \* @type: Int;
    idx_of_B_j_2,
    \* @type: $block;
    B_j_2,                      (*  B' in Lemma 1. Assume B_j_2 in chain 2.  *)
    \* @type: $checkpoint;
    C_j_2, 
    \* @type: Set(Int);
    voters_of_C_f_1,            (*  Validators votes for the finalization or justification of C_f_1.     *)
    \* @type: Set(Int);
    voters_of_C_j_2,            (*  Validators votes for the justification of B_f_2.    *)
    \* @type: $checkpoint;
    C_f_2
    

(*  1.  The first block is Genesis_Checkpoint.
    2.  Block slots are strictly increasing.
    3.  Block bodies are strictly increasing.
 *)
\* @type: (Int -> $block, Int) => Bool;
ConstraintsOnChain(chain, LEN) ==
    /\  chain[1] = Genesis_Block
    /\  \A i \in 1..(LEN - 1) : chain[i].slot < chain[i + 1].slot
    /\  \A i \in 1..(LEN - 1) : chain[i].body < chain[i + 1].body
    
\* @type: (Int -> $block, Int) => Bool;
InitChain(chain, LEN) ==
    /\  chain \in [ 1..LEN -> All_Blocks ]
    /\  ConstraintsOnChain(chain, LEN)

(*  If blocks B_1 in chain_1 and B_2 in chain_2 have the same body, they have the same slot. 
    Note that: NoBlocksHaveSameBodyButDifferentSlots is not implied by the conjunction of
    ConstraintsOnChain(chain_1, LEN_1) and ConstraintsOnChain(chain_2, LEN_2).
 *)
NoBlocksHaveSameBodyButDifferentSlots ==
    /\  \A i \in 1..LEN_1, j \in 1..LEN_2 : chain_1[i].body = chain_2[j].body => chain_1[i].slot = chain_2[j].slot

InitChains ==
    /\  InitChain(chain_1, LEN_1)
    /\  InitChain(chain_2, LEN_2)
    /\  NoBlocksHaveSameBodyButDifferentSlots

(*  We require fork_idx <= LEN_1 - 1 and fork_idx <= LEN_2 - 1 to ensure that
        -   We can initialize two conflicting blocks B_f_1 and B_j_2 in chain_1
            and chain_2, respectively. 
        -   We can initialize a target checkpoint for the finalization of B_f_1.
    There is no shared block body in the postfixes of chain_1 and chain_2.
    No pair of blocks in the postfixes of chain_1 and chain_2 are proposed in the same slot.
 *)
InitFork ==
    /\  fork_idx \in 1..(LEN_1 - 2)
    /\  fork_idx <= LEN_2 - 1
    /\  \A i \in 1..LEN_1 : i <= fork_idx => chain_1[i] = chain_2[i]
    /\  \A i \in 1..LEN_1, j \in 1..LEN_2 : 
            /\  i > fork_idx
            /\  j > fork_idx
            =>  /\ chain_1[i].body /= chain_2[j].body
                /\ chain_1[i].slot /= chain_2[j].slot

\* @type: ($block) => Bool;
IsValidBlock(block) ==
    /\  block.body \in Block_Bodies
    /\  block.slot \in Block_Slots

\* @type: ($checkpoint) => Bool;
IsValidCheckpoint(checkpoint) == 
    /\  IsValidBlock(checkpoint.chkp_block)
    /\  \/  checkpoint = Genesis_Checkpoint
        \/  checkpoint.chkp_slot > checkpoint.chkp_block.slot
        
\* @type: (Int -> $block, Int, $checkpoint) => Bool;
IsCheckpointForChain(chain, LEN, c) ==
    /\  \E i \in 1..LEN : c.chkp_block = chain[i]

(*  -   Initialize a set_of_checkpoints for blocks in chain_1 and chain_2
        whose cardinality is NUMBER_OF_CHECKPOINTS.
    -   For every valid checkpoint, its block is in chain_1 or chain_2.
    -   For every block b in chain_1, at least one checkpoint has b as its block.
        Similar thing for blocks in chain_2.
 *)
InitCheckpoints ==
    /\  set_of_checkpoints \in SUBSET All_Checkpoints
    /\  Genesis_Checkpoint \in set_of_checkpoints
    /\  Cardinality(set_of_checkpoints) = NUMBER_OF_CHECKPOINTS
    /\  \A c \in set_of_checkpoints : 
            /\  IsValidCheckpoint(c)
            /\  \/ IsCheckpointForChain(chain_1, LEN_1, c)
                \/ IsCheckpointForChain(chain_2, LEN_2, c) 
    /\  \A i \in 1..LEN_1 : \E c \in set_of_checkpoints : c.chkp_block = chain_1[i] 
    /\  \A i \in 1..LEN_2 : \E c \in set_of_checkpoints : c.chkp_block = chain_2[i] 
    
\* @type: (Int -> $block, Int, $checkpoint, $checkpoint) => Bool;
IsAncestorCheckpoint(chain, LEN, chkp1, chkp2) ==
    \E i, j \in 1..LEN : i <= j /\ chkp1.chkp_block = chain[i] /\ chkp2.chkp_block = chain[j]
    
\* @type: (Int -> $block, Int, $ffgVote) => Bool;
IsFFGVoteOnChain(chain, LEN, vote) ==
    \E i \in 1..LEN : \E j \in 1..LEN : 
        /\ i <= j
        /\  vote.source.chkp_block = chain[i]
        /\  vote.target.chkp_block = chain[j]

\* @type: (Int -> $block, Int, $ffgVote) => Bool;
IsValidFFGVote(chain, LEN, vote) ==
    /\  IsValidCheckpoint(vote.source)
    /\  IsValidCheckpoint(vote.target)
    /\  IsFFGVoteOnChain(chain, LEN, vote)
    /\  vote.source.chkp_slot < vote.target.chkp_slot

\* @type: (Int -> $block, Int, $checkpoint, $ffgVote) => Bool;
IsFFGVoteForFinalization(chain, LEN, checkpoint, ffg_vote) ==
    /\  IsValidFFGVote(chain, LEN, ffg_vote)
    /\  ffg_vote.source = checkpoint
    /\  ffg_vote.target.chkp_slot = ffg_vote.source.chkp_slot + 1
           
\* @type: (Int -> $block, Int, $checkpoint, $ffgVote) => Bool;
IsFFGVoteForJustification(chain, LEN, checkpoint, ffg_vote) ==
    /\  IsValidFFGVote(chain, LEN, ffg_vote)
    /\  checkpoint.chkp_slot = ffg_vote.target.chkp_slot
    /\  \E i, j, k \in 1..LEN : 
            /\  i < j        (*  Since the source checkpoint was justified but checkpoint is not justified. *)
            /\  j <= k
            /\  checkpoint.chkp_block = chain[j]
            /\  ffg_vote.source.chkp_block = chain[i]
            /\  ffg_vote.target.chkp_block = chain[k]

(*  -   B_f_1 is a block in chain_1 after fork, and C_f_1 is a corresponding checkpoing 
        for B_f_1.
    -   We just assume C_f_1 and B_f_1 are finalized.
    -   Note that C_f_1 can be used as a source checkpoint for FFG votes which supports 
        the finalization of C_f_1.
    -   There exists a valid checkpoint C_f_1_target after C_f_1 such that C_f_1_target 
        can become a target checkpoint of an FFG vote supporting the finalization of C_f_1. 
    -   Formally, we have 
            C_f_1_source.chkp_block = B_f_1
            C_f_1_target.chkp_slot = C_f_1_source.chkp_slot + 1
            IsValidFFGVote(FFGVote(C_f_1_source, C_f_1_target))

 *)
Init_C_f_1 ==
    /\  idx_of_B_f_1 \in 1..LEN_1
    /\  idx_of_B_f_1 > fork_idx
    /\  B_f_1  = chain_1[idx_of_B_f_1]
    /\  C_f_1 \in set_of_checkpoints
    /\  C_f_1.chkp_block = B_f_1
    /\  \E f_target \in set_of_checkpoints : 
            LET ffg_vote == FFGVote(C_f_1, f_target)
            IN  IsFFGVoteForFinalization(chain_1, LEN_1, C_f_1, ffg_vote)
    /\  \E j_source, j_target \in set_of_checkpoints : 
            LET ffg_vote == FFGVote(j_source, j_target)
            IN  IsFFGVoteForJustification(chain_1, LEN_1, C_f_1, ffg_vote)
            
(*  C_f_2 is a finalized block in chain_2 such that 
        - C_f_2 conflicts with C_f_1, and
        - C_f_1.chkp_slot <= C_f_2.chkp_slot.
 *)
Init_C_f_2 ==
    /\  C_f_2 \in set_of_checkpoints 
    /\  \E idx \in 1..LEN_2 : 
            /\ idx > fork_idx
            /\ chain_2[idx] = C_f_2.chkp_block
    /\  \E f_target \in set_of_checkpoints : 
            LET ffg_vote == FFGVote(C_f_2, f_target)
            IN  IsFFGVoteForFinalization(chain_2, LEN_2, C_f_2, ffg_vote)
    /\  \E j_source, j_target \in set_of_checkpoints : 
            LET ffg_vote == FFGVote(j_source, j_target)
            IN  IsFFGVoteForJustification(chain_2, LEN_2, C_f_2, ffg_vote)
    /\  C_f_1.chkp_slot <= C_f_2.chkp_slot
            
(*  Let C_j_2 be a checkpoint such that
        -   C_f_1.chkp_slot < C_j_2.chkp_slot, and
        -   B_f_1 is not a prefix of B_j_2.
    
    So, we know that
        -   B_j_2 is not in the postfix of chain_1.
        -   Either B_j_2 is a strict ancestor of B_f_1
            or B_j_2 conflicts with B_f_1.
        
    For every checkpoint c in set_of_checkpoints, we have
        -   c.chkp_slot >= C_j_2.chkp_slot, 
        -   c.chkp_slot < C_f_1.chkp_slot
        -   c.chkp_slot < C_j_2.chkp_slot and c.chkp_block is a descendant of C_f_1
    
    The block of C_f_1 is not a prefix of the block of C_j_2.
    -   There exists a checkpoint C_target after C_j_2 such that C_target can become
        a target checkpoint of an FFG vote for the justification of C_j_2. Hence,
        it implies C_target.chkp_slot = C_j_2.chkp_slot.
 *)
Init_C_j_2_that_can_be_different_from_C_f_2 ==
    /\  C_j_2 \in set_of_checkpoints 
    /\  B_j_2 = C_j_2.chkp_block
    /\  \/  /\  idx_of_B_j_2 \in 1..LEN_2              (*  B_j_2 conflicts with B_f_1          *)
            /\  B_j_2  = chain_2[idx_of_B_j_2]
            /\  idx_of_B_j_2 > fork_idx
        \/  /\  idx_of_B_j_2 \in 1..LEN_1              (*  B_j_2 is a strict ancestor of B_f_1 *)
            /\  B_j_2  = chain_1[idx_of_B_j_2]
            /\  idx_of_B_j_2 < idx_of_B_f_1
    /\  \A c \in set_of_checkpoints :
            ~IsAncestorCheckpoint(chain_1, LEN_1, C_f_1, c)
            =>  \/  c.chkp_slot <= C_f_1.chkp_slot
                \/  c.chkp_slot > C_j_2.chkp_slot
                \/  /\  c.chkp_slot = C_j_2.chkp_slot  (*  This constraint is missing in the current proof *)  
                    /\  \/  IsAncestorCheckpoint(chain_1, LEN_1, C_j_2, c)
                        \/  IsAncestorCheckpoint(chain_2, LEN_2, C_j_2, c)
    (*  ffg_vote is used in the justification of C_j_2.
        ffg_vote_1 is used in the justifiaction of the source checkpoint of ffg_vote.
     *) 
    /\  \E source, target, s1, t1 \in set_of_checkpoints : 
            LET ffg_vote == FFGVote(source, target)
                ffg_vote_1 == FFGVote(s1, t1)
            IN  \/  /\  IsFFGVoteForJustification(chain_2, LEN_2, C_j_2, ffg_vote)
                    /\  IsFFGVoteForJustification(chain_2, LEN_2, source, ffg_vote_1)
                \/  /\  IsFFGVoteForJustification(chain_1, LEN_1, C_j_2, ffg_vote)
                    /\  IsFFGVoteForJustification(chain_1, LEN_1, source, ffg_vote_1)
                
Init_C_j_2_that_is_the_same_with_C_f_2 ==
    /\  C_j_2 = C_f_2
    /\  B_j_2 = C_j_2.chkp_block
    /\  idx_of_B_j_2 \in 1..LEN_2              (*  B_j_2 conflicts with B_f_1          *)
    /\  B_j_2 = chain_2[idx_of_B_j_2]
            
Init_C_j_2 ==
    \/  /\ C_f_1.chkp_slot = C_f_2.chkp_slot
        /\  Init_C_j_2_that_is_the_same_with_C_f_2
    \/  /\ C_f_1.chkp_slot < C_f_2.chkp_slot
        /\  Init_C_j_2_that_can_be_different_from_C_f_2

InitVoters ==
    /\  voters_of_C_f_1 \in SUBSET Validators
    /\  3 * Cardinality(voters_of_C_f_1) >= 2 * N
    /\  voters_of_C_j_2 \in SUBSET Validators
    /\  3 * Cardinality(voters_of_C_j_2) >= 2 * N     

(*  -   C_f_1's checkpoint slot is less than or equals to C_f_2's.
    -   Except of C_f_2, other checkpoints conflicting with C_f_1 have different slots with C_f_1's.
 *)
AssumptionOnConflictingCheckpoint ==
    /\  C_f_1.chkp_slot <= C_f_2.chkp_slot
    /\  \A c \in set_of_checkpoints :
            /\  c /= C_f_2
            /\  \E idx \in 1..LEN_2 : fork_idx < idx /\ c.chkp_block = chain_2[idx]
            =>  c.chkp_slot /= C_f_1.chkp_slot

Init ==
    /\  InitChains
    /\  InitFork
    /\  InitCheckpoints
    /\  InitVoters
    /\  Init_C_f_1
    /\  Init_C_f_2
    /\  Init_C_j_2
    /\  AssumptionOnConflictingCheckpoint
    

(*  Check: Init => OnlyProposedOnce
    That should be correct and able to model-check.
 *)
OnlyProposedOnce ==
    LET all_blocks_in_two_chains == {chain_1[i] : i \in 1..LEN_1} \cup {chain_2[i] : i \in 1..LEN_2}
        all_slots_in_two_chains == {chain_1[i].slot : i \in 1..LEN_1} \cup {chain_2[i].slot : i \in 1..LEN_2}
    IN  \A slot \in all_slots_in_two_chains :
            \A b_1, b_2 \in all_blocks_in_two_chains :
                b_1.slot = b_2.slot => b_1.body = b_2.body

\* @type: ($ffgVote, $ffgVote) => Bool;
ViolatesE1(ffg_vote_1, ffg_vote_2) ==
    /\  ffg_vote_1 /= ffg_vote_2
    /\  ffg_vote_1.target.chkp_slot = ffg_vote_2.target.chkp_slot

\* @type: ($checkpoint, $checkpoint) => Bool;
Chkp_Less(checkpoint_1, checkpoint_2) ==
    \/  checkpoint_1.chkp_slot < checkpoint_2.chkp_slot
    \/  /\  checkpoint_1.chkp_slot = checkpoint_2.chkp_slot
        /\  checkpoint_1.chkp_block.slot < checkpoint_2.chkp_block.slot

\* @type: ($ffgVote, $ffgVote) => Bool;
ViolatesE2(ffg_vote_1, ffg_vote_2) ==
    /\  Chkp_Less(ffg_vote_2.source, ffg_vote_1.source)
    /\  ffg_vote_1.target.chkp_slot < ffg_vote_2.target.chkp_slot

\* @type: ($vote, $vote) => Bool;
IsSlashable(vote_1, vote_2) ==
    /\  vote_1.validator = vote_2.validator
    /\  \/  ViolatesE1(vote_1.ffg_vote, vote_2.ffg_vote) 
        \/  ViolatesE2(vote_1.ffg_vote, vote_2.ffg_vote) 
        \/  ViolatesE2(vote_2.ffg_vote, vote_1.ffg_vote)


(*  Case 1: C_f_1 and C_j_2 have the same checkpoint slot.
 *)
Case1 ==
    LET voters == voters_of_C_f_1 \cap voters_of_C_j_2
    IN  /\  3 * Cardinality(voters) >= N
        /\  \A v \in voters : \A s1, t1, s2, t2 \in set_of_checkpoints : 
                LET ffg_vote_1 == FFGVote(s1, t1)
                    ffg_vote_2 == FFGVote(s2, t2)
                    vote_1 == Vote(v, ffg_vote_1)
                    vote_2 == Vote(v, ffg_vote_2)
                IN  /\  IsFFGVoteForJustification(chain_1, LEN_1, C_f_1, ffg_vote_1)
                    /\  IsFFGVoteForJustification(chain_2, LEN_2, C_j_2, ffg_vote_2)
                    =>  IsSlashable(vote_1, vote_2)

(*  -   This property checks the intersection set called voters has at least one third of validators.
    -   Moreover, let v be an arbitrary validator in voters, ffg_vote_1 be an arbitrary FFG vote
        that can support the finalization of C_f_1, and ffg_vote_2 be an arbitrary FFG vote
        that can support the justification of C_j_2.
    -   This property also checks that ffg_vote_1 and ffg_vote_2 are always slashable.
    -   Votes vote_1 and vote_2 are used only to make the specification similar to the Python spec.
    -   Assume that C_j_2 is in chain_1.
 *)
Case3 ==
    LET voters == voters_of_C_f_1 \cap voters_of_C_j_2
    IN  /\  3 * Cardinality(voters) >= N
        /\  \A v \in voters : \A s1, t1, s2, t2 \in set_of_checkpoints : 
                LET ffg_vote_1 == FFGVote(s1, t1)
                    ffg_vote_2 == FFGVote(s2, t2)
                    vote_1 == Vote(v, ffg_vote_1)
                    vote_2 == Vote(v, ffg_vote_2)
                IN  /\  IsFFGVoteForFinalization(chain_1, LEN_1, C_f_1, ffg_vote_1)
                    /\  IsFFGVoteForJustification(chain_1, LEN_1, C_j_2, ffg_vote_2)
                    /\  (   s1.chkp_slot = s2.chkp_slot                                (*  This is case 1 *)
                            =>  \/ IsAncestorCheckpoint(chain_1, LEN_1, s1, s2) 
                                \/ IsAncestorCheckpoint(chain_2, LEN_2, s2, s1) 
                        )
                    =>  IsSlashable(vote_1, vote_2)

OtherCases ==   
    LET voters == voters_of_C_f_1 \cap voters_of_C_j_2
    IN  /\  3 * Cardinality(voters) >= N
        /\  \A v \in voters : \A t1, s2, t2 \in set_of_checkpoints : 
                LET ffg_vote_1 == FFGVote(C_f_1, t1)
                    ffg_vote_2 == FFGVote(s2, t2)
                    vote_1 == Vote(v, ffg_vote_1)
                    vote_2 == Vote(v, ffg_vote_2)
                IN  \/  /\  IsFFGVoteForFinalization(chain_1, LEN_1, C_f_1, ffg_vote_1)
                        /\  IsFFGVoteForJustification(chain_1, LEN_1, C_j_2, ffg_vote_2)
                        =>  /\ C_f_1.chkp_slot /= s2.chkp_slot 
                            /\ IsSlashable(vote_1, vote_2)
                    \/  /\  IsFFGVoteForFinalization(chain_1, LEN_1, C_f_1, ffg_vote_1)
                        /\  IsFFGVoteForJustification(chain_2, LEN_2, C_j_2, ffg_vote_2)
                        =>  /\ C_f_1.chkp_slot /= s2.chkp_slot 
                            /\ IsSlashable(vote_1, vote_2)
                    
AtLeastOneThirdIsSlashable ==
    \/  C_f_1.chkp_slot = C_j_2.chkp_slot => Case1
    \/  C_f_1.chkp_slot < C_j_2.chkp_slot => OtherCases
                    
Next == UNCHANGED <<    chain_1,
                        chain_2,
                        set_of_checkpoints,
                        fork_idx,
                        idx_of_B_f_1,
                        B_f_1,
                        C_f_1,
                        idx_of_B_j_2,
                        B_j_2,
                        C_j_2, 
                        voters_of_C_f_1,
                        voters_of_C_j_2,
                        C_f_2
                    >>

=============================================================================
