----------------------------- MODULE MC_case_1 -----------------------------
(*
    This spec is used to test APALACHE's performance in a special case:
    There are two conflicting finalized checkpoints who have the same checkpoint slot.
        \* @type: $checkpoint;
        conflicting_justified_checkpoint_1,
        \* @type: $checkpoint;
        conflicting_justified_checkpoint_2

    The justification of the two checkpoints are supported by votes from two sets 
    of validators, respectively.    
        \* @type: Set(Int);
        validators_support_conflicting_justified_checkpoint_1,
        \* @type: Set(Int);
        validators_support_conflicting_justified_checkpoint_2

    The property AtLeastOneThirdIsSlashable is to formalize "Weak" Accountable Safety.

    This spec is in a very high abstract level:
        -   The block tree and chain are not specified. Only the forementioned checkpoints are specified.
        -   The ancester-decesdand relationship are not specified.
        -   The whole set of votes from validators are not specificied.
        -   The votes from the two forementioned sets of validators are not specified explicitly. 
            Instead, AtLeastOneThirdIsSlashable does the following steps:
                a)  Ensures the cardinality of the intersection of the two sets 
                    validators_support_conflicting_justified_checkpoint_1 and 
                    validators_support_conflicting_justified_checkpoint_1 is a least one third of validators.
                b)  Pick an arbitrary validator v in validator in the intersection of 
                    validators_support_conflicting_justified_checkpoint_1 and 
                    validators_support_conflicting_justified_checkpoint_1. 
                c)  Generates two arbitrary votes vote_1 and vote_2 from v for the justification of 
                    conflicting_justified_checkpoint_1 and conflicting_justified_checkpoint_2, respectively.
                    The construction of vote_1 and vote_2 ensures that:
                        i)  their targets are different target, and
                        ii) their targets' checkpoint slot are the same.
                d)  Checks the slashability of vote_1 and vote_2.
          
    All possible states are generated in the initial state, and all variables are not updated.
    The model checking happens on the initial state.

    The experiment with APALACHE on my laptop was done in 6 seconds .
    The experiment with TLC was not finished after 15 minutes.
 *)

EXTENDS FiniteSets, Integers, typedefs

\* @type: Int;
N == 4

\* @type: Set(Int);
VALIDATORS == 1..N

\* @type: Int;
MAX_BLOCK_SLOT == 20

\* @type: Set(Int);
BlockSlots == 0..MAX_BLOCK_SLOT

\* @type: Int;
MAX_BLOCK_BODY == 20

\* @type: Set(Int);
BlockBodies == 0..MAX_BLOCK_BODY

\* @type: Set(Int);
CheckpointSlots == 0..MAX_BLOCK_SLOT

\* @type: (Int, Int) => $block;
Block(slot, body) ==
    [
        slot |-> slot,
        body |-> body
    ]
GenesisBlock == Block(0, 0)
AllBlocks == {Block(slot, body): slot \in BlockSlots, body \in BlockBodies} 


\* @type: ($block, Int) => $checkpoint;
Checkpoint(block, checkpoint_slot) == [ chkp_block |-> block, chkp_slot |-> checkpoint_slot ]    

GenesisCheckpoint == Checkpoint(GenesisBlock, 0)
AllCheckpoints == {Checkpoint(block, i): block \in AllBlocks, i \in CheckpointSlots}

\* @type: ($checkpoint, $checkpoint) => $ffgVote;
FFGVote(source, target) == [ source |-> source, target |-> target ]

All_FFG_Votes == {FFGVote(s, t) : s \in AllCheckpoints, t \in AllCheckpoints} 

\* @type: (Int, $ffgVote) => $vote;
Vote(v, ffgVote) == [validator |-> v, ffg_vote |-> ffgVote] 

All_Votes == {Vote(v, ffgVote) : v \in VALIDATORS, ffgVote \in All_FFG_Votes} 


VARIABLES
    \* @type: $checkpoint;
    conflicting_justified_checkpoint_1,
    \* @type: $checkpoint;
    conflicting_justified_checkpoint_2,
    \* @type: Set(Int);
    validators_support_conflicting_justified_checkpoint_1,
    \* @type: Set(Int);
    validators_support_conflicting_justified_checkpoint_2



InitConflictingJustifiedheckpoint1 ==
    /\ conflicting_justified_checkpoint_1 \in AllCheckpoints

InitConflictingJustifiedheckpoint2 ==
    /\ conflicting_justified_checkpoint_2 \in AllCheckpoints

InitConditionsInCase1 ==
    /\ conflicting_justified_checkpoint_1 /= conflicting_justified_checkpoint_2
    /\ conflicting_justified_checkpoint_1.chkp_slot = conflicting_justified_checkpoint_2.chkp_slot
    
    
InitVotersFirstJustification ==
    /\ validators_support_conflicting_justified_checkpoint_1 \in SUBSET VALIDATORS
    /\ 3 * Cardinality(validators_support_conflicting_justified_checkpoint_1) >= 2 * N


InitVotersSecondJustification ==
    /\ validators_support_conflicting_justified_checkpoint_2 \in SUBSET VALIDATORS
    /\ 3 * Cardinality(validators_support_conflicting_justified_checkpoint_2) >= 2 * N
    
Init ==
    /\ InitConflictingJustifiedheckpoint1
    /\ InitConflictingJustifiedheckpoint2
    /\ InitConditionsInCase1
    /\ InitVotersFirstJustification
    /\ InitVotersSecondJustification

\* @type: ($ffgVote, $ffgVote) => Bool;
IsSlashableByE1(ffg_vote_1, ffg_vote_2) ==
    /\ ffg_vote_1 /= ffg_vote_2
    /\ ffg_vote_1.target.chkp_slot = ffg_vote_2.target.chkp_slot


    
AtLeastOneThirdIsSlashable ==
    LET voters == validators_support_conflicting_justified_checkpoint_2 \cap validators_support_conflicting_justified_checkpoint_2
    IN  /\ 3 * Cardinality(voters) >= N
        /\ \A v \in voters, vote_1 \in All_Votes, vote_2 \in All_Votes : 
            /\ vote_1.validator = v
            /\ vote_1.ffg_vote.target.chkp_slot = conflicting_justified_checkpoint_1.chkp_slot
            /\ vote_2.validator = v
            /\ vote_2.ffg_vote.target.chkp_slot = conflicting_justified_checkpoint_2.chkp_slot
            (*Just use the following assumption temporarilty*)
            /\ vote_1.ffg_vote.target.chkp_block /= vote_2.ffg_vote.target.chkp_block
            => IsSlashableByE1(vote_1.ffg_vote, vote_2.ffg_vote)


Next == UNCHANGED <<
    conflicting_justified_checkpoint_1,
    conflicting_justified_checkpoint_2,
    validators_support_conflicting_justified_checkpoint_1,
    validators_support_conflicting_justified_checkpoint_2 >>
    
    
=============================================================================
