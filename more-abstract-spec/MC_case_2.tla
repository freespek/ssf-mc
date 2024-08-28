----------------------------- MODULE MC_case_2 -----------------------------


EXTENDS FiniteSets, Integers, typedefs

\* @type: Int;
N == 4

\* @type: Set(Int);
Validators == 1..N

\* @type: Int;
MAX_BLOCK_SLOT == 20

\* @type: Set(Int);
BlockSlots == 0..MAX_BLOCK_SLOT

\* @type: Int;
MAX_BLOCK_BODY == 20

\* @type: Set(Int);
Block_Bodies == 0..MAX_BLOCK_BODY

\* @type: Set(Int);
Checkpoint_Slots == 0..MAX_BLOCK_SLOT

\* @type: (Int, Int) => $block;
Block(slot, body) ==
    [
        slot |-> slot,
        body |-> body
    ]

Genesis_Block == Block(0, 0)
All_Blocks == {Block(slot, body): slot \in BlockSlots, body \in Block_Bodies} 


\* @type: ($block, Int) => $checkpoint;
Checkpoint(block, checkpoint_slot) == [ chkp_block |-> block, chkp_slot |-> checkpoint_slot ]    

Genesis_Checkpoint == Checkpoint(Genesis_Block, 0)
All_Checkpoints == {Checkpoint(block, i): block \in All_Blocks, i \in Checkpoint_Slots}

\* @type: ($checkpoint, $checkpoint) => $ffgVote;
FFGVote(source, target) == [ source |-> source, target |-> target ]

All_FFG_Votes == {FFGVote(s, t) : s \in All_Checkpoints, t \in All_Checkpoints} 

\* @type: (Int, $ffgVote) => $vote;
Vote(v, ffgVote) == [validator |-> v, ffg_vote |-> ffgVote] 

All_Votes == {Vote(v, ffgVote) : v \in Validators, ffgVote \in All_FFG_Votes} 

\* @type: Int;
LEN_1 == 5

\* @type: Int;
LEN_2 == 5


VARIABLES
    \* @type: Int -> $checkpoint;
    chain_1,
    \* @type: Int -> $checkpoint;
    chain_2,
    \* @type: Int;
    fork_index,
    \* @type: Int;
    index_of_C_f_1,
    \* @type: $checkpoint;
    C_f_1 ,
    \* @type: Int;
    index_of_C_j_2,
    \* @type: $checkpoint;
    C_j_2

(*  1.  The first checkpoint is Genesis_Checkpoint.
    2.  Checkpoint slots are increasing.
    3.  Let i, j, and k be three indexes in a chain. 
        Let C_i, C_j, and C_k be checkpoints whose indexes are i, j, and k, respectively.
        If i < j < k and the blocks of C_i and C_k, then the blocks of C_i and C_j are the same.
    4.  A checkpoint slot is greater than its block's slot.
 *)
\* @type: (Int -> $checkpoint, Int) => Bool;
ConstraintsOnChain(chain, LEN) ==
    /\ chain[1] = Genesis_Checkpoint
    /\ \A i \in 1..(LEN - 1) : chain[i].chkp_slot <= chain[i + 1].chkp_slot
    /\ \A i, j, k \in 1..LEN : 
            /\ i < j /\ j < k 
            /\ chain[i].chkp_block = chain[k].chkp_block 
            => chain[i].chkp_block = chain[j].chkp_block
    /\ \A i \in 1..LEN : chain[i].chkp_block.slot < chain[i].chkp_slot

(* No two blocks have the same body but different block slots.
 *)
EveryBlockIsProposedOnce ==
    /\ LET all_blocks_in_two_chains == {chain_1[i].chkp_block : i \in 1..LEN_1} \cup {chain_2[i].chkp_block : i \in 1..LEN_2}
       IN \A b_1, b_2 \in all_blocks_in_two_chains : b_1.body = b_2.body => b_1.slot = b_2.slot


InitTwoConflictingChains ==
    /\ chain_1 \in [ 1..LEN_1 -> All_Checkpoints ]
    /\ chain_2 \in [ 1..LEN_2 -> All_Checkpoints ]
    /\ ConstraintsOnChain(chain_1, LEN_1)
    /\ ConstraintsOnChain(chain_2, LEN_2)
    /\ EveryBlockIsProposedOnce
    
(*  Two chains chain_1 and chain_2 have the same prefix from 1 to fork_index. *)
InitFork ==
    /\ fork_index \in Int
    /\ 1 <= fork_index
    /\ fork_index < LEN_1 - 2
    /\ fork_index < LEN_2 - 2
    /\ \A i \in 1..fork_index : chain_1[i] = chain_2[i]
    /\ \E i \in (fork_index + 1)..LEN_2 : i <= LEN_1 /\ chain_1[i] /= chain_2[i]

(*  -   C_f_1 is a checkpoint in chain_1 after fork, and we just assume C_f_1 is finalized.
    -   There exists a checkpoint C_target after C_f_1 such that C_target can become
        a target checkpoint of an FFG vote for the finalization of C_f_1. Hence,
        it implies C_target.chkp_slot = C_f_1.chkp_slot + 1.
 *)
InitFinalizedCheckpointInChain1Postfix ==
    /\ index_of_C_f_1 \in (fork_index + 1)..LEN_1
    /\ C_f_1  = chain_1[index_of_C_f_1]
    /\ \E target_index \in (index_of_C_f_1 + 1)..LEN_1 :
            chain_1[target_index].chkp_slot = C_f_1.chkp_slot + 1

(*  -   C_j_2 is a checkpoint in chain_2, and we just assume C_j_2 is justified.
    -   C_f_1.chkp_slot < C_j_2.chkp_slot
    -   The block of C_f_1 is not a prefix of the block of C_j_2.
    -   There exists a checkpoint C_target after C_j_2 such that C_target can become
        a target checkpoint of an FFG vote for the justification of C_j_2. Hence,
        it implies C_target.chkp_slot = C_j_2.chkp_slot.
 *)
InitJustifiedCheckpointInChain2 ==
    /\ index_of_C_j_2 \in 1..LEN_2
    /\ C_j_2 = chain_2[index_of_C_j_2]
    /\ C_f_1.chkp_slot < C_j_2.chkp_slot
    /\ \A i \in 1..index_of_C_j_2 : 
            chain_2[i].chkp_slot <= C_f_1 .chkp_slot
    /\ \A i \in index_of_C_j_2..LEN_1 :
            chain_1[i].chkp_block /= C_j_2.chkp_block
    /\ \E i \in index_of_C_j_2..LEN_2 :
            chain_2[i].chkp_slot = C_j_2.chkp_slot

ConstraintsInCase2 ==
    /\ InitFinalizedCheckpointInChain1Postfix
    /\ InitJustifiedCheckpointInChain2

Init ==
    /\ InitTwoConflictingChains 
    /\ InitFork
    /\ ConstraintsInCase2
 
    
=============================================================================
