----------------------------- MODULE MC_plausible_ffg_4 -----------------------------

\* @type: Int;
N == 4

\* @type: Int;
MAX_BLOCK_SLOT == 7

\* @type: Int;
MAX_BLOCK_BODY == 7

\* @type: Int;
NUMBER_OF_CHECKPOINTS == 12

\* @type: Int;
LEN_1 == 4

\* @type: Int;
LEN_2 == 3

VARIABLES
    \* @type: Int -> $block;
    chain_1,
    \* @type: Int -> $block;
    chain_2,
    \* @type: Set($checkpoint);
    set_of_checkpoints,
    \* @type: Int;
    last_idx_in_shared_prefix,
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
    
INSTANCE plausible_ffg




=============================================================================
