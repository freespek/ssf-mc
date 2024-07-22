----------------------------- MODULE ffg -----------------------------

EXTENDS typedefs, Apalache, Integers, helpers

CONSTANTS
    (*
     * Checks whther the vote signature is valid.
     *
     * @type: ($signedVoteMessage) => Bool;
     *)
    VERIFY_VOTE_SIGNATURE(_),

    (*
     * TODO
     *
     * Requires(is_complete_chain(block, nodeState))
     * @type: ($block, Int, $commonNodeState) => $validatorBalances;
     *)
    GET_VALIDATOR_SET_FOR_SLOT(_,_,_)

\* ========  HELPER METHODS ========

\* Lexicographically compares (a,b) to (c,d).
\* Returns -1 if (a,b) < (c,d), 1 if (a,b) > (c,d) and 0 otherwise
\* @type: (<<Int, Int>>, <<Int, Int>>) => Int;
PairCompare(pa1, pa2) ==
    LET a == pa1[1]
        b == pa1[2]
        c == pa2[1]
        d == pa2[2]
    IN 
    IF a < c
    THEN -1
    ELSE IF a > c
         THEN 1
         ELSE IF b < d
              THEN -1
              ELSE IF b > d
                THEN 1
                ELSE 0

\* =================================

\* SRC: https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/ffg.py#L208
\* @type: ($signedVoteMessage, $signedVoteMessage) => Bool;
are_equivocating_votes(vote1, vote2) == 
    /\ VERIFY_VOTE_SIGNATURE(vote1)
    /\ VERIFY_VOTE_SIGNATURE(vote2)
    /\ vote1.sender = vote2.sender
    /\ vote1 /= vote2
    /\ vote1.message.ffg_target.chkp_slot = vote2.message.ffg_target.chkp_slot

\* SRC: https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/ffg.py#L218
\* @type: ($signedVoteMessage, $signedVoteMessage) => Bool;
does_first_vote_surround_second_vote(vote1, vote2) == 
    /\ VERIFY_VOTE_SIGNATURE(vote1)
    /\ VERIFY_VOTE_SIGNATURE(vote2)
    /\ vote1.sender = vote2.sender
    /\ LET 
        \* @type: () => <<Int, Int>>;
        pair1 == <<vote1.message.ffg_source.chkp_slot, vote1.message.ffg_source.block_slot>>
        \* @type: () => <<Int, Int>>;
        pair2 == <<vote2.message.ffg_source.chkp_slot, vote2.message.ffg_source.block_slot>>
        IN PairCompare(pair1, pair2) = -1
    /\  vote2.message.ffg_target.chkp_slot < vote1.message.ffg_target.chkp_slot

\* SRC: https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/ffg.py#L228
\* @type: ($signedVoteMessage, $signedVoteMessage) => Bool;
is_slashable_offence(vote1, vote2) == 
    \/ are_equivocating_votes(vote1, vote2)
    \/ does_first_vote_surround_second_vote(vote1, vote2)
    \/ does_first_vote_surround_second_vote(vote2, vote1)

\* SRC: https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/ffg.py#L243
\* @type: (Set($signedVoteMessage)) => Set($nodeIdentity);
get_slashable_nodes(vote_view) ==
    LET filtered ==
        {
            vote1 \in vote_view : \E vote2 \in vote_view: is_slashable_offence(vote1, vote2)
        }
    IN { vote.sender : vote \in filtered }

\* #mechanical
\* If we were to blindly follow translation rules, without applying human judgement, we would end up with 
\* the below implementation, which is semantically equivalent to the above, 
\* but more verbose and computationally expensive for Apalache.
\* @type: (Set($signedVoteMessage)) => Set($nodeIdentity);
get_slashable_nodes_unoptimized(vote_view) == 
    LET filtered ==
        LET lambda1(vote1) == 
            LET S == 
                LET lambda2(vote2) == is_slashable_offence(vote1, vote2)
                IN { vote \in vote_view : lambda2(vote) }
            IN ~(S = {})
        IN { vote \in vote_view: lambda1(vote)}
    IN { vote.sender : vote \in filtered}

\* ================================

\* SRC: https://github.com/saltiniroberto/ssf/blob/ad3ba2c21bc1cd554a870a6e0e4d87040558e129/high_level/common/ffg.py#L20
\* A FFG vote is valid if:
\*     - the sender is a validator;
\*     - `vote.message.ffg_source.block_hash` is an ancestor of `vote.message.ffg_target.block_hash`;
\*     - the checkpoint slot of `vote.message.ffg_source` is strictly less than checkpoint slot of `vote.message.ffg_target`;
\*     - the block associated with `vote.message.ffg_source.block_hash` has a slot number that matches the slot number specified in the same vote message;
\*     - the block associated with `vote.message.ffg_target.block_hash` has a slot number that matches the slot number specified in the same vote message;
\*     - the block hash associated the source exists within a validator's view of blocks; and
\*     - the block hash associated the target exists within a validator's view of blocks.
\* @type: ($signedVoteMessage, $commonNodeState) => Bool;
valid_FFG_vote(vote, node_state) ==
    /\ VERIFY_VOTE_SIGNATURE(vote)
    /\ is_validator(
            vote.sender,
            GET_VALIDATOR_SET_FOR_SLOT(
                get_block_from_hash(vote.message.head_hash, node_state), 
                vote.message.slot, 
                node_state
            )
        )
    /\ is_ancestor_descendant_relationship(
            get_block_from_hash(vote.message.ffg_source.block_hash, node_state),
            get_block_from_hash(vote.message.ffg_target.block_hash, node_state),
            node_state
        )
    /\ vote.message.ffg_source.chkp_slot < vote.message.ffg_target.chkp_slot
    /\ has_block_hash(vote.message.ffg_source.block_hash, node_state)
    /\ get_block_from_hash(vote.message.ffg_source.block_hash, node_state).slot = vote.message.ffg_source.block_slot
    /\ has_block_hash(vote.message.ffg_target.block_hash, node_state)
    /\ get_block_from_hash(vote.message.ffg_target.block_hash, node_state).slot = vote.message.ffg_target.block_slot

\* @type: ($checkpoint, $commonNodeState) => Bool;
RECURSIVE is_justified_checkpoint(_, _)

\* Apalache refuses to typecheck mutually-recursive operators, so we invent an operator with the same
\* signature as is_justified_checkpoint for typechecking is_FFG_vote_in_support_of_checkpoint_justification
\* @type: ($checkpoint, $commonNodeState) => Bool;
tc_dummy(a,b) == TRUE

\* SRC: https://github.com/saltiniroberto/ssf/blob/ad3ba2c21bc1cd554a870a6e0e4d87040558e129/high_level/common/ffg.py#L48
\* It determines whether a given `vote` supports the justification of a specified `checkpoint`.
RECURSIVE is_FFG_vote_in_support_of_checkpoint_justification(_, _, _)
\* @type: ($signedVoteMessage, $checkpoint, $commonNodeState) => Bool;
is_FFG_vote_in_support_of_checkpoint_justification(vote, checkpoint, node_state) ==
    /\ valid_FFG_vote(vote, node_state)
    /\ vote.message.ffg_target.chkp_slot = checkpoint.chkp_slot
    /\ is_ancestor_descendant_relationship(
            get_block_from_hash(checkpoint.block_hash, node_state),
            get_block_from_hash(vote.message.ffg_target.block_hash, node_state),
            node_state
        )
    /\ is_ancestor_descendant_relationship(
            get_block_from_hash(vote.message.ffg_source.block_hash, node_state),
            get_block_from_hash(checkpoint.block_hash, node_state),
            node_state)
    \* /\ is_justified_checkpoint(vote.message.ffg_source, node_state) 
    /\ tc_dummy(vote.message.ffg_source, node_state) 
    


\* SRC: https://github.com/saltiniroberto/ssf/blob/ad3ba2c21bc1cd554a870a6e0e4d87040558e129/high_level/common/ffg.py#L67
\* It filters out ffg votes that do not support the justification of a specified `checkpoint`.
RECURSIVE filter_out_FFG_votes_not_in_FFG_support_of_checkpoint_justification(_, _, _)
\* @type: (Set($signedVoteMessage), $checkpoint, $commonNodeState) => Set($signedVoteMessage);
filter_out_FFG_votes_not_in_FFG_support_of_checkpoint_justification(votes, checkpoint, node_state) ==
    {vote \in votes: is_FFG_vote_in_support_of_checkpoint_justification(vote, checkpoint, node_state)}
    

\* SRC: https://github.com/saltiniroberto/ssf/blob/ad3ba2c21bc1cd554a870a6e0e4d87040558e129/high_level/common/ffg.py#L74
\* It identifies and returns the set of validators that have cast `votes` in support of the justification of a specified `checkpoint`.
RECURSIVE get_validators_in_FFG_support_of_checkpoint_justification(_, _, _)
\* @type: (Set($signedVoteMessage), $checkpoint, $commonNodeState) => Set($nodeIdentity);
get_validators_in_FFG_support_of_checkpoint_justification(votes, checkpoint, node_state) ==
    {vote.sender : vote \in filter_out_FFG_votes_not_in_FFG_support_of_checkpoint_justification(votes, checkpoint, node_state)}

\* SRC: https://github.com/saltiniroberto/ssf/blob/ad3ba2c21bc1cd554a870a6e0e4d87040558e129/high_level/common/ffg.py#L84
\* It checks whether a `checkpoint` if justified, specifically a `checkpoint` is justified if at least
\* two-thirds of the total validator set weight is in support. This is evaluated by checking if
\* `FFG_support_weight * 3 >= tot_validator_set_weight * 2`.
\* @type: ($checkpoint, $commonNodeState) => Bool;
is_justified_checkpoint(checkpoint, node_state) ==
    IF checkpoint = genesis_checkpoint(node_state)
    THEN TRUE
    ELSE 
        LET
            hasBlockHash == has_block_hash(checkpoint.block_hash, node_state)
            isCompleteChain == 
                is_complete_chain(
                    get_block_from_hash(checkpoint.block_hash, node_state), 
                    node_state
                )
        IN 
            IF (~hasBlockHash \/ ~isCompleteChain)
            THEN FALSE
            ELSE
                LET 
                    validatorBalances == 
                        GET_VALIDATOR_SET_FOR_SLOT(
                            get_block_from_hash(checkpoint.block_hash, node_state), 
                            checkpoint.block_slot, 
                            node_state
                        )
                IN LET 
                    FFG_support_weight == 
                        validator_set_weight(
                            get_validators_in_FFG_support_of_checkpoint_justification(
                                node_state.view_votes, 
                                checkpoint, 
                                node_state
                            ), 
                            validatorBalances
                        )
                    tot_validator_set_weight == 
                        validator_set_weight(DOMAIN validatorBalances, validatorBalances)
                IN FFG_support_weight * 3 >= tot_validator_set_weight * 2


\* SRC: https://github.com/saltiniroberto/ssf/blob/ad3ba2c21bc1cd554a870a6e0e4d87040558e129/high_level/common/ffg.py#L134
\* It evaluates whether a given `vote` represents a link from a specified `checkpoint` to a checkpoint in the immediately following slot.
\* @type: ($signedVoteMessage, $checkpoint, $commonNodeState) => Bool;
is_FFG_vote_linking_to_a_checkpoint_in_next_slot(vote, checkpoint, node_state) ==
    /\ valid_FFG_vote(vote, node_state)
    /\ vote.message.ffg_source = checkpoint
    /\ vote.message.ffg_target.chkp_slot = checkpoint.chkp_slot + 1


\* SRC: https://github.com/saltiniroberto/ssf/blob/ad3ba2c21bc1cd554a870a6e0e4d87040558e129/high_level/common/ffg.py#L145
\* It filters and retains only those votes from a `node_state` that are linking to a `checkpoint` in the next slot.
\* @type: ($checkpoint, $commonNodeState) => Set($signedVoteMessage);
filter_out_FFG_vote_not_linking_to_a_checkpoint_in_next_slot(checkpoint, node_state) ==
    { vote \in node_state.view_votes : is_FFG_vote_linking_to_a_checkpoint_in_next_slot(vote, checkpoint, node_state)}

\* SRC: https://github.com/saltiniroberto/ssf/blob/ad3ba2c21bc1cd554a870a6e0e4d87040558e129/high_level/common/ffg.py#L152
\* It retrieves the identities of validators who have cast ffg votes that support linking a specified `checkpoint` to its immediate successor.
\* @type: ($checkpoint, $commonNodeState) => Set($nodeIdentity);
get_validators_in_FFG_votes_linking_to_a_checkpoint_in_next_slot(checkpoint, node_state) == 
    {vote.sender : vote \in filter_out_FFG_vote_not_linking_to_a_checkpoint_in_next_slot(checkpoint, node_state)}

\* SRC: https://github.com/saltiniroberto/ssf/blob/ad3ba2c21bc1cd554a870a6e0e4d87040558e129/high_level/common/ffg.py#L162
\* It evaluates whether a given `checkpoint` has been finalized. A `checkpoint` is considered finalized if it is justified and
\* if at least two-thirds of the total validator set's weight supports the transition from this `checkpoint` to the next. Specifically, it first checks if the `checkpoint` is justified using
\* `is_justified_checkpoint(checkpoint, node_state)`. Then it retrieves the set of validators and their balances for the slot associated with the `checkpoint`.
\* This is done through `get_validator_set_for_slot`. Then it calculates the total weight (stake) of validators who have cast votes
\* linking the `checkpoint` to the next slot, using `get_validators_in_FFG_votes_linking_to_a_checkpoint_in_next_slot` to identify these validators
\* and `validator_set_weight` to sum their stakes. Finally it checks if `FFG_support_weight * 3 >= tot_validator_set_weight * 2` to finalize `checkpoint`.
\* @type: ($checkpoint, $commonNodeState) => Bool;
is_finalized_checkpoint(checkpoint, node_state) ==
    IF ~is_justified_checkpoint(checkpoint, node_state)
    THEN FALSE
    ELSE 
        LET 
            validatorBalances == 
                GET_VALIDATOR_SET_FOR_SLOT(
                    get_block_from_hash(checkpoint.block_hash, node_state), 
                    checkpoint.block_slot, 
                    node_state
                )
        IN LET
            FFG_support_weight == 
                validator_set_weight(
                    get_validators_in_FFG_votes_linking_to_a_checkpoint_in_next_slot(checkpoint, node_state), 
                    validatorBalances
                )
            tot_validator_set_weight == 
                validator_set_weight(DOMAIN validatorBalances, validatorBalances)
        IN FFG_support_weight * 3 >= tot_validator_set_weight * 2
        
    
\* SRC: https://github.com/saltiniroberto/ssf/blob/ad3ba2c21bc1cd554a870a6e0e4d87040558e129/high_level/common/ffg.py#L181
\* @type: (Set($checkpoint), $commonNodeState) => Set($checkpoint);
filter_out_non_finalized_checkpoint(checkpoints, node_state) ==
    {checkpoint \in checkpoints: is_finalized_checkpoint(checkpoint, node_state)}

\* SRC: https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/ffg.py#L10
\* It extracts a set of ffg targets from a set of `votes`.
\* @type: (Set($signedVoteMessage)) => Set($checkpoint);
get_set_FFG_targets(votes) ==
    { vote.message.ffg_target: vote \in votes }

\* SRC: https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/ffg.py#L188
\* It retrieves from `node_state` all the checkpoints that have been finalized.
\* @type: ($commonNodeState) => Set($checkpoint); 
get_finalized_checkpoints(node_state) ==
    LET ffgTargets == get_set_FFG_targets(node_state.view_votes)
    IN LET filtered == filter_out_non_finalized_checkpoint(ffgTargets, node_state)
    IN filtered \cup {genesis_checkpoint(node_state)}


\* SRC: https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/ffg.py#L198
\* It returns the greatest finalized checkpoint from a `node_state`.
\* @type: ($commonNodeState) => $checkpoint;
get_greatest_finalized_checkpoint(node_state) == 
    LET e == get_finalized_checkpoints(node_state)
    IN CHOOSE max \in e: \A x \in e: (x.chkp_slot <= max.chkp_slot)


=============================================================================