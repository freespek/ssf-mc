---- MODULE ffg_recursive ----

EXTENDS ffg

\* @type: ($checkpoint, $commonNodeState) => Bool;
RECURSIVE is_justified_checkpoint_TLC(_, _)

\* SRC: https://github.com/saltiniroberto/ssf/blob/ad3ba2c21bc1cd554a870a6e0e4d87040558e129/high_level/common/ffg.py#L48
\* It determines whether a given `vote` supports the justification of a specified `checkpoint`.
RECURSIVE is_FFG_vote_in_support_of_checkpoint_justification_TLC(_, _, _)
\* @type: ($signedVoteMessage, $checkpoint, $commonNodeState) => Bool;
is_FFG_vote_in_support_of_checkpoint_justification_TLC(vote, checkpoint, node_state) ==
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
    \* Apalache refuses to typecheck mutually-recursive operators, so we apply the non-recursive operator from `ffg` here.
    /\ is_justified_checkpoint(vote.message.ffg_source, node_state) 

\* SRC: https://github.com/saltiniroberto/ssf/blob/ad3ba2c21bc1cd554a870a6e0e4d87040558e129/high_level/common/ffg.py#L67
\* It filters out ffg votes that do not support the justification of a specified `checkpoint`.
RECURSIVE filter_out_FFG_votes_not_in_FFG_support_of_checkpoint_justification_TLC(_, _, _)
\* @type: (Set($signedVoteMessage), $checkpoint, $commonNodeState) => Set($signedVoteMessage);
filter_out_FFG_votes_not_in_FFG_support_of_checkpoint_justification_TLC(votes, checkpoint, node_state) ==
    {vote \in votes: is_FFG_vote_in_support_of_checkpoint_justification_TLC(vote, checkpoint, node_state)}

\* SRC: https://github.com/saltiniroberto/ssf/blob/ad3ba2c21bc1cd554a870a6e0e4d87040558e129/high_level/common/ffg.py#L74
\* It identifies and returns the set of validators that have cast `votes` in support of the justification of a specified `checkpoint`.
RECURSIVE get_validators_in_FFG_support_of_checkpoint_justification_TLC(_, _, _)
\* @type: (Set($signedVoteMessage), $checkpoint, $commonNodeState) => Set($nodeIdentity);
get_validators_in_FFG_support_of_checkpoint_justification_TLC(votes, checkpoint, node_state) ==
    {vote.sender : vote \in filter_out_FFG_votes_not_in_FFG_support_of_checkpoint_justification_TLC(votes, checkpoint, node_state)}

\* SRC: https://github.com/saltiniroberto/ssf/blob/ad3ba2c21bc1cd554a870a6e0e4d87040558e129/high_level/common/ffg.py#L84
\* It checks whether a `checkpoint` if justified, specifically a `checkpoint` is justified if at least
\* two-thirds of the total validator set weight is in support. This is evaluated by checking if
\* `FFG_support_weight * 3 >= tot_validator_set_weight * 2`.
\* @type: ($checkpoint, $commonNodeState) => Bool;
is_justified_checkpoint_TLC(checkpoint, node_state) ==
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
                            get_validators_in_FFG_support_of_checkpoint_justification_TLC(
                                node_state.view_votes, 
                                checkpoint, 
                                node_state
                            ), 
                            validatorBalances
                        )
                    tot_validator_set_weight == 
                        validator_set_weight(DOMAIN validatorBalances, validatorBalances)
                IN FFG_support_weight * 3 >= tot_validator_set_weight * 2

========