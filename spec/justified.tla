---- MODULE justified ----

EXTENDS ffg, Sequences

\* Given a set of votes, returns all of the checkpoints, which appear as sources.
\* @type: (Set($signedVoteMessage)) => Set($checkpoint);
Sources(votes) == { vote.message.ffg_source : vote \in votes} 

\* The recursion in is_justified_checkpoint is set up as follows:
\* To justify checkpoint C, we must look at all votes C1 -> C2, s.t.
\* C lies between C1 and C2 (definition below), AND C1 is justified.
\* We define the following operator, which precisely captures this condition, 
\* save for the recursive justificaiton.
\* @type: ($signedVoteMessage, $checkpoint, $commonNodeState) => Bool;
IsVoteInSupportAssumingJustifiedSource(vote, checkpoint, node_state) ==
    \* TODO: If we end up always doing 1-state model checking, a lot of sub-checks in 
    \* valid_FFG_vote are already a part of the state validity predicate, and couldbe omitted here 
    \* to simplify computation
    /\ valid_FFG_vote(vote, node_state) 
    /\ vote.message.ffg_target.chkp_slot = checkpoint.chkp_slot
    \* TODO: If we end up always doing 1-state model checking, we could 
    \* precompute the relation is_ancestor_descendant_relationship(a,b), for all blocks
    \* ahead of time as a _function_, s.t. this lookup here becomes a simple access, instead of each of them being
    \* another pseudo-recursive computation
    /\ is_ancestor_descendant_relationship(
        get_block_from_hash(checkpoint.block_hash, node_state),
        get_block_from_hash(vote.message.ffg_target.block_hash, node_state),
        node_state
        )
    /\ is_ancestor_descendant_relationship(
        get_block_from_hash(vote.message.ffg_source.block_hash, node_state),
        get_block_from_hash(checkpoint.block_hash, node_state),
        node_state
        )

\* With the predicate, we can filter out the votes that are relevant in one step
\* @type: ($checkpoint, $commonNodeState) => Set($signedVoteMessage);
VotesRelevantForOneStepIteration(checkpoint, node_state) == 
    { vote \in node_state.view_votes: IsVoteInSupportAssumingJustifiedSource(vote, checkpoint, node_state)}

\* Using VotesRelevantForOneStepIteration, we can define, for every initial checkpoint C, 
\* a sequence of maps M_i. We will refer to the domain elements of M_i as "targets" for step i.
\* The first map M_1 for C is simply [ c \in {C} |-> VotesRelevantForOneStepIteration(C, ...) ].
\* Each subsequent map M_{i+1} is defined in the following way:
\* M_{i+1} ==
\*     LET newTargets == UNION { Sources(M_i[target]): target \in DOMAIN M_i } 
\*     IN [ target \in newTargets |-> VotesRelevantForOneStepIteration(target, ...) ]
 
\* This construction is guaranteed to be finite, i.e., there exists some n, s.t. M_k is empty for all k >= n and nonempty
\* for all 1 < i < n. The reason is as follows:
\*   1. valid_FFG_vote(vote) requires `vote.message.ffg_source.chkp_slot < vote.message.ffg_target.chkp_slot`
\*   2. IsVoteInSupportAssumingJustifiedSource requires `vote.message.ffg_target.chkp_slot = checkpoint.chkp_slot`
\* Therefore, for any checkpoint C, all votes in VotesRelevantForOneStepIteration(C, ..)
\* have sources with a strictly lower slot number. 
\* If we take N_i to be the maximal slot number of any sorce of a vote in a set in the codomain of M_i, then
\* we can easily see that N_i > N_{i+1}.
\* Since the checkpoint with the lowest slot number is the genesis checkpoint C_G, and 
\* VotesRelevantForOneStepIteration(C_G, ...) = {}, eventually S_m will be empty.

\* This satisfies our termination requirement from the recursion rule.

\* ============IMPORTANT============
\* TODO: Instead of computing is_justified_checkpoint for a single checkpoint
\* we should directly define the set of _ALL_ justified checkpoints for a given state
\* (which can be justified by all the votes in that state)
\* =================================

\* Using the above knowledge, we can construct a Chain operator, to compute the sequence <<M_n, ..., M_1>>,
\* as required by the recursion rule.

\* @typeAlias: targetMap = $checkpoint -> Set($signedVoteMessage);
\* @type: ($targetMap, Int, $commonNodeState) => Seq($targetMap);
Chain(x, N, node_state) ==
    LET 
        \* @type: ($targetMap) => Bool;
        P(map) == DOMAIN map = {}
        \* if x = M_i, then b(x) defines M_{i+1}
        \* @type: ($targetMap) => $targetMap;
        b(map) ==
            LET newTargets == UNION { Sources(x[target]): target \in DOMAIN map } 
            IN [ target \in newTargets |-> VotesRelevantForOneStepIteration(target, node_state) ]
    IN  LET 
            \* @type: (Seq($targetMap), Int) => Seq($targetMap);
            step(seq, i) == 
                IF P(seq[1])
                THEN seq
                ELSE <<b(seq[1])>> \o seq \* Alternatively, we can append here and reverse the list at the end
        IN ApaFoldSeqLeft( step, <<x>>, MkSeq(N, LAMBDA i: i) )
        

\* @type: ($targetMap, Int, $commonNodeState) => Set($checkpoint);
AllJustifiedCheckpoints(initialTargetMap, N, node_state) ==
    LET chain == Chain(initialTargetMap, N, node_state) IN
    LET 
        \* @type: ($targetMap, Set($checkpoint)) => Set($checkpoint);
        G(currentTargetMap, justifiedCheckpoints) ==
            LET targets == DOMAIN currentTargetMap IN
            \* We define the justification filter for one checkpoint, which
            \* looks at the currently computed set of justifiedCheckpoints
            \* instead of recursing
            LET 
                \* @type: ($checkpoint) => Bool;
                isOneCheckpointJustified(checkpoint) ==
                    LET
                        \* TODO: If we end up always doing 1-state model checking, these two are
                        \* implied by the sate validity predicate and can be omitted
                        hasBlockHash == has_block_hash(checkpoint.block_hash, node_state)
                        isCompleteChain == 
                            is_complete_chain(
                                get_block_from_hash(checkpoint.block_hash, node_state), 
                                node_state
                            )
                    IN  LET 
                        \* TODO: Since GET_VALIDATOR_SET_FOR_SLOT is a constant operator, we could
                        \* directly substitute it here
                        validatorBalances == 
                            GET_VALIDATOR_SET_FOR_SLOT(
                                get_block_from_hash(checkpoint.block_hash, node_state), 
                                checkpoint.block_slot, 
                                node_state
                            )
                    IN LET 
                        FFG_support_weight == 
                            validator_set_weight(
                                {
                                    \* Instead of recursion, we take the 
                                    \* votes relevant for this target, and filter them by known justified  sources
                                    filtered_vote.sender : filtered_vote \in  {
                                        vote \in currentTargetMap[checkpoint] : 
                                            vote.message.ffg_source \in justifiedCheckpoints
                                    }
                                },
                                validatorBalances
                            )
                        \* TODO: This value does not depend on any checkpoint or set of votes, so it is 
                        \* constant throughout the iteration, assuming validatorBalances is constant as decribed above
                        tot_validator_set_weight == 
                            validator_set_weight(DOMAIN validatorBalances, validatorBalances)
                    IN FFG_support_weight * 3 >= tot_validator_set_weight * 2
            IN justifiedCheckpoints \union { target \in targets : isOneCheckpointJustified(target) }
    IN LET step(cumul, v) == G(v, cumul) 
    IN ApaFoldSeqLeft( step, {genesis_checkpoint(node_state)}, Tail(chain) )


\* @type: ($checkpoint, Int, $commonNodeState) => Bool;
NonrecursiveIsJustifiedCheckpoint(checkpoint, N, node_state) ==
    LET initialTargetMap == [ c \in {checkpoint} |-> VotesRelevantForOneStepIteration(c, node_state) ]
    IN checkpoint \in AllJustifiedCheckpoints(initialTargetMap, N, node_state)


\* =========================================

\* For comparison, we include the unrolled version of is_justified_checkpoint

\* SRC: https://github.com/saltiniroberto/ssf/blob/ad3ba2c21bc1cd554a870a6e0e4d87040558e129/high_level/common/ffg.py#L84
\* It checks whether a `checkpoint` if justified, specifically a `checkpoint` is justified if at least
\* two-thirds of the total validator set weight is in support. This is evaluated by checking if
\* `FFG_support_weight * 3 >= tot_validator_set_weight * 2`.
RECURSIVE is_justified_checkpoint_unrolled(_, _)
\* @type: ($checkpoint, $commonNodeState) => Bool;
is_justified_checkpoint_unrolled(checkpoint, node_state) ==
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
                            {
                                filtered_vote.sender : filtered_vote \in  {
                                    vote \in node_state.view_votes: 
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
                                        /\ is_justified_checkpoint(vote.message.ffg_source, node_state) 
                                }
                            },
                            validatorBalances
                        )
                    tot_validator_set_weight == 
                        validator_set_weight(DOMAIN validatorBalances, validatorBalances)
                IN FFG_support_weight * 3 >= tot_validator_set_weight * 2

=====