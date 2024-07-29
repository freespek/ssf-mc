---- MODULE justified ----

EXTENDS ffg, Sequences

\* Given a set of votes, returns all of the checkpoints, which appear as sources.
\* @type: (Set($signedVoteMessage)) => Set($checkpoint);
Sources(votes) == { vote.message.ffg_source : vote \in votes }

\* The recursion in is_justified_checkpoint is set up as follows:
\* To justify checkpoint C, we must look at all votes C1 -> C2, s.t.
\* C lies between C1 and C2 (definition below), AND C1 is justified.
\* We define the following operator, which precisely captures this condition, 
\* save for the recursive justification.
\* @type: ($signedVoteMessage, $checkpoint, $commonNodeState) => Bool;
IsVoteInSupportAssumingJustifiedSource(vote, checkpoint, node_state) ==
    \* TODO: If we end up always doing 1-state model checking, a lot of sub-checks in 
    \* valid_FFG_vote are already a part of the state validity predicate, and
    \* could be omitted here to simplify computation.
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
VotesInSupportAssumingJustifiedSource(checkpoint, node_state) == 
    { vote \in node_state.view_votes: IsVoteInSupportAssumingJustifiedSource(vote, checkpoint, node_state)}

\* In the recursive implementation, computing is_justified_checkpoint(C) for a given checkpoint C
\* requires us to look at the set of all votes in VotesInSupportAssumingJustifiedSource(C, ...)
\* which additionally have source checkpoints satisfying is_justified_checkpoint recursively.        
\* This naturally defines, for our choice of C, a set of (other) checkpoints, 
\* for which we need to be able to tell whether or not they are justified.
\* For certain checkpoints, such as for example the genesis checkpoint C_G, as well as 
\* any checkpoints which do not have any votes in support, this set is empty.

\* Each such checkpoint c pending justification requires us to look at VotesInSupportAssumingJustifiedSource(c, ...),
\* which in turn gives us another (possibly empty) set of (other) checkpoints, the justification of which needs to be evaluated.
\* We will show below that this construction necessarily terminates, but for now we note that:
\*   - in each step, we have a set of relevant checkpoints
\*   - for each of these checkpoints, we need to keep track of a set of votes potentially justifying it, 
\*     the sources of which define the checkpoints in the next step

\* Due to the above, we observe that we can define a (finite) sequence of _maps_ s.t.:
\*   - The domain of the i-th map is exactly the set of checkpoints pending justification in the i-th step
\*   - Each checkpoint in this domain maps to the set of votes used to potentially justify it

\* We assume that
\*  1. all structures appearing in the above and below sections are finite (e.g. VotesInSupportAssumingJustifiedSource always returns a finite set)
\*  2. all slot numbers appearing in blocks/checkpoints/votes are nonnegative.

\* Let CheckpointsPendingJustification_i denote the set of checkpoints for which we need to be able to evaluate justification in the i-th step
\* Initially, CheckpointsPendingJustification_1 = { C }, i.e. the original checkpoint C
\* To formalize the construction described above, CheckpointsPendingJustification_{i+1} will contain the sources of 
\* all checkpoints, used by votes in support of any of the checkpoints in CheckpointsPendingJustification_i:
\* CheckpointsPendingJustification_{i+1} ==
\*     UNION { Sources(VotesInSupportAssumingJustifiedSource(c, ...)) : c \in CheckpointsPendingJustification_i }

\* Finally, we extend this notion to a sequence of maps M_i,
\* where the domain of M_i is CheckpointsPendingJustification_i, and
\* M_i[c] is the set `VotesInSupportAssumingJustifiedSource(c, ...)`.
\*
\* Thus, the first map M_1 for C is simply [ c \in {C} |-> VotesInSupportAssumingJustifiedSource(C, ...) ].
\* Each subsequent map M_{i+1} is defined in the following way:
\* M_{i+1} ==
\*     LET CheckpointsPendingJustification == UNION { Sources(M_i[previousStepCheckpoint]): previousStepCheckpoint \in DOMAIN M_i } 
\*     IN [ checkpoint \in CheckpointsPendingJustification |-> VotesInSupportAssumingJustifiedSource(checkpoint, ...) ]
 
\* This construction is guaranteed to be finite, if we can show that there exists some n, 
\* s.t. CheckpointsPendingJustification_k is empty for all k >= n and nonempty for all k < n.

\* To do this, we first make the following observation:
\*   1. valid_FFG_vote(vote) requires `vote.message.ffg_source.chkp_slot < vote.message.ffg_target.chkp_slot`
\*   2. IsVoteInSupportAssumingJustifiedSource requires `vote.message.ffg_target.chkp_slot = checkpoint.chkp_slot`
\* Therefore, for any checkpoint c, all votes in VotesInSupportAssumingJustifiedSource(c, ..)
\* have sources with a strictly lower slot number. If we define
\* N_i := sup( { c.chkp_slot : c \in CheckpointsPendingJustification_i } )
\* (which, as a reminder, evaluates to negative infinity if the set is empty)
\* we can easily show that CheckpointsPendingJustification_i /= {} implies N_i > N_{i+1}.
\* Thus, assume CheckpointsPendingJustification_i is nonempty. Then, N_i >= 0, since it is the slot number of some 
\* checkpoint, and slot numbers are nonnegative.
\* As the sets CheckpointsPendingJustification_i are finite for all i, N_{i+1} is either:
\*   - negative infinity if CheckpointsPendingJustification_{i+1} is empty, which is trivially less than N_i, or 
\*   - the maximum of checkpoint slots in CheckpointsPendingJustification_{i+1}. 
\* Suppose the second case holds, and c0 is one such checkpoint, for which c0.chckp_slot = N_{i+1} (may not be unique).
\* By definition, since c0 belongs to CheckpointsPendingJustification_{i+1}, there exists some c1 in CheckpointsPendingJustification_i, s.t. 
\* c0 is the source of some vote in VotesInSupportAssumingJustifiedSource(c1, ...).
\* All votes in VotesInSupportAssumingJustifiedSource(c1, ..) have sources with a strictly lower slot number than c1.
\* It follows that N_{i+1} = c0.chkp_slot < c1.chkp_slot <= N_i.

\* We now have a sequence of values N_i, where the values strictly decrease, as long as they remain nonnegative.
\* We can therefore conclude, that there exists some index n (possibly 1), s.t. 
\* N_k >= 0 for all k < n, and N_k = -inf for all k >= n.
\* However, observe that N_i = -inf <=> CheckpointsPendingJustification_i = {}, 
\* so this is the same index n we originally sought out to find.

\* This satisfies our termination requirement from the recursion rule.

\* ============IMPORTANT============
\* TODO: #19
\* Instead of computing is_justified_checkpoint for a single checkpoint
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
            LET newTargets == UNION { Sources(map[target]): target \in DOMAIN map } 
            IN [ target \in newTargets |-> VotesInSupportAssumingJustifiedSource(target, node_state) ]
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
                        \* TODO: #20
                        \* Since GET_VALIDATOR_SET_FOR_SLOT is a constant operator, we could
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
                        \* TODO: #20
                        \* Since GET_VALIDATOR_SET_FOR_SLOT is a constant operator, 
                        \* validatorBalances is constant as well, we could compute it outside the iteration
                        tot_validator_set_weight == 
                            validator_set_weight(DOMAIN validatorBalances, validatorBalances)
                    IN hasBlockHash /\ isCompleteChain /\ FFG_support_weight * 3 >= tot_validator_set_weight * 2
            IN justifiedCheckpoints \union { target \in targets : isOneCheckpointJustified(target) }
    IN LET step(cumul, v) == G(v, cumul) 
    IN ApaFoldSeqLeft( step, {genesis_checkpoint(node_state)}, Tail(chain) )


\* @type: ($checkpoint, Int, $commonNodeState) => Bool;
NonrecursiveIsJustifiedCheckpoint(checkpoint, N, node_state) ==
    LET initialTargetMap == [ c \in {checkpoint} |-> VotesInSupportAssumingJustifiedSource(c, node_state) ]
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