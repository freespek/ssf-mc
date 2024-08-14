----------------------------- MODULE ffg -----------------------------
(*
 * Translation of the `ffg.py` Python module to TLA+.
 *
 * Jure Kukovec, 2024.
 *
 * Subject to Apache 2.0. See `LICENSE.md`.
 *)

EXTENDS Apalache, Integers, Sequences, helpers, typedefs

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

VARIABLES
    \* A precomputed set of all justified checkpoints.
    \* @type: Set($checkpoint);
    PRECOMPUTED__IS_JUSTIFIED_CHECKPOINT

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
    /\ PRECOMPUTED__is_ancestor_descendant_relationship(
            get_block_from_hash(vote.message.ffg_source.block_hash, node_state),
            get_block_from_hash(vote.message.ffg_target.block_hash, node_state),
            node_state
        )
    /\ vote.message.ffg_source.chkp_slot < vote.message.ffg_target.chkp_slot
    /\ has_block_hash(vote.message.ffg_source.block_hash, node_state)
    /\ get_block_from_hash(vote.message.ffg_source.block_hash, node_state).slot = vote.message.ffg_source.block_slot
    /\ has_block_hash(vote.message.ffg_target.block_hash, node_state)
    /\ get_block_from_hash(vote.message.ffg_target.block_hash, node_state).slot = vote.message.ffg_target.block_slot

\* -----------------------------------------------------------------------------
\* ffg.py contains a chain of mutually recursive functions, via
\* is_justified_checkpoint -> get_validators_in_FFG_support_of_checkpoint_justification -> filter_out_FFG_votes_not_in_FFG_support_of_checkpoint_justification -> is_FFG_vote_in_support_of_checkpoint_justification -> is_justified_checkpoint
\*
\* Below, we translate this chain of recursion to an Apalache fold application, see
\*   - [the translation rules](../Translation.md#mutual-recursion-cycles)
\*   - [the Apalache manual on folds](https://apalache.informal.systems/docs/apalache/principles/folds.html)
\*
\* For a naive translation to recursive TLA+ operators (not supported by Apalache), see `./ffg_recursive.tla`.
\* -----------------------------------------------------------------------------

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
    /\ PRECOMPUTED__is_ancestor_descendant_relationship(
        get_block_from_hash(checkpoint.block_hash, node_state),
        get_block_from_hash(vote.message.ffg_target.block_hash, node_state),
        node_state
        )
    /\ PRECOMPUTED__is_ancestor_descendant_relationship(
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
\*
\* N_i := sup( { c.chkp_slot : c \in CheckpointsPendingJustification_i } )
\*
\* (which, as a reminder, evaluates to negative infinity if the set is empty)
\* we can easily show that CheckpointsPendingJustification_i /= {} implies N_{i+1} < N_i.
\* Thus, assume CheckpointsPendingJustification_i is nonempty. Then, N_i >= 0, since it is the slot number of some
\* checkpoint, and slot numbers are nonnegative.
\* As the sets CheckpointsPendingJustification_i are finite for all i, N_{i+1} is either:
\*   - negative infinity if CheckpointsPendingJustification_{i+1} is empty, which is trivially less than N_i, or
\*   - the maximum of checkpoint slots in CheckpointsPendingJustification_{i+1}.
\* Suppose the second case holds, and c0 is one such checkpoint, for which c0.chkp_slot = N_{i+1} (may not be unique).
\* By definition, since c0 belongs to CheckpointsPendingJustification_{i+1}, there exists some c1 in CheckpointsPendingJustification_i, s.t.
\* c0 is the source of some vote in VotesInSupportAssumingJustifiedSource(c1, ...).
\* All votes in VotesInSupportAssumingJustifiedSource(c1, ..) have sources with a strictly lower slot number than c1.
\* It follows that N_{i+1} = c0.chkp_slot < c1.chkp_slot <= N_i.

\* We now have a sequence of values N_i, where the values strictly decrease, as long as they remain nonnegative.
\* We can therefore conclude, that there exists some index n (possibly 1), s.t.
\* N_k >= 0 for all k < n, and N_k = -inf for all k >= n.
\* However, observe that N_j = -inf <=> CheckpointsPendingJustification_j = {} for all j,
\* so this is the same index n we originally set out to find.

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
\* @type: ($targetMap, $commonNodeState, Int) => Seq($targetMap);
Chain(x, node_state, N) ==
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
        IN ApaFoldSeqLeft( step, <<x>>, MkSeq(N, (* @type: Int => Int; *) LAMBDA i: i) )

\* @type: ($targetMap, $commonNodeState, Int) => Set($checkpoint);
AllJustifiedCheckpoints(initialTargetMap, node_state, N) ==
    LET chain == Chain(initialTargetMap, node_state, N) IN
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
                            PRECOMPUTED__is_complete_chain(
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

\* SRC: https://github.com/saltiniroberto/ssf/blob/ad3ba2c21bc1cd554a870a6e0e4d87040558e129/high_level/common/ffg.py#L84
\* It checks whether a `checkpoint` if justified, specifically a `checkpoint` is justified if at least
\* two-thirds of the total validator set weight is in support. This is evaluated by checking if
\* `FFG_support_weight * 3 >= tot_validator_set_weight * 2`.
\* @type: ($checkpoint, $commonNodeState) => Bool;
is_justified_checkpoint(checkpoint, node_state) ==
    LET initialTargetMap == [ c \in {checkpoint} |-> VotesInSupportAssumingJustifiedSource(c, node_state) ]
    IN checkpoint \in AllJustifiedCheckpoints(initialTargetMap, node_state, MAX_SLOT)


\* A precomputed version of `is_justified_checkpoint`, to avoid emitting folds.
\* @type: ($checkpoint, $commonNodeState) => Bool;
PRECOMPUTED__is_justified_checkpoint(checkpoint, node_state) ==
    checkpoint \in PRECOMPUTED__IS_JUSTIFIED_CHECKPOINT

\* For comparison, we include the unrolled version of is_justified_checkpoint
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
                                        /\ PRECOMPUTED__is_ancestor_descendant_relationship(
                                                get_block_from_hash(checkpoint.block_hash, node_state),
                                                get_block_from_hash(vote.message.ffg_target.block_hash, node_state),
                                                node_state
                                            )
                                        /\ PRECOMPUTED__is_ancestor_descendant_relationship(
                                                get_block_from_hash(vote.message.ffg_source.block_hash, node_state),
                                                get_block_from_hash(checkpoint.block_hash, node_state),
                                                node_state)
                                        /\ PRECOMPUTED__is_justified_checkpoint(vote.message.ffg_source, node_state)
                                }
                            },
                            validatorBalances
                        )
                    tot_validator_set_weight == 
                        validator_set_weight(DOMAIN validatorBalances, validatorBalances)
                IN FFG_support_weight * 3 >= tot_validator_set_weight * 2

\* ----------------------------

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
    IF ~PRECOMPUTED__is_justified_checkpoint(checkpoint, node_state)
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
    IN filtered \union {genesis_checkpoint(node_state)}

\* SRC: https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/ffg.py#L198
\* It returns the greatest finalized checkpoint from a `node_state`.
\* @type: ($commonNodeState) => $checkpoint;
get_greatest_finalized_checkpoint(node_state) == 
    LET finCheckpoints == get_finalized_checkpoints(node_state)
    IN CHOOSE maxFinCheckpoint \in finCheckpoints: \A finCheckpoint \in finCheckpoints: (finCheckpoint.chkp_slot <= maxFinCheckpoint.chkp_slot)

=============================================================================