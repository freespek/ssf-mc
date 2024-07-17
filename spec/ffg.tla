----------------------------- MODULE ffg -----------------------------

EXTENDS typedefs, Apalache, Integers

VARIABLES
    \* @type: $configuration;
    configuration,
    \* @type: $nodeIdentity;
    identity,
    \* @type: Int;
    current_slot,
    \* @type: $hash -> $block;
    view_blocks,
    \* @type: Set($signedVoteMessage);
    view_votes,
    \* @type: $block;
    chava

\* Start in some arbitrary state
\* @type: () => Bool;
Init == 
    /\ configuration = Gen(4)
    /\ identity = Gen(4)
    /\ current_slot = Gen(4)
    /\ view_blocks = Gen(4)
    /\ view_votes = Gen(4)
    /\ chava = Gen(4)

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

\* SRC: https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/stubs.pyi#L9
\* stub, so we don't have access to the definition
\* @type: ($signedVoteMessage) => Bool;
verify_vote_signature(vote) == TRUE

\* SRC: https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/ffg.py#L208
\* @type: ($signedVoteMessage, $signedVoteMessage) => Bool;
are_equivocating_votes(vote1, vote2) == 
    /\ verify_vote_signature(vote1)
    /\ verify_vote_signature(vote2)
    /\ vote1.sender = vote2.sender
    /\ vote1 /= vote2
    /\ vote1.message.ffg_target.chkp_slot = vote2.message.ffg_target.chkp_slot

\* SRC: https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/ffg.py#L218
\* @type: ($signedVoteMessage, $signedVoteMessage) => Bool;
does_first_vote_surround_second_vote(vote1, vote2) == 
    /\ verify_vote_signature(vote1)
    /\ verify_vote_signature(vote2)
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
get_slashabe_nodes(vote_view) ==
    LET filtered ==
        {
            vote1 \in vote_view : \E vote2 \in vote_view: is_slashable_offence(vote1, vote2)
        }
    IN { vote.sender : vote \in filtered}

\* #mechanical
\* If we were to blindly follow translation rules, without applying human judgement, we would end up with 
\* the below implementation, which is semantically equivalent to the above, 
\* but more verbose and computationally expensive for Apalache.
\* @type: (Set($signedVoteMessage)) => Set($nodeIdentity);
get_slashabe_nodes_unoptimized(vote_view) == 
    LET filtered ==
        LET lambda1(vote1) == 
            LET S == 
                LET lambda2(vote2) == is_slashable_offence(vote1, vote2)
                IN { vote \in vote_view : lambda2(vote) }
            IN ~(S = {})
        IN { vote \in vote_view: lambda1(vote)}
    IN { vote.sender : vote \in filtered}

NextForceExistsSlashable == 
    /\ configuration' = Gen(4)
    /\ identity' = Gen(4)
    /\ current_slot' = Gen(4)
    /\ view_blocks' = Gen(4)
    /\ view_votes' = Gen(4)
    /\ get_slashabe_nodes(view_votes') /= {}
    /\ chava' = Gen(4) 

Next == NextForceExistsSlashable

=============================================================================