----------------------------- MODULE typedefs -----------------------------

(*
    @typeAlias: block = {
        slot: Int,
        body: Int
    };

    @typeAlias: checkpoint = {
        chkp_block: $block, 
        chkp_slot: Int
    };

    @typeAlias: ffgVote = {
        source: $checkpoint,
        target: $checkpoint
    };

    @typeAlias: vote = {
        validator: Int,
        ffg_vote: $ffgVote
    };
*)

TYPEDEFS == TRUE

=============================================================================