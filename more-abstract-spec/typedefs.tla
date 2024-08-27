----------------------------- MODULE typedefs -----------------------------

(*
    @typeAlias: block = {
        slot: Int,
        body: Int
    };

    @typeAlias: checkpoint = <<$block, Int>>;

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