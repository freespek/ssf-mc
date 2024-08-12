----------------------------- MODULE typedefs -----------------------------

(*
    @typeAlias: block = {
        slot: Int,
        body: Str
    };
    @typeAlias: checkpoint = <<$block, Int>>;
    @typeAlias: ffgVote = {
        source: $checkpoint,
        target: $checkpoint
    };
    @typeAlias: vote = {
        validator: Str,
        ffg_vote: $ffgVote
    };
*)
TYPEDEFS == TRUE

=============================================================================