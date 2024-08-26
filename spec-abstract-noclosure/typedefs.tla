----------------------------- MODULE typedefs -----------------------------

(*
    @typeAlias: body = Str;
    @typeAlias: block = {
        slot: Int,
        body: $body
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