----------------------------- MODULE typedefs -----------------------------

(*
    We model two sequences of block bodies:

    0 -> +1 -> +2 -> +3 -> +4 -> +5
             \     \     \     \
         -1 -> -2 -> -3 -> -4 -> -5

    @typeAlias: body = Int;
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