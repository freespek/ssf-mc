----------------------------- MODULE typedefs -----------------------------

EXTENDS Lists

(*
    @typeAlias: hash = Str;
    @typeAlias: signature = SIGNATURE;
    @typeAlias: nodeIdentity = Str;
    @typeAlias: validatorBalances = $nodeIdentity -> Int;
    @typeAlias: checkpoint = {
        block_hash: $hash,
        chkp_slot: Int,
        block_slot: Int
    };
    @typeAlias: voteMessage = {
        slot: Int,
        head_hash: $hash,
        ffg_source: $checkpoint,
        ffg_target: $checkpoint
    };
    @typeAlias: signedVoteMessage = {
        message: $voteMessage,
        signature: $signature,
        sender: $nodeIdentity
    };
    @typeAlias: blockBody = BLOCK_BODY;
    @typeAlias: block = {
        parent_hash: $hash,
        slot: Int,
        votes: Set($signedVoteMessage),
        body: $blockBody
    };
    @typeAlias: proposeMessage = {
        block: $block,
        proposer_view: $list
    };
    @typeAlias: signedProposeMessage = {
        message: $proposeMessage,
        signature: $signature
    };
    @typeAlias: nodePhase = NODE_PHASE;
    @typeAlias: configuration = {
        delta: Int,
        genesis: $block,
        eta: Int,
        k: Int
    };
    @typeAlias: commonNodeState = {
        configuration: $configuration,
        identity: $nodeIdentity,
        current_slot: Int,
        view_blocks: $hash -> $block,
        view_votes: Set($signedVoteMessage),
        chava: $block
    };
    @typeAlias: blockView = $hash -> $block;
*)
typedefs_aliases == TRUE

\* @type: $nodePhase;
PROPOSE == "PROPOSE_OF_NODE_PHASE"
\* @type: $nodePhase;
VOTE == "VOTE_OF_NODE_PHASE"
\* @type: $nodePhase;
CONFIRM == "CONFIRM_OF_NODE_PHASE"
\* @type: $nodePhase;
MERGE == "MERGE_OF_NODE_PHASE"

=============================================================================