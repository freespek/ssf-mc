----------------------------- MODULE typedefs -----------------------------
(*
 * Translation of the `data_structures.py` Python module to TLA+.
 *
 * In particular, we translate the class definitions to types in Apalache's Type System 1.2:
 * https://apalache.informal.systems/docs/adr/002adr-types.html#ts12
 *
 * Thomas Pani, 2024.
 *
 * Subject to Apache 2.0. See `LICENSE.md`.
 *)

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
    @typeAlias: blockBody = Str;
    @typeAlias: block = {
        parent_hash: $hash,
        slot: Int,
        votes: Set($signedVoteMessage),
        body: $blockBody
    };
    @typeAlias: listOfSignedVoteMessage = { es: Seq($signedVoteMessage) };
    @typeAlias: proposeMessage = {
        block: $block,
        proposer_view: $listOfSignedVoteMessage
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