----------------------------- MODULE MC_ffg -----------------------------

Nodes == { "A", "B", "C", "D"}
MAX_SLOT == 5

\* ========== Dummy implementations of stubs ==========

\* SRC: https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/stubs.pyi#L6
\* We assume the block_body type is the string (hash) already.
\* @type: ($block) => $hash;
BLOCK_HASH(b) == b.body

\* SRC: https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/stubs.pyi#L9
\* @type: ($signedVoteMessage) => Bool;
VERIFY_VOTE_SIGNATURE(vote) == TRUE


\* Stake associated with each validator in a given slot.
\*
\* Assume uniform voting power for model checking.
\*
\* @type: ($block, Int, $commonNodeState) => $validatorBalances;
GET_VALIDATOR_SET_FOR_SLOT(block, slot, node_state) == [node \in Nodes |-> 100]

\* ====================================================

INSTANCE ffg WITH
    BLOCK_HASH <- BLOCK_HASH,
    VERIFY_VOTE_SIGNATURE <- VERIFY_VOTE_SIGNATURE,
    MAX_SLOT <- MAX_SLOT,
    GET_VALIDATOR_SET_FOR_SLOT <- GET_VALIDATOR_SET_FOR_SLOT

VARIABLES
    \* @type: $commonNodeState;
    single_node_state

\* ========== Shape-requirements for state-variable fields ==========

\* @type: ($checkpoint, $commonNodeState) => Bool;
IsValidCheckpoint(c, node_state) ==
    /\ c.block_hash \in DOMAIN node_state.view_blocks
    \* Section 3.Checkpoints: "Importantly, the slot c for the checkpoint occurs after the slot B.p where the block was proposed"
    /\ c.block_slot >= 0
    /\ c.chkp_slot > c.block_slot 
    /\ c.chkp_slot <= MAX_SLOT

\* @type: ($voteMessage, $commonNodeState) => Bool;
IsValidVoteMessage(msg, node_state) ==
    /\ msg.slot >= 0
    /\ msg.slot <= MAX_SLOT
    \* A message can only reference checkpoints that have already happened
    \* QUESTION TO REVIEWERS: strict > ?
    /\ msg.slot >= msg.ffg_source.chkp_slot
    /\ msg.slot >= msg.ffg_target.chkp_slot
    /\ IsValidCheckpoint(msg.ffg_source, node_state)
    /\ IsValidCheckpoint(msg.ffg_target, node_state)
    \* Section 3.Votes: "... C1 and C2 are checkpoints with C1.c < C2.c and C1.B <- C2.B"
    /\ msg.ffg_source.chkp_slot < msg.ffg_target.chkp_slot
    \* TODO: MAJOR source of slowdown as MAX_SLOT increases, investigate further
    /\ is_ancestor_descendant_relationship(
        get_block_from_hash(msg.ffg_source.block_hash, node_state), 
        get_block_from_hash(msg.ffg_target.block_hash, node_state),
        node_state
        )

\* @type: ($signedVoteMessage, $commonNodeState) => Bool;
IsValidSigedVoteMessage(msg, node_state) ==
    /\ IsValidVoteMessage(msg.message, node_state)
    /\ VERIFY_VOTE_SIGNATURE(msg)
    /\ msg.sender \in Nodes

\* @type: ($block, $commonNodeState) => Bool;
IsValidBlock(block, node_state) == 
    /\ block.parent_hash \in (DOMAIN node_state.view_blocks \union {""}) \* Parent of genesis = ""
    /\ block.slot >= 0
    /\ block.slot <= MAX_SLOT
    /\ \A voteMsg \in block.votes: IsValidSigedVoteMessage(voteMsg, node_state)
    /\ LET parent == get_block_from_hash(block.parent_hash, node_state)
       IN parent.slot < block.slot \* Parent has lower slot #

\* @type: ($proposeMessage, $commonNodeState) => Bool;
IsValidProposeMessage(msg, node_state) ==
    /\ IsValidBlock(msg.block, node_state)
    /\ \A i \in Indices(msg.proposer_view): IsValidSigedVoteMessage(At(msg.proposer_view, i), node_state)

\* @type: ($signedProposeMessage, $commonNodeState) => Bool;
IsValidSignedProposeMessage(msg, node_state) ==
    /\ IsValidProposeMessage(msg.message, node_state)
    \* there's no equivalent to verify_vote_signature for propose messages

\* @type: $block;
GenesisBlock == [
        parent_hash |-> "",
        slot        |-> 0,
        votes       |-> {},
        body        |-> ""
    ]
    
\* QUESTION TO REVIEWERS: strict > ?
\* @type: ($configuration, $commonNodeState) => Bool;
IsValidConfiguration(cfg, node_state) ==
    /\ cfg.delta >= 0
    /\ cfg.genesis = GenesisBlock
    /\ cfg.eta >= 1
    /\ cfg.k >= 0

\* @type: ($commonNodeState) => Bool;
IsValidNodeState(node_state) ==
    /\ IsValidConfiguration(node_state.configuration, node_state)
    /\ node_state.identity \in Nodes
    /\ node_state.current_slot >= 0
    /\ node_state.current_slot <= MAX_SLOT
    \* Each block must have a unique hash: H(B1) = H(B2) <=> B1 = B2
    /\ \A hash1,hash2 \in DOMAIN node_state.view_blocks: 
        hash1 = hash2 <=> node_state.view_blocks[hash1] = node_state.view_blocks[hash2]
    /\ \A msg \in node_state.view_votes: IsValidSigedVoteMessage(msg, node_state)
    /\ IsValidBlock(node_state.chava, node_state)

\* ==================================================================


\* Start in some arbitrary state
\* @type: () => Bool;
Init == 
    /\ single_node_state = Gen(5)
    /\ IsValidNodeState(single_node_state)

Next == UNCHANGED single_node_state

NoSlashableInv == get_slashable_nodes(single_node_state.view_votes) = {}

\* The ebb-and-flow protocol property stipulates that at every step, two chains are maintained,
\* the finalized chain, which is safe, and the available chain, which is live, s.t. the finalized
\* chain is a prefix of the available chain.
FinalizedChainIsPrefixOfAvailableChain == 
    LET lastFinBLock == get_block_from_hash(get_greatest_finalized_checkpoint(single_node_state).block_hash, single_node_state)
    IN is_ancestor_descendant_relationship(lastFinBLock, single_node_state.chava)

Inv == NoSlashableInv


=============================================================================