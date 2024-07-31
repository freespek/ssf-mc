----------------------------- MODULE MC_ffg -----------------------------
(*
 * Main TLA+ module for model-checking with Apalache
 *
 * Jure Kukovec, 2024.
 *
 * Subject to Apache 2.0. See `LICENSE.md`.
 *)

Nodes == { "A", "B", "C", "D" }

\* Model-checking: Maximum slot (inclusive) that Apalache folds over when traversing ancestors.
MAX_SLOT == 5

\* ========== Dummy implementations of stubs ==========

\* SRC: https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/stubs.pyi#L6
\*
\* Model-checking: We assume the block_body type is the string (hash) already.
\*
\* @type: ($block) => $hash;
BLOCK_HASH(b) == b.body

\* SRC: https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/stubs.pyi#L9
\*
\* Model-checking: We assume that all vote signatures are valid.
\*
\* @type: ($signedVoteMessage) => Bool;
VERIFY_VOTE_SIGNATURE(vote) == TRUE

\* SRC: https://github.com/saltiniroberto/ssf/blob/7ea6e18093d9da3154b4e396dd435549f687e6b9/high_level/common/stubs.pyi#L18
\*
\* Stake associated with each validator in a given slot.
\*
\* Model-checking: We assume uniform voting power.
\*
\* @type: ($block, Int, $commonNodeState) => $validatorBalances;
GET_VALIDATOR_SET_FOR_SLOT(block, slot, node_state) == [node \in Nodes |-> 100]

\* ====================================================

INSTANCE ffg WITH
    MAX_SLOT <- MAX_SLOT,
    BLOCK_HASH <- BLOCK_HASH,
    VERIFY_VOTE_SIGNATURE <- VERIFY_VOTE_SIGNATURE,
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
    /\ block.body /= ""

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
        body        |-> "genesis"
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
    /\ "" \notin DOMAIN node_state.view_blocks
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
\* -------------------------------------------------------------------------
\* Falsy invariants to check reachability of certain states

\* Find a complete chain HASH1 ->* genesis
CompleteChain_Example ==
    LET block == single_node_state.view_blocks["HASH1"]
    IN ~is_complete_chain(block, single_node_state)

\* Find a complete chain HASH1 ->* genesis of length >= 4
CompleteChainLong_Example ==
    LET block == single_node_state.view_blocks["HASH1"]
    IN is_complete_chain(block, single_node_state) => Size(get_blockchain(block, single_node_state)) < 4

\* Find a chain such that `ancestor` and `descendant` are in an ancestor-descendant relationship, with at least 1 other block inbetween
AncestorDescendant_Example ==
    LET
        ancestor == single_node_state.view_blocks["HASH1"]
        descendant == single_node_state.view_blocks["HASH3"]
    IN descendant.parent_hash /= "HASH1" => ~is_ancestor_descendant_relationship(ancestor, descendant, single_node_state)

\* Find a common ancestor of 2 blocks, which are not in an ancestor-descendant relationship, that is not their immediate parent
CommonAncestor_Example ==
    LET
        block1 == single_node_state.view_blocks["HASH1"]
        block2 == single_node_state.view_blocks["HASH2"]
        setup ==
            /\ ~is_ancestor_descendant_relationship(block1, block2, single_node_state)
            /\ ~is_ancestor_descendant_relationship(block2, block1, single_node_state)
            /\ block1.parent_hash /= block2.parent_hash
    IN setup => ~have_common_ancestor(block1, block2, single_node_state)

\* Find a common ancestor of 2 blocks, which are not in an ancestor-descendant relationship, that is not their immediate parent
Conflicting_Example ==
    LET
        block1 == single_node_state.view_blocks["HASH1"]
        block2 == single_node_state.view_blocks["HASH2"]
    IN have_common_ancestor(block1, block2, single_node_state) => ~are_conflicting(block1, block2, single_node_state)
Next == UNCHANGED single_node_state

\* Find a slashable node (i.e., an equivocating or surround-voting node)
SlashableNode_Example == get_slashable_nodes(single_node_state.view_votes) = {}

\* Find a (slashable) node that was not surround-voting (i.e., it was equivocating)
Equivocation_Example ==
    LET no_surrounding_votes ==
        \forall vote1, vote2 \in single_node_state.view_votes :
            /\ ~does_first_vote_surround_second_vote(vote1, vote2)
            /\ ~does_first_vote_surround_second_vote(vote2, vote1)
    IN no_surrounding_votes => SlashableNode_Example

\* Find a (slashable) node that was not equivocating (i.e., it was surround-voting)
SurroundVoting_Example ==
    LET no_equivocating_votes ==
        \forall vote1, vote2 \in single_node_state.view_votes : ~are_equivocating_votes(vote1, vote2)
    IN no_equivocating_votes => SlashableNode_Example

\* Find a validator linking to a checkpoint in the next slot (i.e., one that cast a valid FFG vote for checkpoint slots 3->4)
ValidatorsLinkingNextSlot_Example ==
    LET source_checkpoint == [ block_hash |-> "HASH1", block_slot |-> 2, chkp_slot |-> 3 ]
    IN get_validators_in_FFG_votes_linking_to_a_checkpoint_in_next_slot(source_checkpoint, single_node_state) = {}

\* Find at least 3 justifying votes for checkpoint
VotesInSupport_Example ==
    LET checkpoint == [ block_hash |-> "HASH1", block_slot |-> 2, chkp_slot |-> 3 ]
    IN Cardinality(VotesInSupportAssumingJustifiedSource(checkpoint, single_node_state)) < 3

Chain_Example ==
    LET
        checkpoint == [ block_hash |-> "HASH1", block_slot |-> 2, chkp_slot |-> 3 ]
        checkpoint_has_support == VotesInSupportAssumingJustifiedSource(checkpoint, single_node_state) /= {}
        initialTargetMap == [ c \in {checkpoint} |-> VotesInSupportAssumingJustifiedSource(c, single_node_state) ]
    IN checkpoint_has_support => Chain(initialTargetMap, single_node_state) = <<>>

Justified_Example ==
    LET
        checkpoint == [ block_hash |-> "HASH1", block_slot |-> 2, chkp_slot |-> 3 ]
        checkpoint_has_support == VotesInSupportAssumingJustifiedSource(checkpoint, single_node_state) /= {}
        initialTargetMap == [ c \in {checkpoint} |-> VotesInSupportAssumingJustifiedSource(c, single_node_state) ]
    IN checkpoint_has_support => ~is_justified_checkpoint(checkpoint, single_node_state)

\* The ebb-and-flow protocol property stipulates that at every step, two chains are maintained,
\* the finalized chain, which is safe, and the available chain, which is live, s.t. the finalized
\* chain is a prefix of the available chain.
FinalizedChainIsPrefixOfAvailableChain == 
    LET lastFinBLock == get_block_from_hash(get_greatest_finalized_checkpoint(single_node_state).block_hash, single_node_state)
    IN is_ancestor_descendant_relationship(lastFinBLock, single_node_state.chava, single_node_state)

=============================================================================