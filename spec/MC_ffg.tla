----------------------------- MODULE MC_ffg -----------------------------
(*
 * Main TLA+ module for model-checking with Apalache
 *
 * Jure Kukovec, 2024.
 *
 * Subject to Apache 2.0. See `LICENSE.md`.
 *)

EXTENDS FiniteSets

Nodes == { "A", "B", "C", "D" }

\* Model-checking: Maximum slot (inclusive) that Apalache folds over when traversing ancestors.
\* Let `genesis <- b1 <- ... <- bn` be the longest chain from genesis in `view_votes`. Then `MAX_SLOT` MUST be at least `n`.
MAX_SLOT == 1

\* Model-checking: Maximum number of votes in `view_votes`.
MAX_VOTES == 12

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

VARIABLES
    \* @type: $commonNodeState;
    single_node_state,
    \* A precomputed map from (descendant) blocks to their ancestors.
    \* @type: $block -> Set($block);
    PRECOMPUTED__IS_ANCESTOR_DESCENDANT_RELATIONSHIP,
    \* A precomputed set of all justified checkpoints.
    \* @type: Set($checkpoint);
    PRECOMPUTED__IS_JUSTIFIED_CHECKPOINT

INSTANCE ffg WITH
    MAX_SLOT <- MAX_SLOT,
    BLOCK_HASH <- BLOCK_HASH,
    VERIFY_VOTE_SIGNATURE <- VERIFY_VOTE_SIGNATURE,
    GET_VALIDATOR_SET_FOR_SLOT <- GET_VALIDATOR_SET_FOR_SLOT

\* ========== Shape-requirements for state-variable fields ==========

\* Readable names for block hashes (introduced as fresh constants by Apalache). `BlockHashes` must satisfy |BlockHashes| >= |DOMAIN view_blocks|
BlockHashes == { BLOCK_HASH(GenesisBlock), "BLOCK1", "BLOCK2", "BLOCK3", "BLOCK4", "BLOCK5", "BLOCK6", "BLOCK7", "BLOCK8", "BLOCK9", "BLOCK10" }

\* QUESTION TO REVIEWERS: strict > ?
\* @type: ($configuration, $commonNodeState) => Bool;
IsValidConfiguration(cfg, node_state) ==
    /\ cfg.delta >= 0
    /\ cfg.genesis = GenesisBlock
    /\ cfg.eta >= 1
    /\ cfg.k >= 0

\* @type: ($hash -> $block, $commonNodeState) => Bool;
IsValidBlockView(view_blocks, node_state) ==
    \* Assign readable names to block hashes introduced as fresh constants by Apalache
    /\ DOMAIN node_state.view_blocks \subseteq BlockHashes
    \* The genesis block is always in the block view, it's parent hash never
    /\ BLOCK_HASH(GenesisBlock) \in DOMAIN view_blocks
    /\ view_blocks[BLOCK_HASH(GenesisBlock)] = GenesisBlock
    /\ GenesisBlock.parent_hash \notin DOMAIN view_blocks
    \* Each block must have a unique hash: H(B1) = H(B2) <=> B1 = B2
    /\ \A hash1,hash2 \in DOMAIN view_blocks:
        hash1 = hash2 <=> view_blocks[hash1] = view_blocks[hash2]

\* @type: ($commonNodeState) => Bool;
IsValidNodeState(node_state) ==
    /\ IsValidConfiguration(node_state.configuration, node_state)
    /\ node_state.identity \in Nodes
    /\ node_state.current_slot >= 0
    /\ node_state.current_slot <= MAX_SLOT
    /\ IsValidBlockView(node_state.view_blocks, node_state)


\* ==================================================================
\* State machine
\* ==================================================================

\* The following variables encode precomputed sets, to avoid emitting nested folds
Precompute ==
    LET all_blocks == get_all_blocks(single_node_state) IN
        /\ PRECOMPUTED__IS_ANCESTOR_DESCENDANT_RELATIONSHIP =
            [ descendant \in all_blocks |-> { ancestor \in all_blocks : is_ancestor_descendant_relationship(ancestor, descendant, single_node_state) } ]
        /\ LET
                ffg_sources == { vote.message.ffg_source : vote \in single_node_state.view_votes }
                ffg_targets == get_set_FFG_targets(single_node_state.view_votes)
                all_source_and_target_checkpoints == ffg_sources \union ffg_targets
                votes_in_support_assuming_justified_source ==
                    [ checkpoint \in all_source_and_target_checkpoints |-> VotesInSupportAssumingJustifiedSource(checkpoint, single_node_state) ]
                initialTargetMap ==
                    [ target \in ffg_targets |-> votes_in_support_assuming_justified_source[target] ]
           IN PRECOMPUTED__IS_JUSTIFIED_CHECKPOINT = AllJustifiedCheckpoints(initialTargetMap, single_node_state, MAX_SLOT)

\* Start in some arbitrary state
Init ==
    LET
        config == Gen(1)
        id     == Gen(1)
        current_slot == MAX_SLOT
        view_blocks  == Gen(MAX_SLOT + 1)  \* MAX_SLOT "regular" blocks + 1 for genesis (at slot 0)
        view_votes   == Gen(MAX_VOTES)
        chava  == Gen(1)
    IN
    /\ single_node_state = [ configuration |-> config, identity |-> id, current_slot |-> current_slot, view_blocks |-> view_blocks, view_votes |-> view_votes, chava |-> chava ]
    /\ Precompute
    /\ IsValidNodeState(single_node_state)

Next == UNCHANGED <<single_node_state, PRECOMPUTED__IS_ANCESTOR_DESCENDANT_RELATIONSHIP, PRECOMPUTED__IS_JUSTIFIED_CHECKPOINT>>

\* ==================================================================
\* Invariants
\* ==================================================================

\* Consistency checks on parameters
ConsistentParameters == Cardinality(BlockHashes) >= Cardinality(DOMAIN single_node_state.view_blocks)

\* Theorem 1 (Accountable safety). The finalized chain chFin_i is accountably safe, i.e.,
\* two conflicting finalized blocks imply that at least n/3 adversarial validators can be
\* detected to have violated either [slashing condition] E1 or E2.
AccountableSafety ==
    LET
        finalized_checkpoints == get_finalized_checkpoints(single_node_state)
        finalized_blocks == { get_block_from_hash(checkpoint.block_hash, single_node_state) : checkpoint \in finalized_checkpoints }
        there_are_conflicting_finalized_blocks == \E block1, block2 \in finalized_blocks : are_conflicting(block1, block2, single_node_state)
        slashable_nodes == get_slashable_nodes(single_node_state.view_votes)
    \* TODO(#33): Generalize to weighted voting power
    IN there_are_conflicting_finalized_blocks => Cardinality(slashable_nodes) * 3 >= Cardinality(Nodes)

Inv ==
    /\ ConsistentParameters
    /\ AccountableSafety

\* The ebb-and-flow protocol property stipulates that at every step, two chains are maintained,
\* the finalized chain, which is safe, and the available chain, which is live, s.t. the finalized
\* chain is a prefix of the available chain.
FinalizedChainIsPrefixOfAvailableChain == 
    LET lastFinBLock == get_block_from_hash(get_greatest_finalized_checkpoint(single_node_state).block_hash, single_node_state)
    IN is_ancestor_descendant_relationship(lastFinBLock, single_node_state.chava, single_node_state)

=============================================================================