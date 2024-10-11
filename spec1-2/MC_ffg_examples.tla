----------------------------- MODULE MC_ffg_examples -----------------------------
(*
 * Fixed chains and falsy invariants to check reachability of certain states.
 *
 * Thomas Pani, 2024.
 *
 * Subject to Apache 2.0. See `LICENSE.md`.
 *)

EXTENDS MC_ffg

Init_SingleChain ==
    LET
        config == Gen(1)
        id == Gen(1)
        current_slot == MAX_SLOT
        view_blocks == SetAsFun({
            \* |   0    |    1    |    2    |    3    |    4    |
            \* genesis <- BLOCK1 <- BLOCK2 <- BLOCK3 <- BLOCK4
            <<"genesis", GenesisBlock>>,
            <<"BLOCK1", [ parent_hash |-> "genesis", slot |-> 1, votes |-> {}, body |-> "BLOCK1" ] >>,
            <<"BLOCK2", [ parent_hash |-> "BLOCK1", slot |-> 2, votes |-> {}, body |-> "BLOCK2" ] >>,
            <<"BLOCK3", [ parent_hash |-> "BLOCK2", slot |-> 3, votes |-> {}, body |-> "BLOCK3" ] >>,
            <<"BLOCK4", [ parent_hash |-> "BLOCK3", slot |-> 4, votes |-> {}, body |-> "BLOCK4" ] >>
        })
        view_votes == Gen(MAX_VOTES)
        chava == Gen(1)
    IN
    /\ single_node_state = [ configuration |-> config, identity |-> id, current_slot |-> current_slot, view_blocks |-> view_blocks, view_votes |-> view_votes, chava |-> chava ]
    /\ Precompute
    /\ IsValidNodeState(single_node_state)

\* Precompute for the single chain setup is correct
Inv_SingleChain_PrecomputeOK ==
    LET
        b(hash) == single_node_state.view_blocks[hash]
        bs(hashes) == { single_node_state.view_blocks[hash] : hash \in hashes }
    IN
    /\ PRECOMPUTED__IS_ANCESTOR_DESCENDANT_RELATIONSHIP = SetAsFun({
        <<b("genesis"), bs({ "genesis" })>>,
        <<b("BLOCK1"), bs({ "genesis", "BLOCK1" })>>,
        <<b("BLOCK2"), bs({ "genesis", "BLOCK1", "BLOCK2" })>>,
        <<b("BLOCK3"), bs({ "genesis", "BLOCK1", "BLOCK2", "BLOCK3" })>>,
        <<b("BLOCK4"), bs({ "genesis", "BLOCK1", "BLOCK2", "BLOCK3", "BLOCK4" })>> })

Init_Forest ==
    LET
        config == Gen(1)
        id == Gen(1)
        current_slot == MAX_SLOT
        view_blocks == SetAsFun({
            \* |   0    |    1    |    2    |    3    |    4    |
            \* genesis <- BLOCK1 <- BLOCK2 <- BLOCK3 <- BLOCK4
            \*       ^--- BLOCK5 <- BLOCK6 <- BLOCK7
            \*
            \* (... more blocks below)
            <<"genesis", GenesisBlock>>,
            <<"BLOCK1", [ parent_hash |-> "genesis", slot |-> 1, votes |-> {}, body |-> "BLOCK1" ] >>,
            <<"BLOCK2", [ parent_hash |-> "BLOCK1", slot |-> 2, votes |-> {}, body |-> "BLOCK2" ] >>,
            <<"BLOCK3", [ parent_hash |-> "BLOCK2", slot |-> 3, votes |-> {}, body |-> "BLOCK3" ] >>,
            <<"BLOCK4", [ parent_hash |-> "BLOCK3", slot |-> 4, votes |-> {}, body |-> "BLOCK4" ] >>,
            <<"BLOCK5", [ parent_hash |-> "genesis", slot |-> 1, votes |-> {}, body |-> "BLOCK5" ] >>,
            <<"BLOCK6", [ parent_hash |-> "BLOCK5", slot |-> 2, votes |-> {}, body |-> "BLOCK6" ] >>,
            <<"BLOCK7", [ parent_hash |-> "BLOCK6", slot |-> 3, votes |-> {}, body |-> "BLOCK7" ] >>,
            \*
            \* |   0    |    1    |    2    |    3    |    4    |
            \*            BLOCK8
            <<"BLOCK8", [ parent_hash |-> "not_here", slot |-> 1, votes |-> {}, body |-> "BLOCK8" ] >>,
            \*
            \* |   0    |    1    |    2    |    3    |    4    |
            \*            BLOCK9 <- BLOCK10
            <<"BLOCK9", [ parent_hash |-> "not_here", slot |-> 1, votes |-> {}, body |-> "BLOCK9" ] >>,
            <<"BLOCK10", [ parent_hash |-> "BLOCK9", slot |-> 2, votes |-> {}, body |-> "BLOCK10" ] >>
        })
        view_votes == Gen(MAX_VOTES)
        chava == Gen(1)
    IN
    /\ single_node_state = [ configuration |-> config, identity |-> id, current_slot |-> current_slot, view_blocks |-> view_blocks, view_votes |-> view_votes, chava |-> chava ]
    /\ Precompute
    /\ IsValidNodeState(single_node_state)

\* Precompute for the forest chain setup is correct
Inv_Forest_PrecomputeOK ==
    LET
        b(hash) == single_node_state.view_blocks[hash]
        bs(hashes) == { single_node_state.view_blocks[hash] : hash \in hashes }
    IN
    /\ PRECOMPUTED__IS_ANCESTOR_DESCENDANT_RELATIONSHIP = SetAsFun({
        <<b("genesis"), bs({ "genesis" })>>,
        <<b("BLOCK1"), bs({ "genesis", "BLOCK1" })>>,
        <<b("BLOCK2"), bs({ "genesis", "BLOCK1", "BLOCK2" })>>,
        <<b("BLOCK3"), bs({ "genesis", "BLOCK1", "BLOCK2", "BLOCK3" })>>,
        <<b("BLOCK4"), bs({ "genesis", "BLOCK1", "BLOCK2", "BLOCK3", "BLOCK4" })>>,
        <<b("BLOCK5"), bs({ "genesis", "BLOCK5" })>>,
        <<b("BLOCK6"), bs({ "genesis", "BLOCK5", "BLOCK6" })>>,
        <<b("BLOCK7"), bs({ "genesis", "BLOCK5", "BLOCK6", "BLOCK7" })>>,
        <<b("BLOCK8"), bs({ "BLOCK8" })>>,
        <<b("BLOCK9"), bs({ "BLOCK9" })>>,
        <<b("BLOCK10"), bs({ "BLOCK9", "BLOCK10" })>> })

Init_ShortFork ==
    LET
        config == Gen(1)
        id == Gen(1)
        current_slot == MAX_SLOT
        view_blocks == SetAsFun({
            \* |   0    |    1    |
            \* genesis <- BLOCK1
            \*       ^---.
            \*            BLOCK2
            <<"genesis", GenesisBlock>>,
            <<"BLOCK1", [ parent_hash |-> "genesis", slot |-> 1, votes |-> {}, body |-> "BLOCK1" ] >>,
            <<"BLOCK2", [ parent_hash |-> "genesis", slot |-> 1, votes |-> {}, body |-> "BLOCK2" ] >>
        })
        view_votes == Gen(MAX_VOTES)
        chava == Gen(1)
    IN
    /\ single_node_state = [ configuration |-> config, identity |-> id, current_slot |-> current_slot, view_blocks |-> view_blocks, view_votes |-> view_votes, chava |-> chava ]
    /\ Precompute
    /\ IsValidNodeState(single_node_state)

\* ============================================================================
\* Falsy invariants to check reachability of certain states.
\* ============================================================================

\* Find a complete chain BLOCK1 ->* genesis
CompleteChain_Example ==
    LET
        block == single_node_state.view_blocks["BLOCK1"]
        setup == "BLOCK1" \in DOMAIN single_node_state.view_blocks
    IN setup => ~is_complete_chain(block, single_node_state)

\* Find a complete chain BLOCK1 ->* genesis, joining all blocks
CompleteChainLong_Example ==
    LET
        block == single_node_state.view_blocks["BLOCK1"]
        setup == "BLOCK1" \in DOMAIN single_node_state.view_blocks /\ is_complete_chain(block, single_node_state)
    IN setup => Size(get_blockchain(block, single_node_state)) < MAX_SLOT+1

\* Find a chain such that `ancestor` and `descendant` are in an ancestor-descendant relationship, with at least 1 other block inbetween
AncestorDescendant_Example ==
    LET
        ancestor == single_node_state.view_blocks["BLOCK1"]
        descendant == single_node_state.view_blocks["BLOCK2"]
        setup == /\ "BLOCK1" \in DOMAIN single_node_state.view_blocks
                 /\ "BLOCK2" \in DOMAIN single_node_state.view_blocks
                 /\ descendant.parent_hash /= "BLOCK1"
    IN setup => ~is_ancestor_descendant_relationship(ancestor, descendant, single_node_state)

\* Find a common ancestor of 2 blocks, which are not in an ancestor-descendant relationship (i.e., they are conflicting), that is not their immediate parent
CommonAncestor_Example ==
    LET
        block1 == single_node_state.view_blocks["BLOCK1"]
        block2 == single_node_state.view_blocks["BLOCK2"]
        setup ==
            /\ "BLOCK1" \in DOMAIN single_node_state.view_blocks
            /\ "BLOCK2" \in DOMAIN single_node_state.view_blocks
            /\ ~is_ancestor_descendant_relationship(block1, block2, single_node_state)
            /\ ~is_ancestor_descendant_relationship(block2, block1, single_node_state)
            /\ block1.parent_hash /= block2.parent_hash
    IN setup => ~have_common_ancestor(block1, block2, single_node_state)

\* Find a chain where two blocks are conflicting, even though they have a common ancestor (i.e., there is a fork in the chain)
Conflicting_Example ==
    LET
        block1 == single_node_state.view_blocks["BLOCK1"]
        block2 == single_node_state.view_blocks["BLOCK2"]
        setup ==
            /\ "BLOCK1" \in DOMAIN single_node_state.view_blocks
            /\ "BLOCK2" \in DOMAIN single_node_state.view_blocks
            /\ have_common_ancestor(block1, block2, single_node_state)
    IN setup => ~are_conflicting(block1, block2, single_node_state)

\* Find a slashable node (i.e., an equivocating or surround-voting node)
SlashableNode_Example == get_slashable_nodes(single_node_state.view_votes) = {}

\* Find a (slashable) node that was not surround-voting (i.e., it was equivocating)
Equivocation_Example ==
    LET no_surrounding_votes ==
        \forall vote1, vote2 \in single_node_state.view_votes :
            /\ ~does_first_vote_surround_second_vote(vote1, vote2)
            /\ ~does_first_vote_surround_second_vote(vote2, vote1)
    IN no_surrounding_votes => get_slashable_nodes(single_node_state.view_votes) = {}

\* Find a (slashable) node that was not equivocating (i.e., it was surround-voting)
SurroundVoting_Example ==
    LET no_equivocating_votes ==
        \forall vote1, vote2 \in single_node_state.view_votes : ~are_equivocating_votes(vote1, vote2)
    IN no_equivocating_votes => get_slashable_nodes(single_node_state.view_votes) = {}

\* Find a validator linking to a checkpoint in the next slot (i.e., one that cast a valid FFG vote for checkpoint slots 3->4)
ValidatorsLinkingNextSlot_Example ==
    LET source_checkpoint == [ block_hash |-> "BLOCK1", block_slot |-> 1, chkp_slot |-> 2 ]
    IN get_validators_in_FFG_votes_linking_to_a_checkpoint_in_next_slot(source_checkpoint, single_node_state) = {}

\* Find at least 3 justifying votes for checkpoint (assuming their sources are justified)
VotesInSupport_Example ==
    LET
        checkpoint == [ block_hash |-> "BLOCK1", block_slot |-> 1, chkp_slot |-> 2 ]
        setup == "BLOCK1" \in DOMAIN single_node_state.view_blocks
    IN setup => Cardinality(VotesInSupportAssumingJustifiedSource(checkpoint, single_node_state)) < 3

\* Find justifying votes for a checkpoint
JustifyingVotes_Example ==
    LET
        checkpoint == [ block_hash |-> "BLOCK1", block_slot |-> 1, chkp_slot |-> 2 ]
        setup == "BLOCK1" \in DOMAIN single_node_state.view_blocks
    IN setup => ~is_justified_checkpoint(checkpoint, single_node_state)

\* Find finalizing (and justifying) votes for a checkpoint
FinalizingVotes_Example ==
    LET
        checkpoint == [ block_hash |-> "BLOCK1", block_slot |-> 1, chkp_slot |-> 2 ]
        setup == "BLOCK1" \in DOMAIN single_node_state.view_blocks
    IN setup => ~is_finalized_checkpoint(checkpoint, single_node_state)

\* Find a finalized checkpoint (in addition to the genesis checkpoint)
FinalizedCheckpoint_Example ==
    get_finalized_checkpoints(single_node_state) = { genesis_checkpoint(single_node_state) }

\* Find at least two finalized blocks (in addition to the genesis block)
FinalizedBlocks_Example ==
    LET
        finalized_checkpoints == get_finalized_checkpoints(single_node_state)
        finalized_blocks == { get_block_from_hash(checkpoint.block_hash, single_node_state) : checkpoint \in finalized_checkpoints }
    IN Cardinality(finalized_blocks) < 3

\* Find at least two conflicting finalized blocks
Finalized_And_Conflicting_Blocks_Example ==
    LET
        finalized_checkpoints == get_finalized_checkpoints(single_node_state)
        finalized_blocks == { get_block_from_hash(checkpoint.block_hash, single_node_state) : checkpoint \in finalized_checkpoints }
    IN \A block1, block2 \in finalized_blocks : ~are_conflicting(block1, block2, single_node_state)

=============================================================================