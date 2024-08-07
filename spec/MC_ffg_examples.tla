----------------------------- MODULE MC_ffg_examples -----------------------------
(*
 * Falsy invariants to check reachability of certain states
 *
 * Thomas Pani, 2024.
 *
 * Subject to Apache 2.0. See `LICENSE.md`.
 *)

EXTENDS MC_ffg

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
    LET source_checkpoint == [ block_hash |-> "BLOCK1", block_slot |-> 2, chkp_slot |-> 3 ]
    IN get_validators_in_FFG_votes_linking_to_a_checkpoint_in_next_slot(source_checkpoint, single_node_state) = {}

\* Find at least 3 justifying votes for checkpoint (assuming their sources are justified)
VotesInSupport_Example ==
    LET
        checkpoint == [ block_hash |-> "BLOCK1", block_slot |-> 2, chkp_slot |-> 3 ]
        setup == "BLOCK1" \in DOMAIN single_node_state.view_blocks
    IN setup => Cardinality(VotesInSupportAssumingJustifiedSource(checkpoint, single_node_state)) < 3

\* Find justifying votes for a checkpoint
JustifiedCheckpoint_Example ==
    LET
        checkpoint == [ block_hash |-> "BLOCK1", block_slot |-> 2, chkp_slot |-> 3 ]
        setup == "BLOCK1" \in DOMAIN single_node_state.view_blocks
    IN setup => ~is_justified_checkpoint(checkpoint, single_node_state)

\* Find finalizing (and justifying) votes for a checkpoint
FinalizedCheckpoint_Example ==
    LET
        checkpoint == [ block_hash |-> "BLOCK1", block_slot |-> 2, chkp_slot |-> 3 ]
        setup == "BLOCK1" \in DOMAIN single_node_state.view_blocks
    IN setup => ~is_finalized_checkpoint(checkpoint, single_node_state)

=============================================================================