---- MODULE helpers_recursive ----

EXTENDS helpers

(*
 * Check if a block is part of a complete chain of blocks that reaches back to the genesis block.
 * 
 * For a non-recursive version for Apalache, see helpers.
 *
 * @type: ($block, $commonNodeState) => Bool;
 *)
RECURSIVE TLC_is_complete_chain(_, _)
TLC_is_complete_chain(block, node_state) ==
    IF block = node_state.configuration.genesis THEN TRUE
    ELSE IF ~has_parent(block, node_state) THEN FALSE
    ELSE TLC_is_complete_chain(get_parent(block, node_state), node_state)

(*
 * Construct a blockchain from a given block back to the genesis block.
 * Assumes that the given block is part of a complete chain.
 *
 * Requires: is_complete_chain(block, node_state)
 *
 * @type: ($block, $commonNodeState) => $list;
 *)
RECURSIVE TLC_get_blockchain(_, _)
TLC_get_blockchain(block, node_state) ==
    IF block = node_state.configuration.genesis THEN List(<< block >>)
    ELSE Concat(List(<< block >>), TLC_get_blockchain(get_parent(block, node_state), node_state))

(*
 * Determine if there is an ancestor-descendant relationship between two blocks.
 *
 * @type: ($block, $block, $commonNodeState) => Bool;
 *)
RECURSIVE TLC_is_ancestor_descendant_relationship(_, _, _)
TLC_is_ancestor_descendant_relationship(ancestor, descendant, node_state) ==
    IF ancestor = descendant THEN TRUE
    ELSE IF descendant = node_state.configuration.genesis THEN FALSE
    ELSE
        /\ has_parent(descendant, node_state)
        /\ TLC_is_ancestor_descendant_relationship(ancestor, get_parent(descendant, node_state), node_state)

(*
 * Check if two blocks have a common ancestor.
 *
 * @type: ($block, $block, $commonNodeState) => Bool;
 *)
RECURSIVE TLC_have_common_ancestor(_, _, _)
TLC_have_common_ancestor(chain1, chain2, node_state) ==
    IF TLC_is_ancestor_descendant_relationship(chain1, chain2, node_state) THEN TRUE
    ELSE IF has_parent(chain1, node_state) THEN TLC_have_common_ancestor(get_parent(chain1, node_state), chain2, node_state)
    ELSE FALSE
=====