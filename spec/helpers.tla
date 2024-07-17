---- MODULE helpers ----

EXTENDS typedefs, Apalache, Integers

CONSTANT
    (* Hash a block
     *
     * @type: $block => $hash;
     *)
    BLOCK_HASH(_)

(*
 * The last element of a list.
 *
 * @type: $list => a;
 *)
Last(lst) == At(lst, (Size(lst) - 1))

(*
 * Checkpoint for the genesis block.
 * 
 * @type: $commonNodeState => $checkpoint;
 *)
genesis_checkpoint(node_state) ==
    [ block_hash |-> BLOCK_HASH(node_state.configuration.genesis), chkp_slot |-> 0, block_slot |-> 0 ]

(*
 * Check if a block hash is present in a node state.
 * 
 * @type: ($hash,  $commonNodeState) => Bool;
 *)
has_block_hash(block_hash, node_state) ==
    block_hash \in DOMAIN node_state.view_blocks

(*
 * Get the block associated with a block hash.
 *
 * Requires: has_block_hash(block_hash, node_state)
 * 
 * @type: ($hash, $commonNodeState) => $block;
 *)
get_block_from_hash(block_hash, node_state) ==
    node_state.view_blocks[block_hash]

(*
 * Check if a block has a parent.
 * 
 * @type: ($block, $commonNodeState) => Bool;
 *)
has_parent(block, node_state) ==
    has_block_hash(block.parent_hash, node_state)

(*
 * Get the parent of a block.
 *
 * Requires: has_parent(block, node_state)
 * 
 * @type: ($block, $commonNodeState) => $block;
 *)
get_parent(block, node_state) ==
    get_block_from_hash(block.parent_hash, node_state)

(*
 * Get all the blocks in a node state.
 * 
 * @type: $commonNodeState => Set($block);
 *)
get_all_blocks(node_state) ==
    { node_state.view_blocks[hash] : hash \in DOMAIN node_state.view_blocks }

(*
 * Check if a block is part of a complete chain of blocks that reaches back to the genesis block.
 * 
 * For a non-recursive version for Apalache, see below.
 *
 * @type: ($block, $commonNodeState) => Bool;
 *)
RECURSIVE TLC_is_complete_chain(_, _)
TLC_is_complete_chain(block, node_state) ==
    IF block = node_state.configuration.genesis THEN TRUE
    ELSE IF ~has_parent(block, node_state) THEN FALSE
    ELSE TLC_is_complete_chain(get_parent(block, node_state), node_state)

(*
 * Check if a node is a validator.
 * 
 * @type: ($nodeIdentity, $validatorBalances) => Bool;
 *)
is_validator(node, validatorBalances) ==
    node \in DOMAIN validatorBalances

(*
 * Get the total weight (sum of `validatorBalances`) of a set of validators.
 *
 * @type: (Set($nodeIdentity), $validatorBalances) => Int;
 *)
validator_set_weight(validators, validatorBalances) ==
    LET queried_validator_ids == validators \intersect (DOMAIN validatorBalances) IN
    LET queried_validator_balances == { validatorBalances[v] : v \in queried_validator_ids } IN
    ApaFoldSet(+, 0, queried_validator_balances)

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
 * Construct a blockchain from a given block back to the genesis block.
 *
 * Non-recursive version for Apalache.
 *
 * Assumes that the given block is part of a complete chain.
 * Assumes that for all blocks, `get_parent(block, node_state).slot < block.slot`.
 *
 * @typeAlias: listOfBlocks = { es: Seq($block) };
 * @type: ($block, $commonNodeState) => $listOfBlocks;
 *)
get_blockchain(block, node_state) ==
    LET \* @type: (<<$block, $listOfBlocks>>, Int) => <<$block, $listOfBlocks>>; 
    ChainWithParent(last_block_and_chain_upto_slot, slot) ==
        LET last_block == last_block_and_chain_upto_slot[1] IN
        LET chain_upto_slot == last_block_and_chain_upto_slot[2] IN
        IF last_block = node_state.configuration.genesis \/ ~has_parent(last_block, node_state) THEN
            last_block_and_chain_upto_slot
        ELSE
            LET parent == get_parent(last_block, node_state) IN
            << parent, Push(chain_upto_slot, parent) >>
    IN
    ApaFoldSet( ChainWithParent, <<block, List(<< block >>)>>, 0..node_state.current_slot )[2]

\* @type: ($block, $commonNodeState) => Bool;
is_complete_chain(block, node_state) ==
    Last(TLC_get_blockchain(block, node_state)) = node_state.configuration.genesis

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
 * Determine if there is an ancestor-descendant relationship between two blocks.
 * Non-recursive version for Apalache.
 *
 * Assumes that for all blocks, `get_parent(block, node_state).slot < block.slot`.
 *
 * @type: ($block, $block, $commonNodeState) => Bool;
 *)
is_ancestor_descendant_relationship(ancestor, descendant, node_state) ==
    LET \* @type: (<<$block, Bool>>, Int) => <<$block, Bool>>; 
    FindAncestor(last_block_and_flag, slot) ==
        LET last_block == last_block_and_flag[1] IN
        LET flag == last_block_and_flag[2] IN
        IF last_block = ancestor \/ flag THEN << last_block, TRUE >>
        ELSE IF last_block = node_state.configuration.genesis \/ ~has_parent(last_block, node_state) THEN << last_block, FALSE >>
        ELSE << get_parent(last_block, node_state), FALSE >>
    IN
    ApaFoldSet( FindAncestor, << descendant, FALSE >>, 0..node_state.current_slot )[2]

(*
 * Filter blocks, retaining only those that are ancestors of a specified block.
 *
 * @type: ($block, Set($block), $commonNodeState) => Set($block);
 *)
filter_out_blocks_non_ancestor_of_block(block, blocks, node_state) ==
    { b \in blocks: is_ancestor_descendant_relationship(b, block, node_state) }

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

(*
 * Check if two blocks have a common ancestor.
 * Non-recursive version for Apalache.
 *
 * Assumes that for all blocks, `get_parent(block, node_state).slot < block.slot`.
 *
 * @type: ($block, $block, $commonNodeState) => Bool;
 *)
have_common_ancestor(chain1, chain2, node_state) ==
    LET get_blockchain_set(block) ==
        LET \* @type: (<<$block, Set($block)>>, Int) => <<$block, Set($block)>>; 
        ChainWithParent(last_block_and_chain_upto_slot, slot) ==
            LET last_block == last_block_and_chain_upto_slot[1] IN
            LET chain_upto_slot == last_block_and_chain_upto_slot[2] IN
            IF last_block = node_state.configuration.genesis \/ ~has_parent(last_block, node_state) THEN
                last_block_and_chain_upto_slot
            ELSE
                LET parent == get_parent(last_block, node_state) IN
                << parent, chain_upto_slot \union { parent } >>
        IN
        ApaFoldSet( ChainWithParent, <<block, { block } >>, 0..node_state.current_slot )[2]
    IN
    get_blockchain_set(chain1) \intersect get_blockchain_set(chain2) # {}

(*
 * Check if two blocks are conflicting.
 *
 * Requires: have_common_ancestor(chain1, chain2, node_state)
 *
 * @type: ($block, $block, $commonNodeState) => Bool;
 *)
are_conflicting(chain1, chain2, node_state) ==
    /\ ~is_ancestor_descendant_relationship(chain1, chain2, node_state)
    /\ ~is_ancestor_descendant_relationship(chain2, chain1, node_state)

=====