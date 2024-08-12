---- MODULE helpers ----
(*
 * Translation of the `helpers.py` Python module to TLA+.
 *
 * Recursive functions are translated to Apalache folds, see
 *   - [the translation rules](../Translation.md#bounded-recursion-rule)
 *   - [the Apalache manual on folds](https://apalache.informal.systems/docs/apalache/principles/folds.html)
 *
 * For a naive translation to recursive TLA+ operators (not supported by Apalache), see `./helpers_recursive.tla`.
 *
 * Thomas Pani, Jure Kukovec. 2024.
 *
 * Subject to Apache 2.0. See `LICENSE.md`.
 *)

EXTENDS typedefs, Apalache, Integers, Tuples

CONSTANTS
    (*
     * Hash a block
     *
     * @type: $block => $hash;
     *)
    BLOCK_HASH(_),
    (*
     * Maximum slot (inclusive) for Apalache to fold over
     * when traversing ancestors.
     *
     * @type: Int;
     *)
    MAX_SLOT

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
    LET 
        \* @type: (Int, $nodeIdentity) => Int;
        Accumulate(x, n) == x + validatorBalances[n]
    IN ApaFoldSet(Accumulate, 0, queried_validator_ids)

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
            Pair(parent, Push(chain_upto_slot, parent))
    IN
    ApaFoldSeqLeft( ChainWithParent, Pair(block, List(<< block >>)), MkSeq(MAX_SLOT, (* @type: Int => Int; *) LAMBDA i: i) )[2]

\* @type: ($block, $commonNodeState) => Bool;
is_complete_chain(block, node_state) ==
    \* We could also do this without constructing the entire list / blockchain,
    \* with a fold similar to above, but reducing to a boolean flag indicating
    \* if it has seen the genesis block. Choosing this version now for brevity.
    Last(get_blockchain(block, node_state)) = node_state.configuration.genesis

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
        IF flag THEN Pair(last_block, TRUE)
        ELSE IF last_block = node_state.configuration.genesis \/ ~has_parent(last_block, node_state) THEN Pair(last_block, FALSE)
        ELSE LET parent == get_parent(last_block, node_state) IN Pair(parent, parent = ancestor)
    IN
    ApaFoldSeqLeft( FindAncestor, Pair(descendant, descendant = ancestor), MkSeq(MAX_SLOT, (* @type: Int => Int; *) LAMBDA i: i) )[2]

(*
 * Filter blocks, retaining only those that are ancestors of a specified block.
 *
 * @type: ($block, Set($block), $commonNodeState) => Set($block);
 *)
filter_out_blocks_non_ancestor_of_block(block, blocks, node_state) ==
    { b \in blocks: is_ancestor_descendant_relationship(b, block, node_state) }

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
                Pair(parent, chain_upto_slot \union { parent })
        IN ApaFoldSeqLeft( ChainWithParent, Pair(block, { block }), MkSeq(MAX_SLOT, (* @type: Int => Int; *) LAMBDA i: i) )[2]
    IN get_blockchain_set(chain1) \intersect get_blockchain_set(chain2) # {}

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