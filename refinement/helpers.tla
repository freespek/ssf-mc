---- MODULE helpers ----
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
========================
