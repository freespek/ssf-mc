---- MODULE chains ----
EXTENDS Integers, SequencesExt, Lists, Tuples, helpers

MAX_SLOT == 10

(*
    @typeAlias: hash = Str;
    @typeAlias: signature = SIGNATURE;
    @typeAlias: nodeIdentity = Str;
    @typeAlias: blockBody = Str;
    @typeAlias: block = {
        parent_hash: $hash,
        slot: Int,
        votes: Set($signedVoteMessage),
        body: $blockBody
    };
    @typeAlias: commonNodeState = {
        view_blocks: $hash -> $block
        // the rest is omitted
    };    
 *)
chains_aliases == TRUE

MkSeq(__N, __F(_)) ==
    \* This is the TLC implementation. Apalache does it differently.
    [ __i \in (1..__N) |-> __F(__i) ]

(*
 * Check if a block is part of a complete chain of blocks that reaches back to the genesis block.
 * 
 * For a non-recursive version for Apalache, see helpers.
 *
 * @type: ($block, $commonNodeState) => Bool;
 *)
RECURSIVE is_complete_chain(_, _)
is_complete_chain(block, node_state) ==
    IF block = node_state.configuration.genesis THEN TRUE
    ELSE IF ~has_parent(block, node_state) THEN FALSE
    ELSE is_complete_chain(get_parent(block, node_state), node_state)

(*
 * Construct a blockchain from a given block back to the genesis block.
 * Assumes that the given block is part of a complete chain.
 *
 * Requires: is_complete_chain(block, node_state)
 *
 * @type: ($block, $commonNodeState) => $list;
 *)
RECURSIVE get_blockchain(_, _)
get_blockchain(block, node_state) ==
    IF block = node_state.configuration.genesis THEN List(<< block >>)
    ELSE Concat(List(<< block >>), get_blockchain(get_parent(block, node_state), node_state))

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
get_blockchain_nonrec(block, node_state) ==
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
    FoldSeq( ChainWithParent, Pair(block, List(<< block >>)), MkSeq(MAX_SLOT, (* @type: Int => Int; *) LAMBDA i: i) )[2]    

get_blockchain_equivalence ==
    \A parent_hash \in STRING, slot \in Int, block_body \in STRING:
      \* TODO: introduces view_votes
      LET block == [ parent_hash |-> parent_hash, slot |-> slot, block_body |-> block_body, votes |-> {} ]
          node_state == [ view_blocks: [ x \in {} |-> {} ] ]
      IN
      get_blockchain(block, node_state) = get_blockchain_nonrec(block, node_state)
       
THEOREM get_blockchain_equivalence

=======================