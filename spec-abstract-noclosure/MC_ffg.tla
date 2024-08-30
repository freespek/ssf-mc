----------------------------- MODULE MC_ffg -----------------------------

EXTENDS FiniteSets

\* @type: Int;
MAX_BLOCK_SLOT == 5
\* @type: Int;
MAX_BLOCK_BODY == 3

\* @type: Set(Str);
VALIDATORS == {"V1", "V2", "V3", "V4"}

N == 4

VARIABLES
    \* the set of all_blocks
    \* @type: Set($block);
    all_blocks,
    \* the set of blocks on chain 1
    \* @type: Set($block);
    chain1,
    \* the latest block on chain 1
    \* @type: $block;
    chain1_tip,
    \* the set of blocks on chain 2
    \* @type: Set($block);
    chain2,
    \* the latest block on chain 2
    \* @type: $block;
    chain2_tip,
    \* If chain2_fork_block_number is not equal to 0,
    \* then chain2 is a fork of chain1 starting at chain2_fork_block_number
    \* @type: Int;
    chain2_fork_block_number,
    \* @type: Set($ffgVote);
    ffg_votes,
    \* @type: Set($vote);
    votes,
    \* @type: Set($checkpoint);
    justified_checkpoints


INSTANCE ffg

Abs(x) == IF x >= 0 THEN x ELSE -x

IndInv ==
    /\ chain2_fork_block_number \in -MAX_BLOCK_BODY..0
    /\ all_blocks = chain1 \union chain2
    \* chain1_tip is the maximum block in chain 1
    /\ \A b \in chain1: b.body <= chain1_tip.body
    \* block numbers on chain 1 simply go from 0 to chain1_tip.body
    /\ \A b1, b2 \in chain1:
        /\ b1.body >= 0 /\ b1.body <= chain1_tip.body
        /\ (b1.body >= b2.body) <=> (b1.slot >= b2.slot)
    \* there are no gaps in the block numbers
    /\ \A i \in 0..MAX_BLOCK_BODY:
        i <= chain1_tip.body => \E b \in chain1: b.body = i
    \* chain2_tip is the maximum block in chain 2
    /\ \A b \in chain2: Abs(b.body) <= Abs(chain2_tip.body)
    \* block numbers on chain 2 go from 0 to (chain2_for_block_number - 1),
    \* then chain2_tip.body to chain2_fork_block_number
    /\ \A b1, b2 \in chain2:
        /\ (b1.body >= 0) => (b1.body < -chain2_fork_block_number) \/ ~IsForked
        /\ (b1.body < 0)  => (chain2_tip.body <= chain2_fork_block_number)
        /\ (Abs(b1.body) >= Abs(b2.body)) <=> (b1.slot >= b2.slot)
    \* there are no gaps in the block numbers (some of them are negative)
    /\ \A i \in 0..MAX_BLOCK_BODY:
        i <= Abs(chain2_tip.body) => \E b \in chain2: Abs(b.body) = i
    \* when there is no fork, the tips coincide
    /\ ~IsForked => chain2_tip = chain1_tip
    /\ GenesisBlock \in chain1
    /\ GenesisBlock \in chain2
    /\ \A ffgVote \in ffg_votes: IsValidFFGVote(ffgVote)
    /\ \A vote \in votes:
        /\ vote.ffg_vote \in ffg_votes
        /\ vote.validator \in VALIDATORS
    /\ justified_checkpoints = JustifiedCheckpoints(votes)

IndInit ==
    \* We choose two different bounds for creating chain1 and chain2 with Gen.
    \* See Apalache issue #2973.
    /\ chain1 = Gen(3)
    /\ chain1_tip \in chain1
    /\ chain2 = Gen(4)
    /\ chain2_tip \in chain2
    /\ ffg_votes = Gen(5) \* must be >= 4 to observe disagreement
    /\ votes = Gen(12)    \* must be >= 12 to observe disagreement
    /\ \E fork_number \in Int:
        /\ fork_number \in -MAX_BLOCK_BODY..0
        /\ chain2_fork_block_number = fork_number
    /\ IndInv

=============================================================================
