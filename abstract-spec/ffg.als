module abs/ffg --- an abstraction of FFG

open util/integer

sig Payload {}
sig Signature {}
fact atLeastFourSignatures { #Signature >= 4 }

sig Block {
	slot: Int,
	body: Payload,
	parent: Block
}

one sig GenesisPayload extends Payload {}
one sig GenesisBlock extends Block {}

sig Checkpoint {
	block: Block,
	slot: Int
}

one sig GenesisCheckpoint extends Checkpoint {}

fact genesisCheckpoint {
	GenesisCheckpoint.block = GenesisBlock
	GenesisCheckpoint.slot = 0
}

sig FfgVote {
	source: Checkpoint,
	target: Checkpoint
}

sig Vote {
	validator: Signature,
	ffgVote: FfgVote
}

one sig JustifiedCheckpoints {
	justified: set Checkpoint
}

fact voteStructuralEquality {
	all v1: Vote, v2: Vote |
		v1 = v2 <=> v1.validator = v2.validator and v1.ffgVote = v2.ffgVote
}

fact checkpointStructuralEquality {
	all c1: Checkpoint, c2: Checkpoint |
		c1 = c2 <=> c1.block = c2.block and c1.slot = c2.slot
}

fact ffgVoteStructuralEquality {
	all v1: FfgVote, v2: FfgVote |
		v1 = v2 <=> v1.source = v2.source and v1.target = v2.target
}

fact blockStructuralEquality {
	all b1: Block, b2: Block |
		b1 = b2 <=> b1.slot = b2.slot and b1.body = b2.body and b1.parent = b2.parent
}

fact genesisStructure {
	GenesisBlock.body = GenesisPayload
	GenesisBlock.parent = GenesisBlock
}

fact slotZeroIsGenesis {
	all b: Block | b.slot = 0 => b = GenesisBlock
}

fact noOtherBlockIsGenesis {
	all b: Block | 
		b.body = GenesisPayload implies b.slot = 0
}

fact blocksAreValid {
	all b: Block | {
		b = GenesisBlock or b.slot > b.parent.slot
	}
}

fact ffgVotesAreValid {
	all v: FfgVote | {
		isAncestorDescendant[v.source.block, v.target.block]
		v.source.slot < v.target.slot
	}
}

fact checkpointsAreValid {
	all c: Checkpoint | {
		(c.slot = 0 and c.block = GenesisBlock) or c.slot > c.block.slot
	}
}

pred isAncestorDescendant[p: Block, c: Block] {
	p in c.*parent
}

fact blocksDescendFromGenesis {
	all b: Block | isAncestorDescendant[GenesisBlock, b]
}

fun justifyingVotes[checkpoint: Checkpoint]: set Vote {
	{ v: Vote | {
		 	(v.ffgVote.source) in JustifiedCheckpoints.justified
			isAncestorDescendant[checkpoint.block, v.ffgVote.target.block]
			isAncestorDescendant[v.ffgVote.source.block, checkpoint.block]
			v.ffgVote.target.slot = checkpoint.slot
		}
	}
}

fact justifiedCheckpointsAreJustified {
	all c: JustifiedCheckpoints.justified |
		c.slot = 0 or 3.mul[#justifyingVotes[c].validator] >= 2.mul[#Signature]
}

fact unjustifiedCheckpointsAreNotJustified {
	all c: Checkpoint | {
		not c in JustifiedCheckpoints.justified => 3.mul[#justifyingVotes[c].validator] < 2.mul[#Signature]
	}
}

pred isJustified[checkpoint: Checkpoint] {
	checkpoint in JustifiedCheckpoints.justified
}

fun finalizedVotes[checkpoint: Checkpoint]: set Vote {
	{ v: Vote | {
			v.ffgVote.source = checkpoint
			v.ffgVote.target.slot = checkpoint.slot.add[1]
		}
	}
}

pred isFinalized[checkpoint: Checkpoint] {
	isJustified[checkpoint]
	3.mul[#finalizedVotes[checkpoint].validator] >= 2.mul[#Signature]
}

pred areConflictingBlocks[b1: Block, b2: Block] {
	!(isAncestorDescendant[b1, b2] or isAncestorDescendant[b2, b1])
}

pred isEquivocation[v1: Vote, v2: Vote] {
	v1.validator = v2.validator
	v1 != v2
	v1.ffgVote.target.slot = v2.ffgVote.target.slot
}

pred isSurroundVoting[v1: Vote, v2: Vote] {
	v1.validator = v2.validator
	v1.ffgVote.source.slot < v2.ffgVote.source.slot or {
		{
			v1.ffgVote.source.slot = v2.ffgVote.source.slot
			(v1.ffgVote.source.block.slot) < (v2.ffgVote.source.block.slot)
		}
	}
	v2.ffgVote.target.slot < v1.ffgVote.target.slot
}

fun slashableNodes: set Signature {
	{ vote1: Vote | some vote2: Vote |
		isEquivocation[vote1, vote2] or isSurroundVoting[vote1, vote2]
	}.validator
}

pred areFinalizedConflictingCheckpoints[c1: Checkpoint, c2: Checkpoint] {
	isFinalized[c1]
	isFinalized[c2]
	areConflictingBlocks[c1.block, c2.block]
}

pred disagreement {
	some c1: Checkpoint, c2: Checkpoint | areFinalizedConflictingCheckpoints[c1, c2]
}

pred accountableSafety {
	disagreement implies (3.mul[#slashableNodes] >= #Signature)
}

pred noAccountableSafety {
	disagreement and (3.mul[#slashableNodes] < #Signature)
}

pred someJustifiedCheckpoint { some c: Checkpoint | isJustified[c] and c.slot != 0 }
run someJustifiedCheckpoint for 6 but 3 Block, 5 Checkpoint, 5 int
run twoJustifiedCheckpoints {
	some c1: Checkpoint, c2: Checkpoint | {
		c1 != c2
		isJustified[c1]
		isJustified[c2]
		c1.slot != 0
		c2.slot != 0
	}
} for 6 but 3 Block, 5 Checkpoint, 5 int
run someFinalizedCheckpoint { some c: Checkpoint | isFinalized[c] and c.slot != 0 }
	for 10 but 6 Block, 6 Checkpoint, 12 Vote, 5 int
run someConflicting { some b1: Block, b2: Block | areConflictingBlocks[b1, b2] }
	for 6 but 3 Block, 6 Checkpoint, 5 int
run someSlashable { some slashableNodes }
	for 6 but 3 Block, 6 Checkpoint, 5 int
run disagreement for 10 but 5 Block, 6 Checkpoint, 20 Vote, 5 int
run accountableSafety for 10 but 5 Block, 6 Checkpoint, 20 Vote, 5 int
run noAccountableSafety for 10 but 5 Block, 6 Checkpoint, 20 Vote, 5 int
run { some b: Block | b != GenesisBlock } for 6 but 5 Block, 5 Checkpoint, 5 int
