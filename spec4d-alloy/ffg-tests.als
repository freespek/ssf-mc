module abs/ffg_tests
-- a separate module for the examples

open abs/ffg

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

