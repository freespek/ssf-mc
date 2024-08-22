; Check accountable safety for the 3SF protocol.
;
; We encode an abstract version of the 3SF protocol (high-level definitions)
; using SMT constraints. In particular, we make use of the decision procedure
; for finite sets and cardinality constraints in CVC5.
; This allows us to check accountable safety for small models of the protocol.

; Run with
;   $ cvc5 ssf.smt
;
; Tested with CVC5 v1.2.0.

(set-logic ALL)

(set-option :produce-models true)
; we need finite model finding to answer sat problems with universal
; quantified formulas
(set-option :finite-model-find true)
; enable extended set operators
(set-option :sets-ext true)
; we need to enable incremental mode to answer multiple queries
(set-option :incremental true)

; ============================
; Datatypes
; ============================

; we search a finite universe: 3 hashes, 5 checkpoints, 4 nodes
(declare-datatype Hash ((Hash1) (Hash2) (Hash3)))
(declare-datatype Checkpoint ((C1) (C2) (C3) (C4) (C5)))
(declare-datatype Node ((Alice) (Bob) (Charlie) (David)))
(define-fun N () Int 4)
(declare-datatype Vote ((Vote (source Checkpoint) (target Checkpoint) (sender Node))))

; ============================
; Blocks
; ============================

; genesis block
(declare-const genesis Hash)

; edges, genesis has a self-loop
(declare-fun parent_of (Hash) Hash)
(assert (= (parent_of genesis) genesis))

; slots
(declare-fun slot (Hash) Int)
(assert (= (slot genesis) 0))

; slots are increasing from parent to child
(assert (forall ((h Hash)) (=> (not (= h genesis)) (> (slot h) (slot (parent_of h))))))

; ancestor-descendant relationship
(declare-const ancestor_descendant_relationship (Relation Hash Hash))
(assert (forall ((ancestor Hash) (descendant Hash))
    (=  (set.member (tuple ancestor descendant) ancestor_descendant_relationship)
        (or
            (= ancestor descendant)
            (and
                (not (= descendant genesis))
                (set.member (tuple ancestor (parent_of descendant)) ancestor_descendant_relationship)
            )
        )
    )
))

; conflicting blocks
(declare-const conflicting_blocks (Relation Hash Hash))
(assert (forall ((h1 Hash) (h2 Hash))
    (=  (set.member (tuple h1 h2) conflicting_blocks)
        (and
            (not (set.member (tuple h1 h2) ancestor_descendant_relationship))
            (not (set.member (tuple h2 h1) ancestor_descendant_relationship))
        )
    )
))

; ============================
; Checkpoints
; ============================

; genesis checkpoint
(declare-const genesis_checkpoint Checkpoint)

; checkpoint block
(declare-fun checkpoint_block (Checkpoint) Hash)
(assert (= (checkpoint_block genesis_checkpoint) genesis))

; checkpoint slot
(declare-fun checkpoint_slot (Checkpoint) Int)
(assert (= (checkpoint_slot genesis_checkpoint) 0))

; all checkpoints ((B, block_slot), chkp_slot) except genesis have chkp_slot > block_slot
(assert (forall ((c Checkpoint)) (or (= c genesis_checkpoint) (> (checkpoint_slot c) (slot (checkpoint_block c))))))

; checkpoints have no "identity": if they have the same block and slot, they are the same checkpoint
(assert (forall ((c1 Checkpoint) (c2 Checkpoint))
    (=>
        (and
            (= (checkpoint_block c1) (checkpoint_block c2))
            (= (checkpoint_slot c1) (checkpoint_slot c2))
        )
        (= c1 c2)
    )
))

; ============================
; Votes
; ============================

; votes have no "identity": if they have the same checkpoints and sender, they are the same vote
(assert (forall ((v1 Vote) (v2 Vote))
    (=>
        (and
            (= (source v1) (source v2))
            (= (target v1) (target v2))
            (= (sender v1) (sender v2))
        )
        (= v1 v2)
    )
))

; votes that have been cast, a subset of all valid FFG votes
(declare-const votes (Set Vote))
(assert (forall ((vote Vote))
    (=> (set.member vote votes)
        (and
            ; valid FFG votes connect a descendant to an ancestor
            (set.member (tuple (checkpoint_block (source vote)) (checkpoint_block (target vote))) ancestor_descendant_relationship)
            ; valid FFG votes have increasing slots
            (< (checkpoint_slot (source vote)) (checkpoint_slot (target vote)))
        )
    )
))

; ============================
; Justification & Finalization
; ============================

; justified checkpoints
(declare-const justified_checkpoints (Set Checkpoint))
(assert (= justified_checkpoints (set.comprehension ((c Checkpoint))
        (or
            ; L3: genesis is justified
            (= c genesis_checkpoint)
            ; L4: there is a quorum of validators that cast a vote from a justified checkpoint to c
            (>= (* 3 (set.card (set.comprehension ((node Node))
                    (exists ((vote Vote)) (and
                        ; L4+5: vote is a valid vote cast by node
                        (set.member vote votes)
                        (= (sender vote) node)
                        ; L6: the source of the vote is justified
                        (set.member (source vote) justified_checkpoints)
                        ; L7: there is a chain source.block ->* checkpoint.block ->* target.block
                        (and
                            (set.member (tuple (checkpoint_block (source vote)) (checkpoint_block c)) ancestor_descendant_relationship)
                            (set.member (tuple (checkpoint_block c) (checkpoint_block (target vote))) ancestor_descendant_relationship)
                        )
                        ; L8: the target checkpoint slot is the same as the checkpoint's
                        (= (checkpoint_slot (target vote)) (checkpoint_slot c))
                    ))
                    node
                )))
                (* 2 N)
            )
        )
        c
    )
))

; finalized checkpoints
(declare-const finalized_checkpoints (Set Checkpoint))
(assert (= finalized_checkpoints (set.comprehension ((c Checkpoint))
        (or
            ; L11: genesis is finalized
            (= c genesis_checkpoint)
            (and
                ; L12: c is justified
                (set.member c justified_checkpoints)
                ; L13: there is a quorum of validators who cast a vote from c to the next slot
                (>= (* 3 (set.card (set.comprehension ((node Node))
                        (exists ((vote Vote)) (and
                            ; L13+14: vote is a valid vote cast by node
                            (set.member vote votes)
                            (= (sender vote) node)
                            ; L14: the source of the vote is the checkpoint
                            (= (source vote) c)
                            ; L15: the target checkpoint slot is one more than the checkpoint's
                            (= (checkpoint_slot (target vote)) (+ 1 (checkpoint_slot c)))
                        ))
                        node
                    )))
                    (* 2 N)
                )
            )
        )
        c
    )
))

; finalized blocks
(declare-const finalized_blocks (Set Hash))
(assert (forall ((h Hash))
    (=
        (set.member h finalized_blocks)
        (exists ((c Checkpoint))
            (and
                (set.member c finalized_checkpoints)
                (= (checkpoint_block c) h)
            )
        )
    )
))

; ============================
; Slashing
; ============================

; equivocating votes
(define-fun are_equivocating_votes ((vote1 Vote) (vote2 Vote)) Bool
    (and
        ; vote1 != vote2
        (not (= vote1 vote2))
        ; vote1.target.chkp_slot = vote2.target.chkp_slot
        (= (checkpoint_slot (target vote1)) (checkpoint_slot (target vote2)))
    )
)

; surround votes
(define-fun does_first_vote_surround_second_vote ((vote1 Vote) (vote2 Vote)) Bool
    (and
        (or
            ; vote1.source.chkp_slot < vote2.source.chkp_slot
            (< (checkpoint_slot (source vote1)) (checkpoint_slot (source vote2)))
            (and
                ; vote1.source.chkp_slot = vote2.source.chkp_slot
                (= (checkpoint_slot (source vote1)) (checkpoint_slot (source vote2)))
                ; vote1.source.block.slot < vote2.source.block.slot
                (< (slot (checkpoint_block (source vote1))) (slot (checkpoint_block (source vote2))))
            )
        )
        ; vote2.target.chkp_slot < vote1.target.chk_slot
        (< (checkpoint_slot (target vote2)) (checkpoint_slot (target vote1)))
    )
)

; slashable nodes
(declare-const slashable_nodes (Set Node))
(assert (= slashable_nodes (set.comprehension ((node Node))
        (exists ((vote1 Vote) (vote2 Vote))
            (and
                (= (sender vote1) node)
                (= (sender vote2) node)
                (set.member vote1 votes)
                (set.member vote2 votes)
                (or
                    (are_equivocating_votes vote1 vote2)
                    (does_first_vote_surround_second_vote vote1 vote2)
                )
            )
        )
        node
    )
))

; ============================
; Examples
; ============================

; uncomment one of the following queries to search for a model

; ; find conflicting blocks
; (assert (not (= conflicting_blocks (as set.empty (Relation Hash Hash)))))
; (check-sat)
; (get-model)

; ; find a justified checkpoint (besides genesis)
; (assert (not (= justified_checkpoints (set.singleton genesis_checkpoint))))
; (check-sat)
; (get-model)

; ; find a finalized checkpoint (besides genesis)
; (assert (not (= finalized_checkpoints (set.singleton genesis_checkpoint))))
; (check-sat)
; (get-model)

; ; find two conflicting finalized blocks
; (assert (exists ((block1 Hash) (block2 Hash))
;     (and
;         (set.member (tuple block1 block2) conflicting_blocks)
;         (set.member block1 finalized_blocks)
;         (set.member block2 finalized_blocks)
;     )
; ))
; (check-sat)
; (get-model)

; ; find a slashable node
; (assert (not (= slashable_nodes (as set.empty (Set Node)))))
; (check-sat)
; (get-model)

; ============================
; Accountable Safety
; ============================

; We want to check
;     \E b1, b2 : b1 and b2 are conflicting and finalized  => \E node : node is slashable
;
; This formula is valid iff its negation
;     \E b1, b2 : b1 and b2 are conflicting and finalized  /\  ~ (\E node : node is not slashable)
; is unsatisfiable.
(assert
    (and
        (exists ((block1 Hash) (block2 Hash))
            (and
                (set.member (tuple block1 block2) conflicting_blocks)
                (set.member block1 finalized_blocks)
                (set.member block2 finalized_blocks)
            )
        )
        (not (exists ((node Node)) (set.member node slashable_nodes)))
    )
)

(echo "searching for accountable safety violation [expect unsat]")
(check-sat)
