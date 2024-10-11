---------------------------- MODULE counterexample ----------------------------

EXTENDS MC_ffg_b1_ffg5_v12

(* Constant initialization state *)
ConstInit == TRUE

(* Initial state *)
State0 ==
  all_blocks = {[body |-> 0, slot |-> 0]}
    /\ chain1 = {[body |-> 0, slot |-> 0]}
    /\ chain1_tip = [body |-> 0, slot |-> 0]
    /\ chain2 = {[body |-> 0, slot |-> 0]}
    /\ chain2_fork_block_number = 0
    /\ chain2_tip = [body |-> 0, slot |-> 0]
    /\ ffg_votes = {}
    /\ justified_checkpoints = {<<[body |-> 0, slot |-> 0], 0>>}
    /\ votes = {}

(* Transition 3 to State1 *)
State1 ==
  all_blocks = { [body |-> -1, slot |-> 2], [body |-> 0, slot |-> 0] }
    /\ chain1 = {[body |-> 0, slot |-> 0]}
    /\ chain1_tip = [body |-> 0, slot |-> 0]
    /\ chain2 = { [body |-> -1, slot |-> 2], [body |-> 0, slot |-> 0] }
    /\ chain2_fork_block_number = -1
    /\ chain2_tip = [body |-> -1, slot |-> 2]
    /\ ffg_votes = {}
    /\ justified_checkpoints = {<<[body |-> 0, slot |-> 0], 0>>}
    /\ votes = {}

(* Transition 0 to State2 *)
State2 ==
  all_blocks = { [body |-> -1, slot |-> 2], [body |-> 0, slot |-> 0] }
    /\ chain1 = {[body |-> 0, slot |-> 0]}
    /\ chain1_tip = [body |-> 0, slot |-> 0]
    /\ chain2 = { [body |-> -1, slot |-> 2], [body |-> 0, slot |-> 0] }
    /\ chain2_fork_block_number = -1
    /\ chain2_tip = [body |-> -1, slot |-> 2]
    /\ ffg_votes
      = {[source |-> <<[body |-> -1, slot |-> 2], 4>>,
        target |-> <<[body |-> -1, slot |-> 2], 5>>]}
    /\ justified_checkpoints = {<<[body |-> 0, slot |-> 0], 0>>}
    /\ votes
      = { [ffg_vote |->
            [source |-> <<[body |-> -1, slot |-> 2], 4>>,
              target |-> <<[body |-> -1, slot |-> 2], 5>>],
          validator |-> "V1"],
        [ffg_vote |->
            [source |-> <<[body |-> -1, slot |-> 2], 4>>,
              target |-> <<[body |-> -1, slot |-> 2], 5>>],
          validator |-> "V2"],
        [ffg_vote |->
            [source |-> <<[body |-> -1, slot |-> 2], 4>>,
              target |-> <<[body |-> -1, slot |-> 2], 5>>],
          validator |-> "V3"],
        [ffg_vote |->
            [source |-> <<[body |-> -1, slot |-> 2], 4>>,
              target |-> <<[body |-> -1, slot |-> 2], 5>>],
          validator |-> "V4"] }

(* Transition 0 to State3 *)
State3 ==
  all_blocks = { [body |-> -1, slot |-> 2], [body |-> 0, slot |-> 0] }
    /\ chain1 = {[body |-> 0, slot |-> 0]}
    /\ chain1_tip = [body |-> 0, slot |-> 0]
    /\ chain2 = { [body |-> -1, slot |-> 2], [body |-> 0, slot |-> 0] }
    /\ chain2_fork_block_number = -1
    /\ chain2_tip = [body |-> -1, slot |-> 2]
    /\ ffg_votes
      = { [source |-> <<[body |-> -1, slot |-> 2], 4>>,
          target |-> <<[body |-> -1, slot |-> 2], 5>>],
        [source |-> <<[body |-> 0, slot |-> 0], 2>>,
          target |-> <<[body |-> -1, slot |-> 2], 4>>] }
    /\ justified_checkpoints = {<<[body |-> 0, slot |-> 0], 0>>}
    /\ votes
      = { [ffg_vote |->
            [source |-> <<[body |-> -1, slot |-> 2], 4>>,
              target |-> <<[body |-> -1, slot |-> 2], 5>>],
          validator |-> "V1"],
        [ffg_vote |->
            [source |-> <<[body |-> -1, slot |-> 2], 4>>,
              target |-> <<[body |-> -1, slot |-> 2], 5>>],
          validator |-> "V2"],
        [ffg_vote |->
            [source |-> <<[body |-> -1, slot |-> 2], 4>>,
              target |-> <<[body |-> -1, slot |-> 2], 5>>],
          validator |-> "V3"],
        [ffg_vote |->
            [source |-> <<[body |-> -1, slot |-> 2], 4>>,
              target |-> <<[body |-> -1, slot |-> 2], 5>>],
          validator |-> "V4"],
        [ffg_vote |->
            [source |-> <<[body |-> 0, slot |-> 0], 2>>,
              target |-> <<[body |-> -1, slot |-> 2], 4>>],
          validator |-> "V2"],
        [ffg_vote |->
            [source |-> <<[body |-> 0, slot |-> 0], 2>>,
              target |-> <<[body |-> -1, slot |-> 2], 4>>],
          validator |-> "V3"],
        [ffg_vote |->
            [source |-> <<[body |-> 0, slot |-> 0], 2>>,
              target |-> <<[body |-> -1, slot |-> 2], 4>>],
          validator |-> "V4"] }

(* Transition 1 to State4 *)
State4 ==
  all_blocks
      = { [body |-> -1, slot |-> 2],
        [body |-> 0, slot |-> 0],
        [body |-> 1, slot |-> 1] }
    /\ chain1 = { [body |-> 0, slot |-> 0], [body |-> 1, slot |-> 1] }
    /\ chain1_tip = [body |-> 1, slot |-> 1]
    /\ chain2 = { [body |-> -1, slot |-> 2], [body |-> 0, slot |-> 0] }
    /\ chain2_fork_block_number = -1
    /\ chain2_tip = [body |-> -1, slot |-> 2]
    /\ ffg_votes
      = { [source |-> <<[body |-> -1, slot |-> 2], 4>>,
          target |-> <<[body |-> -1, slot |-> 2], 5>>],
        [source |-> <<[body |-> 0, slot |-> 0], 2>>,
          target |-> <<[body |-> -1, slot |-> 2], 4>>] }
    /\ justified_checkpoints = {<<[body |-> 0, slot |-> 0], 0>>}
    /\ votes
      = { [ffg_vote |->
            [source |-> <<[body |-> -1, slot |-> 2], 4>>,
              target |-> <<[body |-> -1, slot |-> 2], 5>>],
          validator |-> "V1"],
        [ffg_vote |->
            [source |-> <<[body |-> -1, slot |-> 2], 4>>,
              target |-> <<[body |-> -1, slot |-> 2], 5>>],
          validator |-> "V2"],
        [ffg_vote |->
            [source |-> <<[body |-> -1, slot |-> 2], 4>>,
              target |-> <<[body |-> -1, slot |-> 2], 5>>],
          validator |-> "V3"],
        [ffg_vote |->
            [source |-> <<[body |-> -1, slot |-> 2], 4>>,
              target |-> <<[body |-> -1, slot |-> 2], 5>>],
          validator |-> "V4"],
        [ffg_vote |->
            [source |-> <<[body |-> 0, slot |-> 0], 2>>,
              target |-> <<[body |-> -1, slot |-> 2], 4>>],
          validator |-> "V2"],
        [ffg_vote |->
            [source |-> <<[body |-> 0, slot |-> 0], 2>>,
              target |-> <<[body |-> -1, slot |-> 2], 4>>],
          validator |-> "V3"],
        [ffg_vote |->
            [source |-> <<[body |-> 0, slot |-> 0], 2>>,
              target |-> <<[body |-> -1, slot |-> 2], 4>>],
          validator |-> "V4"] }

(* Transition 0 to State5 *)
State5 ==
  all_blocks
      = { [body |-> -1, slot |-> 2],
        [body |-> 0, slot |-> 0],
        [body |-> 1, slot |-> 1] }
    /\ chain1 = { [body |-> 0, slot |-> 0], [body |-> 1, slot |-> 1] }
    /\ chain1_tip = [body |-> 1, slot |-> 1]
    /\ chain2 = { [body |-> -1, slot |-> 2], [body |-> 0, slot |-> 0] }
    /\ chain2_fork_block_number = -1
    /\ chain2_tip = [body |-> -1, slot |-> 2]
    /\ ffg_votes
      = { [source |-> <<[body |-> -1, slot |-> 2], 4>>,
          target |-> <<[body |-> -1, slot |-> 2], 5>>],
        [source |-> <<[body |-> 0, slot |-> 0], 2>>,
          target |-> <<[body |-> -1, slot |-> 2], 4>>],
        [source |-> <<[body |-> 1, slot |-> 1], 2>>,
          target |-> <<[body |-> 1, slot |-> 1], 3>>] }
    /\ justified_checkpoints = {<<[body |-> 0, slot |-> 0], 0>>}
    /\ votes
      = { [ffg_vote |->
            [source |-> <<[body |-> -1, slot |-> 2], 4>>,
              target |-> <<[body |-> -1, slot |-> 2], 5>>],
          validator |-> "V1"],
        [ffg_vote |->
            [source |-> <<[body |-> -1, slot |-> 2], 4>>,
              target |-> <<[body |-> -1, slot |-> 2], 5>>],
          validator |-> "V2"],
        [ffg_vote |->
            [source |-> <<[body |-> -1, slot |-> 2], 4>>,
              target |-> <<[body |-> -1, slot |-> 2], 5>>],
          validator |-> "V3"],
        [ffg_vote |->
            [source |-> <<[body |-> -1, slot |-> 2], 4>>,
              target |-> <<[body |-> -1, slot |-> 2], 5>>],
          validator |-> "V4"],
        [ffg_vote |->
            [source |-> <<[body |-> 0, slot |-> 0], 2>>,
              target |-> <<[body |-> -1, slot |-> 2], 4>>],
          validator |-> "V2"],
        [ffg_vote |->
            [source |-> <<[body |-> 0, slot |-> 0], 2>>,
              target |-> <<[body |-> -1, slot |-> 2], 4>>],
          validator |-> "V3"],
        [ffg_vote |->
            [source |-> <<[body |-> 0, slot |-> 0], 2>>,
              target |-> <<[body |-> -1, slot |-> 2], 4>>],
          validator |-> "V4"],
        [ffg_vote |->
            [source |-> <<[body |-> 1, slot |-> 1], 2>>,
              target |-> <<[body |-> 1, slot |-> 1], 3>>],
          validator |-> "V1"],
        [ffg_vote |->
            [source |-> <<[body |-> 1, slot |-> 1], 2>>,
              target |-> <<[body |-> 1, slot |-> 1], 3>>],
          validator |-> "V2"],
        [ffg_vote |->
            [source |-> <<[body |-> 1, slot |-> 1], 2>>,
              target |-> <<[body |-> 1, slot |-> 1], 3>>],
          validator |-> "V3"],
        [ffg_vote |->
            [source |-> <<[body |-> 1, slot |-> 1], 2>>,
              target |-> <<[body |-> 1, slot |-> 1], 3>>],
          validator |-> "V4"] }

(* Transition 0 to State6 *)
State6 ==
  all_blocks
      = { [body |-> -1, slot |-> 2],
        [body |-> 0, slot |-> 0],
        [body |-> 1, slot |-> 1] }
    /\ chain1 = { [body |-> 0, slot |-> 0], [body |-> 1, slot |-> 1] }
    /\ chain1_tip = [body |-> 1, slot |-> 1]
    /\ chain2 = { [body |-> -1, slot |-> 2], [body |-> 0, slot |-> 0] }
    /\ chain2_fork_block_number = -1
    /\ chain2_tip = [body |-> -1, slot |-> 2]
    /\ ffg_votes
      = { [source |-> <<[body |-> -1, slot |-> 2], 4>>,
          target |-> <<[body |-> -1, slot |-> 2], 5>>],
        [source |-> <<[body |-> 0, slot |-> 0], 0>>,
          target |-> <<[body |-> 1, slot |-> 1], 2>>],
        [source |-> <<[body |-> 0, slot |-> 0], 2>>,
          target |-> <<[body |-> -1, slot |-> 2], 4>>],
        [source |-> <<[body |-> 1, slot |-> 1], 2>>,
          target |-> <<[body |-> 1, slot |-> 1], 3>>] }
    /\ justified_checkpoints
      = { <<[body |-> -1, slot |-> 2], 4>>,
        <<[body |-> -1, slot |-> 2], 5>>,
        <<[body |-> 0, slot |-> 0], 0>>,
        <<[body |-> 0, slot |-> 0], 2>>,
        <<[body |-> 0, slot |-> 0], 4>>,
        <<[body |-> 1, slot |-> 1], 2>>,
        <<[body |-> 1, slot |-> 1], 3>> }
    /\ votes
      = { [ffg_vote |->
            [source |-> <<[body |-> -1, slot |-> 2], 4>>,
              target |-> <<[body |-> -1, slot |-> 2], 5>>],
          validator |-> "V1"],
        [ffg_vote |->
            [source |-> <<[body |-> -1, slot |-> 2], 4>>,
              target |-> <<[body |-> -1, slot |-> 2], 5>>],
          validator |-> "V2"],
        [ffg_vote |->
            [source |-> <<[body |-> -1, slot |-> 2], 4>>,
              target |-> <<[body |-> -1, slot |-> 2], 5>>],
          validator |-> "V3"],
        [ffg_vote |->
            [source |-> <<[body |-> -1, slot |-> 2], 4>>,
              target |-> <<[body |-> -1, slot |-> 2], 5>>],
          validator |-> "V4"],
        [ffg_vote |->
            [source |-> <<[body |-> 0, slot |-> 0], 0>>,
              target |-> <<[body |-> 1, slot |-> 1], 2>>],
          validator |-> "V2"],
        [ffg_vote |->
            [source |-> <<[body |-> 0, slot |-> 0], 0>>,
              target |-> <<[body |-> 1, slot |-> 1], 2>>],
          validator |-> "V3"],
        [ffg_vote |->
            [source |-> <<[body |-> 0, slot |-> 0], 0>>,
              target |-> <<[body |-> 1, slot |-> 1], 2>>],
          validator |-> "V4"],
        [ffg_vote |->
            [source |-> <<[body |-> 0, slot |-> 0], 2>>,
              target |-> <<[body |-> -1, slot |-> 2], 4>>],
          validator |-> "V2"],
        [ffg_vote |->
            [source |-> <<[body |-> 0, slot |-> 0], 2>>,
              target |-> <<[body |-> -1, slot |-> 2], 4>>],
          validator |-> "V3"],
        [ffg_vote |->
            [source |-> <<[body |-> 0, slot |-> 0], 2>>,
              target |-> <<[body |-> -1, slot |-> 2], 4>>],
          validator |-> "V4"],
        [ffg_vote |->
            [source |-> <<[body |-> 1, slot |-> 1], 2>>,
              target |-> <<[body |-> 1, slot |-> 1], 3>>],
          validator |-> "V1"],
        [ffg_vote |->
            [source |-> <<[body |-> 1, slot |-> 1], 2>>,
              target |-> <<[body |-> 1, slot |-> 1], 3>>],
          validator |-> "V2"],
        [ffg_vote |->
            [source |-> <<[body |-> 1, slot |-> 1], 2>>,
              target |-> <<[body |-> 1, slot |-> 1], 3>>],
          validator |-> "V3"],
        [ffg_vote |->
            [source |-> <<[body |-> 1, slot |-> 1], 2>>,
              target |-> <<[body |-> 1, slot |-> 1], 3>>],
          validator |-> "V4"] }

(* The following formula holds true in the last state and violates the invariant *)
InvariantViolation ==
  LET disagreement_si_2_si__skolem ==
    Skolem((\E c1_2 \in justified_checkpoints:
      Skolem((\E c2_2 \in justified_checkpoints:
        (c1_2 = <<[slot |-> 0, body |-> 0], 0>>
            \/ (c1_2 \in justified_checkpoints
              /\ LET validatorsWhoCastFinalizingVote_si_3 ==
                {
                  v_6 \in { "V1", "V2", "V3", "V4" }:
                    \E finalizingVote_3 \in votes:
                      finalizingVote_3["validator"] = v_6
                        /\ LET ffgVote_si_6 == finalizingVote_3["ffg_vote"] IN
                        (ffgVote_si_6)["source"] = c1_2
                          /\ (ffgVote_si_6)["target"][2] = c1_2[2] + 1
                }
              IN
              validatorsWhoCastFinalizingVote_si_3
                \in { { "V1", "V2", "V3" },
                  { "V1", "V2", "V4" },
                  { "V1", "V3", "V4" },
                  { "V2", "V3", "V4" },
                  { "V1", "V2", "V3", "V4" } }))
          /\ (c2_2 = <<[slot |-> 0, body |-> 0], 0>>
            \/ (c2_2 \in justified_checkpoints
              /\ LET validatorsWhoCastFinalizingVote_si_4 ==
                {
                  v_7 \in { "V1", "V2", "V3", "V4" }:
                    \E finalizingVote_4 \in votes:
                      finalizingVote_4["validator"] = v_7
                        /\ LET ffgVote_si_7 == finalizingVote_4["ffg_vote"] IN
                        (ffgVote_si_7)["source"] = c2_2
                          /\ (ffgVote_si_7)["target"][2] = c2_2[2] + 1
                }
              IN
              validatorsWhoCastFinalizingVote_si_4
                \in { { "V1", "V2", "V3" },
                  { "V1", "V2", "V4" },
                  { "V1", "V3", "V4" },
                  { "V2", "V3", "V4" },
                  { "V1", "V2", "V3", "V4" } }))
          /\ ((c1_2[1]["slot"] > c2_2[1]["slot"]
              \/ ((~(c1_2[1] \in chain1) \/ ~(c2_2[1] \in chain1))
                /\ (~(c1_2[1] \in chain2) \/ ~(c2_2[1] \in chain2))))
            /\ (c2_2[1]["slot"] > c1_2[1]["slot"]
              \/ ((~(c2_2[1] \in chain1) \/ ~(c1_2[1] \in chain1))
                /\ (~(c2_2[1] \in chain2) \/ ~(c1_2[1] \in chain2)))))))))
  IN
  disagreement_si_2_si__skolem
    /\ (\A vote1_2 \in votes:
      \A vote2_2 \in votes:
        ~(vote1_2["validator"] = vote2_2["validator"])
          \/ (vote1_2 = vote2_2
            \/ ~(vote1_2["ffg_vote"]["target"][2]
              = vote2_2["ffg_vote"]["target"][2])))

================================================================================
(* Created by Apalache on Thu Sep 05 14:01:22 CEST 2024 *)
(* https://github.com/informalsystems/apalache *)
