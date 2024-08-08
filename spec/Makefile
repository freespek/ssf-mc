typecheck:
	apalache-mc typecheck MC_ffg.tla

typecheck_all: typecheck
	# alternative implementations of recursive operators
	apalache-mc typecheck ffg_recursive.tla
	apalache-mc typecheck helpers_recursive.tla

check:
	apalache-mc check --length=0 --discard-disabled=true --inv=Inv MC_ffg.tla

clean:
	rm -rf _apalache-out/

test:
	apalache-mc check --init=Init_SingleChain_Precompute_Naive    --inv=Inv_SingleChain --length=0 MC_ffg_examples.tla | grep EXITCODE
	apalache-mc check --init=Init_SingleChain_Precompute_Fixpoint --inv=Inv_SingleChain --length=0 MC_ffg_examples.tla | grep EXITCODE
	apalache-mc check --init=Init_SingleChain_Precompute_Horizon  --inv=Inv_SingleChain --length=0 MC_ffg_examples.tla | grep EXITCODE
	apalache-mc check --init=Init_Forest_Precompute_Naive         --inv=Inv_Forest --length=0 MC_ffg_examples.tla | grep EXITCODE
	apalache-mc check --init=Init_Forest_Precompute_Fixpoint      --inv=Inv_Forest --length=0 MC_ffg_examples.tla | grep EXITCODE
	apalache-mc check --init=Init_Forest_Precompute_Horizon       --inv=Inv_Forest --length=0 MC_ffg_examples.tla | grep EXITCODE
	echo "Expect ERROR (12):"
	apalache-mc check --length=0 --discard-disabled --init=Init_Forest_Precompute_Naive    --inv=FinalizedCheckpoint_Example MC_ffg_examples.tla | grep EXITCODE
	apalache-mc check --length=0 --discard-disabled --init=Init_Forest_Precompute_Fixpoint --inv=FinalizedCheckpoint_Example MC_ffg_examples.tla | grep EXITCODE
	apalache-mc check --length=0 --discard-disabled --init=Init_Forest_Precompute_Horizon  --inv=FinalizedCheckpoint_Example MC_ffg_examples.tla | grep EXITCODE

.PHONY: check clean test typecheck typecheck_all
