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
	apalache-mc check --init=Init_SingleChain --inv=Inv_SingleChain_PrecomputeOK --length=0 MC_ffg_examples.tla | grep EXITCODE
	apalache-mc check --init=Init_Forest      --inv=Inv_Forest_PrecomputeOK      --length=0 MC_ffg_examples.tla | grep EXITCODE

.PHONY: check clean test typecheck typecheck_all
