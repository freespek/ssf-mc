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

.PHONY: check clean typecheck typecheck_all