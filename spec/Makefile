typecheck:
	apalache-mc typecheck ffg.tla

	# alternative implementations of recursive operators
	apalache-mc typecheck ffg_recursive.tla
	apalache-mc typecheck helpers_recursive.tla

check:
	apalache-mc check --length=0 --discard-disabled=true --inv=Inv MC_ffg.tla

clean:
	rm -rf _apalache-out/

.PHONY: clean typecheck