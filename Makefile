STACKPATH=$(shell stack path | grep local-install-root | sed 's/local-install-root: //')

default:
	stack build
	@mkdir -p builds
	@cp ${STACKPATH}/bin/rpgsolve builds/rpgsolve

clean:
	stack clean
	@rm -r builds

