STACKPATH=$(shell stack path | grep local-install-root | sed 's/local-install-root: //')

default:
	stack build
	@mkdir -p builds
	@cp ${STACKPATH}/bin/rpgsolve builds/rpgsolve
	@cp ${STACKPATH}/bin/rpgprint builds/rpgprint
	@cp ${STACKPATH}/bin/rpgencode builds/rpgencode
	@cp ${STACKPATH}/bin/rpgcross builds/rpgcross
	@cp ${STACKPATH}/bin/tslmt2rpg builds/tslmt2rpg

clean:
	stack clean
	@rm -r builds

