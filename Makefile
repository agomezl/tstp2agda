AGDA_MAIN=Main.agda
AGDA_STDLIB_DIR=/opt/agda-stdlib-0.9/src
PWD=`pwd`
SRC_DIR=src
BIN_DIR=bin
BIN_NAME_AGDA=Main
BIN_NAME_GHC=tstp2agda
GHC_FLAGS=-i${SRC_DIR}/
AGDA_FLAGS= -c ${SRC_DIR}/${AGDA_MAIN} -i ${SRC_DIR}/ -i ${AGDA_STDLIB_DIR}/ \
	   --compile-dir=${BIN_DIR}/ --ghc-flag=${GHC_FLAGS}
PROP_PROBLEMS=test/problems/

.PONY : clean agda-bin haskell-bin
haskell-bin : bin/tstp2agda
agda-bin : bin/Main


bin/tstp2agda : bin \
			     src/*.hs \
			     src/TSTP/*.hs \
			     src/Data/*.hs \
			     src/TSTP/Lexer.hs \
			     src/TSTP/Parser.hs
	ghc src/Main.hs -o bin/tstp2agda ${GHC_FLAGS}


src/TSTP/Lexer.hs : src/TSTP/Lexer.x
	alex -g -o $@ $<


src/TSTP/Parser.hs : src/TSTP/Parser.y
	happy -agc -o $@ $<


bin/Main : bin \
			      src/*.agda \
			      src/TSTP/*.agda \
			      src/TSTP/*.hs \
			      src/Data/*.hs
	agda ${AGDA_FLAGS}


bin :
	mkdir -p bin


tests_path 		 = test
tests_deep 		 = test/deep
tests_shallow   = test/shallow


.PHONY : basic-tests
basic-test :
	shelltest --color --execdir --precise $(tests_path)/basic.test
	@echo "$@ succeeded!"

.PHONY : deep-test
deep-test :
	shelltest --color --execdir --precise $(tests_path)/basic.test $(tests_deep)/
	@echo "$@ succeeded!"


.PHONY : shallow-test
shallow-test :
	cd $(tests_shallow)
	sh run-tests.sh
	@echo "$@ succeeded!"


# Hlint test

# Requires HLint >= 1.9.36 and run `cabal build` or `cabal install`
# before.
.PHONY : hlint
hlint :
	hlint --color=never Setup.hs
	hlint --color=never \
              --cpp-file=dist/build/autogen/cabal_macros.h \
              --cpp-include=src/ \
              src/
	@echo "$@ succeeded!"

.PHONY : haddock
haddock :
	cabal configure
	cabal haddock --executables \
	              --haddock-option=--use-unicode \
	              --hyperlink-source
	@echo "$@ succeeded!"

.PHONY : install-bin
install-bin :
	cabal configure
	cabal build
	cabal install --disable-documentation
	cabal sdist

.PHONY : install-fix-whitespace
install-fix-whitespace :
	cd src/fix-whitespace && cabal install

.PHONY : check-whitespace
check-whitespace :
	fix-whitespace --check


.PHONY : TODO
TODO :
	@find . -type d \( -path './.git' -o -path './dist' \) -prune -o -print \
	| xargs grep -I -s 'TODO' \
	| sort




.PHONY : problems
problems-metis:
	$(shell find ${PROP_PROBLEMS} -type f -name "prop*.tptp" -exec sh -c 'metis --show proof {} > {}s' \;)
	$(shell rename .tptps .tstp ${PROP_PROBLEMS}*.tptps)

.PHONY : problems-agda
problems-agda :
	$(shell find ${PROP_PROBLEMS} -type f -name "prop*tstp" -exec sh -c "tstp2agda {} -e deep > {}a" \;)
	$(shell rename .tstpa .agda ${PROP_PROBLEMS}*.tstpa)


clean :
	@rm -fr ${BIN_DIR}
	@rm -f ${SRC_DIR}/TSTP/Lexer.hs
	@rm -f ${SRC_DIR}/TSTP/Parser.hs
	@find ${SRC_DIR} -regex ".*\(\.hi\|\.o\|\.agdai\)$$" -exec rm -f {} \;
	@rm -f test/problems/*.agda
	@rm -f test/problems/*.agdai
	@rm -f test/problems/*.tstp
	@rm -f test/deep/*.agda
	@rm -f test/deep/*.agdai
	@rm -f cnf*
	@rm -f saturation.tptp
	@rm -rf dist


.PHONY : tests
tests :
	- make clean
	- make problems-metis
	- make problems-agda
	- make basic-test
	- make deep-test
	- make shallow-test
	- make hlint
	- make check-whitespace
	- make haddock
	- @echo "$@ succeeded!"

.PHONY : changed
changed :
	- cabal build
	- make deep-test

