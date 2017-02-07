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
PROP_PROBLEMS=${PWD}/problems/

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

test_path = test/basics

.PHONY : errors
errors :
	shelltest --color --execdir --precise  $(tests_path)/basics.test
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
	cabal install --disable-documentation

.PHONY : install-fix-whitespace
install-fix-whitespace :
	cd src/fix-whitespace && cabal install

.PHONY : check-whitespace
check-whitespace :
	fix-whitespace --check

.PHONY : TODO
TODO :
	find . -type d \( -path './.git' -o -path './dist' \) -prune -o -print \
	| xargs grep -I 'TODO' \
	| sort

.PHONY : problems
problems-metis:
	@echo ${PWD}
	@cd ${PROP_PROBLEMS}
	@find . -type f -name "prop*.tptp" -exec sh -c "metis --show proof --show saturation {} > {}.tstp" \;


.PHONY : problems-agda
problems-agda :
	@echo ${PWD}
	@cd ${PROP_PROBLEMS}
	@find . -type f -name "prop*.tptp.tstp" -exec sh -c "basename {} ; tstp2agda {} -e deep > `basename {}`.agda" \;
	@echo
	@echo "Generated files!"
	ls ${PROP_PROBLEMS}

clean :
	rm -fr ${BIN_DIR}
	rm -f ${SRC_DIR}/TSTP/Lexer.hs
	rm -f ${SRC_DIR}/TSTP/Parser.hs
	find ${SRC_DIR} -regex ".*\(\.hi\|\.o\|\.agdai\)$$" -exec rm -f {} \;
	rm -f ${PROP_PROBLEMS}/*.agda
	rm -f ${PROP_PROBLEMS}/*.tstp
	rm -f cnf*
	rm -f saturation.tptp


.PHONY : tests
tests :
	make errors
	make hlint
	make check-whitespace
	make haddock
	@echo "$@ succeeded!"
