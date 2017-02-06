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

haskell-bin : ${BIN_DIR}/${BIN_NAME_GHC}
agda-bin : ${BIN_DIR}/${BIN_NAME_AGDA}


${BIN_DIR}/${BIN_NAME_GHC} : ${BIN_DIR} \
			     ${SRC_DIR}/*.hs \
			     ${SRC_DIR}/TSTP/*.hs \
			     ${SRC_DIR}/Data/*.hs \
			     ${SRC_DIR}/TSTP/Lexer.hs \
			     ${SRC_DIR}/TSTP/Parser.hs
	ghc ${SRC_DIR}/Main.hs -o ${BIN_DIR}/${BIN_NAME_GHC} ${GHC_FLAGS}


${SRC_DIR}/TSTP/Lexer.hs : ${SRC_DIR}/TSTP/Lexer.x
	alex -g -o $@ $<

${SRC_DIR}/TSTP/Parser.hs : ${SRC_DIR}/TSTP/Parser.y
	happy -agc -o $@ $<

${BIN_DIR}/${BIN_NAME_AGDA} : ${BIN_DIR} \
			      ${SRC_DIR}/*.agda \
			      ${SRC_DIR}/TSTP/*.agda \
			      ${SRC_DIR}/TSTP/*.hs \
			      ${SRC_DIR}/Data/*.hs
	agda ${AGDA_FLAGS}

${BIN_DIR} :
	mkdir -p ${BIN_DIR}


.PHONY : install-bin
install-bin :
	- cabal install

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
