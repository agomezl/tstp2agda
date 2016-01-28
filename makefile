AGDA_MAIN=Main.agda
AGDA_STDLIB_DIR=/opt/agda-stdlib-0.9/src
SRC_DIR=src
BIN_DIR=bin
BIN_NAME_AGDA=Main
BIN_NAME_GHC=tstp2agda
GHC_FLAGS=-i${SRC_DIR}/
AGDA_FLAGS= -c ${SRC_DIR}/${AGDA_MAIN} -i ${SRC_DIR}/ -i ${AGDA_STDLIB_DIR}/ \
	   --compile-dir=${BIN_DIR}/ --ghc-flag=${GHC_FLAGS}

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


clean :
	rm -fr ${BIN_DIR}
	rm -f ${SRC_DIR}/TSTP/Lexer.hs
	rm -f ${SRC_DIR}/TSTP/Parser.hs
	find ${SRC_DIR} -regex ".*\(\.hi\|\.o\|\.agdai\)$$" -exec rm -f {} \;
