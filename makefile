AGDA_MAIN=Main.agda
AGDA_STDLIB_DIR=/opt/agda-stdlib-0.9/src
SRC_DIR=src
BIN_DIR=bin
BIN_NAME=Main
GHC_FLAGS=-i${SRC_DIR}/
AGDA_FLAGS= -c ${SRC_DIR}/${AGDA_MAIN} -i ${SRC_DIR}/ -i ${AGDA_STDLIB_DIR}/ \
	   --compile-dir=${BIN_DIR}/ --ghc-flag=${GHC_FLAGS}



${BIN_DIR}/${BIN_NAME} : ${BIN_DIR} \
			 ${SRC_DIR}/*.agda \
			 ${SRC_DIR}/TSTP/*.agda \
			 ${SRC_DIR}/TSTP/*.hs \
			 ${SRC_DIR}/Data/*.hs
	agda ${AGDA_FLAGS}

${BIN_DIR} :
	mkdir -p ${BIN_DIR}


clean :
	rm -fr ${BIN_DIR}
	find ${SRC_DIR} -regex ".*\(\.hi\|\.o\|\.agdai\)$$" -exec rm -f {} \;
