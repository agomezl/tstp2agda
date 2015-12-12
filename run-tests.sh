#!/bin/bash

TSTP_EXAMPLES=examples/proof
TEST_DIR=$$.test
FAIL=0
TEST_N=1

function do_test {
    echo "####################"
    echo "# Test $((TEST_N++)) "
    echo "####################"
    echo

    MOD=$(basename $1 | cut -d. -f 1)
    FILE=${MOD}.agda
    cabal run -- -f $1 -o ${TEST_DIR}/${FILE} -m ${MOD}
    agda -i src/ -i ${TEST_DIR}/ ${TEST_DIR}/${FILE} \
        || ( echo "FAILURE with ${MOD}" ; ((++FAIL)) )
    echo
}

function cleanup {
    rm -fr ${TEST_DIR}
}

trap cleanup EXIT SIGINT SIGTERM

mkdir -p ${TEST_DIR}

for TEST in ${TSTP_EXAMPLES}/*.tstp
do
    do_test ${TEST}
done

[ ${FAIL} -eq 0 ] && exit 0 || exit 1
