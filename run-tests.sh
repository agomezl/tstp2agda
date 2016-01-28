#!/bin/bash

TSTP_EXAMPLES=examples/proof
TEST_DIR=$$.test
STDLIB=agda-stdlib
STDLIB_GIT=https://github.com/agda/agda-stdlib.git
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
    agda -i src/ -i ${TEST_DIR}/ -i ${STDLIB}/src/ \
         ${TEST_DIR}/${FILE} \
        || ( echo "FAILURE with ${MOD}" ; ((++FAIL)) )
    echo
}

function cleanup {
    rm -fr ${TEST_DIR}
}

trap cleanup EXIT SIGINT SIGTERM

mkdir -p ${TEST_DIR}

if ! ([ -d ${STDLIB} ] || git clone -b 2.4.2.3 ${STDLIB_GIT})
then echo "Failure downloading Agda library"
     exit 1
fi

for TEST in ${TSTP_EXAMPLES}/*.tstp
do
    do_test ${TEST}
done

[ ${FAIL} -eq 0 ] && exit 0 || exit 1
