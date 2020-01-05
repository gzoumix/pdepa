#!/bin/bash

# maintainer: Michael Lienhardt
# email: michael.lienhardt@laposte.net
# license: GPLv3



#########################################
# PARAMETER MANIPULATION

function usage {
  echo "$0 -h|--help"
  echo "$0 [-d DISTRIB_FILE] [-s] TEST_FILE"
  echo "     -h|--help        print this message"
  echo "     -d DISTRIB_FILE  set the distribution where to get the bench data from. If not given, reads from the standard input."
  echo "     -s               also send the bench_run.sh script to the cluster"
  echo "     TEST_FILE        the file containing all the tests to perform"
}

TEST_FILE=""
DISTRIB_FILE=""
DISTRIB_FILE_TMP=""
SEND_SCRIPT=""

while [[ $# -gt 0 ]]; do
  case "$1" in
    -h|--help)
    [[ $# -ne 2 ]] && echo "Wrong number of arguments"
    usage
    exit 0
    ;;
    -d)
    DISTRIB_FILE="$2"
    shift # past argument
    shift # past value
    ;;
    -s)
    SEND_SCRIPT="YES"
    shift
    ;;
    *)
    [[ $# -ne 1 ]] && echo "Wrong number of arguments" && usage && exit 1
    TEST_FILE="$1"
    shift
    ;;
  esac
done

if [[ -z "${DISTRIB_FILE}" ]]; then
  DISTRIB_FILE="$(mktemp --tmpdir)"
  exec > "${DISTRIB_FILE}"
  DISTRIB_FILE_TMP="1"
fi

# ssh breaks the link to the input file, so we need to store its content before hand.
DATA=()
while read line; do
  DATA+=("$line")
done < "${DISTRIB_FILE}"

if [[ ! -z "${DISTRIB_FILE_TMP}" ]]; then
  rm "${DISTRIB_FILE}"
fi


NB_VM="${#DATA[@]}"

TESTS=()
while read line; do
  TESTS+=("$line")
done < "${TEST_FILE}"

#########################################
# MAIN FUNCTION

DIRNAME="$(dirname "${TEST_FILE}")"
FILENAME="$(basename "${TEST_FILE}")"
EXTENSION="${FILENAME##*.}"
FILENAME="${FILENAME%.*}"
if [[ "${EXTENSION}" == "${FILENAME}" ]]; then
  EXTENSION=""
else
  EXTENSION=".${EXTENSION}"
fi

i=1
j=1

for line in "${TESTS[@]}"; do
  echo "giving test $j to $i"
  #ssh "${CONNEXION}" "mkdir -p $(dirname "${TEST_FILE}") && echo \"${line}\" >> ${TEST_FILE}"
  echo "$line" >> "${DIRNAME}/${FILENAME}_${i}${EXTENSION}"
  [[ "$i" == "${NB_VM}" ]] && i=1 || i=$((i + 1))
  j=$((j + 1))
done


i=1
for line in "${DATA[@]}"; do
  CONNEXION="$(echo ${line} | cut -f1 -d' ')"
  echo "sending data to $i: ${CONNEXION}"
  ssh "${CONNEXION}" "mkdir -p ${DIRNAME}"
  scp "${DIRNAME}/${FILENAME}_${i}${EXTENSION}" "${CONNEXION}:${TEST_FILE}"
  [[ -z "${SEND_SCRIPT}" ]] || scp bench_run.sh bench_data.sh "${CONNEXION}:"
  i=$((i + 1))
done

