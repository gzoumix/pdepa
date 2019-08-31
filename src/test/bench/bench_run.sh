#!/bin/bash

# maintainer: Michael Lienhardt
# email: michael.lienhardt@laposte.net
# license: GPLv3


#########################################
# PARAMETER MANIPULATION

function usage {
  echo "$0 -h|--help"
  echo "$0 [-d BENCHDIR] [-c CONCUR] [-k DOCKER_IMAGE] LIST_FILE"
  echo "     -h|--help        print this message"
  echo "     -d BENCHDIR      sets the directory where to store the benchs"
  echo "     -c CONCUR        sets the number of concurrent tests"
  echo "     -k DOCKER_IMAGE  sets the docker image to use"
  echo "     LIST_FILE        the file containing the list of tests to perform"
}

BENCHDIR="bench"
LIST_FILE=""
PYTHONPATH="$PYTHONPATH:$(pwd)/../../main"
DOCKER_IMAGE="gzoumix/pdepa:latest"
CONCURRENCE=1

while [[ $# -gt 0 ]]; do
  case "$1" in
    -h|--help)
    [[ $# -ne 1 ]] && echo "Wrong number of arguments"
    usage
    exit 0
    ;;
    -d)
    BENCHDIR="$2"
    shift # past argument
    shift # past value
    ;;
    -c)
    CONCURRENCE="$2"
    shift # past argument
    shift # past value
    ;;
    -k)
    DOCKER_IMAGE="$2"
    shift # past argument
    shift # past value
    ;;
    *)
    [[ $# -ne 1 ]] && echo "Wrong number of arguments" && usage && exit 1
    LIST_FILE="$1"
    shift # past argument
    ;;
  esac
done


#########################################
# MAIN FUNCTION

# setup the bench repository
[ -e "${BENCHDIR}" ] || mkdir "${BENCHDIR}"


function test {
  DIR="${BENCHDIR}/test_$1"
  shift

  mkdir "${DIR}"
  echo "$@" > "${DIR}/list.txt"
  # emerge
  #{ time emerge -p --backtrack=300 --autounmask y --autounmask-keep-keywords y --autounmask-keep-masks y --autounmask-continue y --autounmask-backtrack y "$@" ; } &> "${DIR}/emerge.out"
  { docker run "${DOCKER_IMAGE}" bash -c "time emerge -p --backtrack=300 --autounmask y --autounmask-continue y --autounmask-backtrack y $@" ; } &> "${DIR}/emerge.out"
  { [ "$?" -eq '0' ] && echo "success" || echo "fail" ; } > "${DIR}/emerge.res"
  # pdepa
  #{ time  pdepa -U -C -p --  "$@" ; } &> "${DIR}/pdepa.out"
  { docker run "${DOCKER_IMAGE}" bash -c "time pdepa -U -C -M -p -- $@" ; } &> "${DIR}/pdepa.out"
  { [ "$?" -eq '0' ] && echo "success" || echo "fail" ; } > "${DIR}/pdepa.res"
  # pdepa
  #{ time  pdepa_alt -U -C -p --  "$@" ; } &> "${DIR}/pdepa.out"
  { docker run "${DOCKER_IMAGE}" bash -c "time pdepa_alt check -U -C -M -- $@" ; } &> "${DIR}/pdepa_alt.out"
  { [ "$?" -eq '0' ] && echo "success" || echo "fail" ; } > "${DIR}/pdepa_alt.res"
}


processes=()
function wait_all {
  while [[ "${#processes[@]}" -ne 0 ]]; do
    wait "${processes[0]}"
    processes=("${processes[@]:1}")
  done
}


i=0
while read line; do
  test $i $line &
  processes+="$!"
  i=$((i+1))
  [[ "${#processes[@]}" -eq "${CONCURRENCE}" ]] && wait_all
done < "${LIST_FILE}"
wait_all

