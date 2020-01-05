#!/bin/bash

# maintainer: Michael Lienhardt
# email: michael.lienhardt@laposte.net
# license: GPLv3


#########################################
# PARAMETER MANIPULATION

function usage {
  echo "$0 -h|--help"
  echo "$0 [-l LIST_FILE] [-c CONCUR] [-k DOCKER_IMAGE] [-no pdepa|emerge|standard] BENCHDIR+"
  echo "     -h|--help                    print this message"
  echo "     -l LIST_FILE                 the file containing the list of tests to perform. If none given, read from the standard input"
  echo "     -c CONCUR                    sets the number of concurrent tests"
  echo "     -k DOCKER_IMAGE              sets the docker image to use"
  echo "     -no emerge|pdepa|standard    do not run the test for emerge, pdepa or the standard"
  echo "     BENCHDIR                     sets the directory where to store the benchs"
}

BENCHDIRS=()
LIST_FILE=""
LIST_FILE_TMP=""
DOCKER_IMAGE="gzoumix/pdepa:latest"
CONCURRENCE=1
TO_RUN=("YES" "YES" "YES")

while [[ $# -gt 0 ]]; do
  case "$1" in
    -h|--help)
    [[ $# -ne 1 ]] && echo "Wrong number of arguments"
    usage
    exit 0
    ;;
    -l)
    LIST_FILE="$2"
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
    -no)
    [[ "$2" == "emerge" ]]   && TO_RUN[0]=""
    [[ "$2" == "pdepa" ]]    && TO_RUN[1]=""
    [[ "$2" == "standard" ]] && TO_RUN[2]=""
    shift
    shift
    ;;
    *)
    BENCHDIRS+=("$1")
    shift # past argument
    ;;
  esac
done

if [[ -z "${LIST_FILE}" ]]; then
  LIST_FILE=$(mktemp --tmpdir)
  exec > "${LIST_FILE}"
  LIST_FILE_TMP="1"
fi


#########################################
# MAIN FUNCTION

# setup the bench repository
for BENCHDIR in "${BENCHDIRS[@]}"; do
  [ -e "${BENCHDIR}" ] || mkdir "${BENCHDIR}"
done

if [[ -z "${TO_RUN[2]}" ]]; then
  { docker run "${DOCKER_IMAGE}" bash -c "time pdepa_alt check -U -C -M -- $@" ; } &> "/tmp/pdepa_alt.out"
  sed -i "s/^user.*$/user 0.000s/" "/tmp/pdepa_alt.out"
fi

function test {
  DIR="$1/$2"
  shift
  shift

  mkdir "${DIR}"
  echo "$@" > "${DIR}/list.txt"
  # emerge
  #{ time emerge -p --backtrack=300 --autounmask y --autounmask-keep-keywords y --autounmask-keep-masks y --autounmask-continue y --autounmask-backtrack y "$@" ; } &> "${DIR}/emerge.out"
  if [[ ! -z "${TO_RUN[0]}" ]]; then
    { docker run "${DOCKER_IMAGE}" bash -c "time emerge -p --backtrack=300 --autounmask y --autounmask-continue y --autounmask-backtrack y $@" ; } &> "${DIR}/emerge.out"
    { [ "$?" -eq '0' ] && echo "success" || echo "fail" ; } > "${DIR}/emerge.res"
  else
    echo "conflict slot\nuser 0m0.000s" > "${DIR}/emerge.out"
    echo "fail" > "${DIR}/emerge.res"
  fi
  # pdepa
  #{ time  pdepa -U -C -p --  "$@" ; } &> "${DIR}/pdepa.out"
  if [[ ! -z "${TO_RUN[1]}" ]]; then
    { docker run "${DOCKER_IMAGE}" bash -c "time pdepa -U -C -M -p -v -- $@" ; } &> "${DIR}/pdepa.out"
    { [ "$?" -eq '0' ] && echo "success" || echo "fail" ; } > "${DIR}/pdepa.res"
  else
    echo "loaded 0\nuser 0m0.000s" > "${DIR}/pdepa.out"
    echo "fail" > "${DIR}/pdepa.res"
  fi
  # pdepa_alt
  #{ time  pdepa_alt -U -C -p --  "$@" ; } &> "${DIR}/pdepa_alt.out"
  if [[ ! -z "${TO_RUN[2]}" ]]; then
    { docker run "${DOCKER_IMAGE}" bash -c "time pdepa_alt check -U -C -M -- $@" ; } &> "${DIR}/pdepa_alt.out"
    { [ "$?" -eq '0' ] && echo "success" || echo "fail" ; } > "${DIR}/pdepa_alt.res"
  else
    cp "/tmp/pdepa_alt.out" "${DIR}/pdepa_alt.out"
    echo "fail" > "${DIR}/pdepa_alt.res"
  fi
}


processes=()
function wait_all {
  while [[ "${#processes[@]}" -ne 0 ]]; do
    wait "${processes[0]}"
    processes=("${processes[@]:1}")
  done
}


for BENCHDIR in "${BENCHDIRS[@]}"; do
  i=0
  while read line; do
    test "${BENCHDIR}" $line &
    processes+="$!"
    i=$((i+1))
    [[ "${#processes[@]}" -eq "${CONCURRENCE}" ]] && wait_all
  done < "${LIST_FILE}"
done
wait_all

if [[ ! -z "${LIST_FILE_TMP}" ]]; then
  rm "${LIST_FILE}"
fi
