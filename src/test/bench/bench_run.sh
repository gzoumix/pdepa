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
EXEC_MAIN=""
EXEC_PDEPA="python ../../main/pdepa.py"
EXEC_STANDARD="python pdepa_alt.py"
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
    EXEC_MAIN="docker run \"$2\" "
    EXEC_PDEPA="pdepa"
    EXEC_STANDARD="pdepa_alt"
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

TESTS=()
while read line; do TESTS+=("$line"); done < "${LIST_FILE}"
[[ ! -z "${LIST_FILE_TMP}" ]] && rm "${LIST_FILE}"

#########################################
# MAIN FUNCTION

# setup the bench repository
for BENCHDIR in "${BENCHDIRS[@]}"; do
  [ -e "${BENCHDIR}" ] || mkdir "${BENCHDIR}"
done

if [[ -z "${TO_RUN[2]}" ]]; then
  { ${EXEC_MAIN}bash -c "time ${EXEC_STANDARD} features -U -C -M" ; } &> "/tmp/pdepa_alt.out"
  sed -i "s/^user.*$/user\t0m000s/" "/tmp/pdepa_alt.out"
fi

function test {
  DIR="$1/$2"
  shift
  shift
  PACKAGES="$@"

  mkdir -p "${DIR}"
  if [[ -e "${DIR}/list.txt" ]]; then
    if [[ "$(cat ${DIR}/list.txt)" != "$@" ]]; then
      echo "ERROR: ${DIR}/list.txt does not correspond to the current test: $@"
      return
    fi
  else
    echo "${PACKAGES}" > "${DIR}/list.txt"
  fi

  # emerge
  #{ time emerge -p --backtrack=300 --autounmask y --autounmask-keep-keywords y --autounmask-keep-masks y --autounmask-continue y --autounmask-backtrack y "$@" ; } &> "${DIR}/emerge.out"
  if [[ ! -z "${TO_RUN[0]}" ]]; then
    echo "${EXEC_MAIN}bash -c \"time emerge -p --backtrack=300 --autounmask y --autounmask-continue y --autounmask-backtrack y ${PACKAGES}\"" &> "${DIR}/emerge.cmd"
    ${EXEC_MAIN}bash -c "time emerge -p --backtrack=300 --autounmask y --autounmask-continue y --autounmask-backtrack y ${PACKAGES}" &> "${DIR}/emerge.out"
    #{ [ "$?" -eq '0' ] && echo "success" || echo "fail" ; } > "${DIR}/emerge.res"
  elif [[ ! -e "${DIR}/emerge.out" ]]; then
    echo -e "conflict slot\nuser\t0m0.000s" > "${DIR}/emerge.out"
    echo "fail" > "${DIR}/emerge.res"
  fi
  # pdepa
  #{ time  pdepa -U -C -p --  "$@" ; } &> "${DIR}/pdepa.out"
  if [[ ! -z "${TO_RUN[1]}" ]]; then
    ${EXEC_MAIN}bash -c "time ${EXEC_PDEPA} -U -C -M -p -v -- ${PACKAGES}" &> "${DIR}/pdepa.out"
    { [ "$?" -eq '0' ] && echo "success" || echo "fail" ; } > "${DIR}/pdepa.res"
  elif [[ ! -e "${DIR}/pdepa.out" ]]; then
    echo -e "loaded 0\nuser\t0m0.000s" > "${DIR}/pdepa.out"
    echo "fail" > "${DIR}/pdepa.res"
  fi
  # pdepa_alt
  #{ time  pdepa_alt -U -C -p --  "$@" ; } &> "${DIR}/pdepa_alt.out"
  if [[ ! -z "${TO_RUN[2]}" ]]; then
    ${EXEC_MAIN}bash -c "time ${EXEC_STANDARD} check -U -C -M -- ${PACKAGES}" &> "${DIR}/pdepa_alt.out"
    { [ "$?" -eq '0' ] && echo "success" || echo "fail" ; } > "${DIR}/pdepa_alt.res"
  elif [[ ! -e "${DIR}/pdepa_alt.out" ]]; then
    cp "/tmp/pdepa_alt.out" "${DIR}/pdepa_alt.out"
    echo "fail" > "${DIR}/pdepa_alt.res"
  fi
}



function process {
  step="$2"
  max="$3"
  for BENCHDIR in "${BENCHDIRS[@]}"; do
    i="$1"
    while [ "$i" -lt "${max}" ]; do
      #echo ${TESTS[$i]}
      test "${BENCHDIR}" ${TESTS[$i]}
      i=$((i + step))
    done
  done
}


processes=()
function wait_all {
  while [[ "${#processes[@]}" -ne 0 ]]; do
    wait "${processes[0]}"
    processes=("${processes[@]:1}")
  done
}

MAX="${#TESTS[@]}"
for i in $(seq ${CONCURRENCE}); do
  j=$((i - 1))
  process $j ${CONCURRENCE} ${MAX} &
  processes+=("$!")
done
wait_all

# for BENCHDIR in "${BENCHDIRS[@]}"; do
#   i=0
#   while read line; do
#     test "${BENCHDIR}" $line &
#     processes+=("$!")
#     i=$((i+1))
#     [[ "${#processes[@]}" -eq "${CONCURRENCE}" ]] && wait_all
#   done < "${LIST_FILE}"
# done
# wait_all

