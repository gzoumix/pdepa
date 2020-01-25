#!/bin/bash

# maintainer: Michael Lienhardt
# email: michael.lienhardt@laposte.net
# license: GPLv3



#########################################
# PARAMETER MANIPULATION

function usage {
  echo "$0 -h|--help"
  echo "$0 BENCHDIR+"
  echo "     -h|--help        print this message"
  echo "     BENCHDIR         the directory where the benchs are stored"
}

BENCHDIRS=()

while [[ $# -gt 0 ]]; do
  case "$1" in
    -h|--help)
    [[ $# -ne 1 ]] && echo "Wrong number of arguments"
    usage
    exit 0
    ;;
    *)
    BENCHDIRS+=("$1")
    shift
    ;;
  esac
done





#########################################
# FUNCTIONS

function create_file {
  [ -e "$1" ] && rm "$1"
  touch "$1"
}

function get_time {
  TIME_STRING=":$(grep '^user' "$1" | cut -f2)"
  TIME_ARRAY=(0 0 0)
  i=0
  while [[ "${TIME_STRING}" ]]; do
    TIME_ARRAY[$i]="${TIME_STRING##*:}"
    TIME_STRING="${TIME_STRING%:*}"
    i=$((i + 1))
  done
  echo "((${TIME_ARRAY[2]} * 60) + ${TIME_ARRAY[1]}) * 60 + ${TIME_ARRAY[0]}" | bc # time in seconds
}


function get_memory {
  MEMORY_STRING="$(grep '^memory' "$1" | cut -f2)"
  echo "scale=4; ${MEMORY_STRING} / 1024" | bc
}

function get_emerge_success {
  if ! grep -q '^\[ebuild' "$1" || grep -q '^\[blocks B' "$1" || grep -q 'REQUIRED_USE\|dependency .* conflict' "$1"  || grep -q 'Error: circular dependencies'; then
    echo False
	return
  else
    TMP=$(grep 'confict' "$1")
    if [ "$TMP" != "" ] && { echo "$TMP" | grep -q -v 'slot' ; }; then
      echo False
	  return
    fi
  fi
  echo True
  
}

function get_pdepa_success {
  if grep -q "Failure" "$1" ; then
    echo False
  else
    echo True
  fi
}

function get_standard_success {
  if grep -q "found an error" "$1" ; then
    echo False
  else
    echo True
  fi
}


#########################################
# MAIN ALGORITHM

for BENCHDIR in "${BENCHDIRS[@]}"; do
  TABLE_FILE_NAME="${BENCHDIR}/table.csv"
  create_file "${TABLE_FILE_NAME}"
  echo "TEST emerge_time emerge_memory emerge_success pdepa_time pdepa_memory pdepa_success standard_time standard_memory standard_success feature_full feature_loaded" > "${TABLE_FILE_NAME}"

  LIST=($(find "${BENCHDIR}" -name "pdepa.out" -printf "%P\n" | sort -g -t_ -k 2))
  for i in "${LIST[@]}"; do
    TEST="$(dirname $i)"
    EMERGE_OUT="${BENCHDIR}/${TEST}/emerge.out"
    EMERGE_RES="${BENCHDIR}/${TEST}/emerge.res"
    PDEPA_OUT="${BENCHDIR}/${TEST}/pdepa.out"
    PDEPA_RES="${BENCHDIR}/${TEST}/pdepa.res"
    STANDARD_OUT="${BENCHDIR}/${TEST}/standard.out"
    STANDARD_RES="${BENCHDIR}/${TEST}/standard.res"
    
    EMERGE_TIME="$(get_time ${EMERGE_OUT})"
    EMERGE_MEMORY="$(get_memory ${EMERGE_OUT})"
    EMERGE_SUCCESS="$(get_emerge_success ${EMERGE_OUT})"
    
    PDEPA_TIME="$(get_time ${PDEPA_OUT})"
    PDEPA_MEMORY="$(get_memory ${PDEPA_OUT})"
    PDEPA_SUCCESS="$(get_pdepa_success ${PDEPA_OUT})"

    STANDARD_TIME="$(get_time ${STANDARD_OUT})"
    STANDARD_MEMORY="$(get_memory ${STANDARD_OUT})"
    STANDARD_SUCCESS="$(get_standard_success ${STANDARD_OUT})"

    FEATURE_FULL="$(grep "with .* features" "${STANDARD_OUT}" | cut -d' ' -f3)"
    FEATURE_LOADED="$(grep '^loaded' "${PDEPA_OUT}" | cut -d' ' -f2)"
    echo "${TEST}" "${EMERGE_TIME}" "${EMERGE_MEMORY}" "${EMERGE_SUCCESS}" "${PDEPA_TIME}" "${PDEPA_MEMORY}" "${PDEPA_SUCCESS}" "${STANDARD_TIME}" "${STANDARD_MEMORY}" "${STANDARD_SUCCESS}" "${FEATURE_FULL}" "${FEATURE_LOADED}" >> "${TABLE_FILE_NAME}"
  done
done
