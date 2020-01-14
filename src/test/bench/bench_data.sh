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
    [[ $# -ne 2 ]] && echo "Wrong number of arguments"
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
  T=$(grep '^user' "$1" | sed 's/s//g' | cut -f 2)           # literal time
  echo "$(echo $T | cut -dm -f 1) *60 + $(echo $T | cut -dm -f 2)" | bc # time in seconds
}

function get_emerge_success {
  if ! grep -q '^\[ebuild' "$1" || grep -q '^\[blocks B' "$1" || grep -q 'REQUIRED_USE\|dependency .* conflict' "$1" ; then
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
  if [ "$(cat "$1")" = "fail" ]; then
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
  echo "TEST emerge_time emerge_success pdepa_time pdepa_success pdepa_alt_time pdepa_alt_success feature_full feature_loaded" > "${TABLE_FILE_NAME}"

  LIST=($(find "${BENCHDIR}" -name "pdepa.out" -printf "%P\n" | sort -g -t_ -k 2))
  for i in "${LIST[@]}"; do
    TEST="$(dirname $i)"
    EMERGE_OUT="${BENCHDIR}/${TEST}/emerge.out"
    EMERGE_RES="${BENCHDIR}/${TEST}/emerge.res"
    PDEPA_OUT="${BENCHDIR}/${TEST}/pdepa.out"
    PDEPA_RES="${BENCHDIR}/${TEST}/pdepa.res"
    PDEPA_ALT_OUT="${BENCHDIR}/${TEST}/pdepa_alt.out"
    PDEPA_ALT_RES="${BENCHDIR}/${TEST}/pdepa_alt.res"
    
    EMERGE_TIME="$(get_time ${EMERGE_OUT})"
    EMERGE_SUCCESS="$(get_emerge_success ${EMERGE_OUT})"
    
    PDEPA_TIME="$(get_time ${PDEPA_OUT})"
    PDEPA_SUCCESS="$(get_pdepa_success ${PDEPA_RES})"

    PDEPA_ALT_TIME="$(get_time ${PDEPA_ALT_OUT})"
    PDEPA_ALT_SUCCESS="$(get_pdepa_success ${PDEPA_ALT_RES})"

    FEATURE_FULL="$(grep "with .* features" "${PDEPA_ALT_OUT}" | cut -d' ' -f3)"
    FEATURE_LOADED="$(grep '^loaded' "${PDEPA_OUT}" | cut -d' ' -f2)"
    echo "${TEST}" "${EMERGE_TIME}" "${EMERGE_SUCCESS}" "${PDEPA_TIME}" "${PDEPA_SUCCESS}" "${PDEPA_ALT_TIME}" "${PDEPA_ALT_SUCCESS}" "${FEATURE_FULL}" "${FEATURE_LOADED}" >> "${TABLE_FILE_NAME}"
  done
done
