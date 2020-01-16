#!/bin/bash

# maintainer: Michael Lienhardt
# email: michael.lienhardt@laposte.net
# license: GPLv3



#########################################
# PARAMETER MANIPULATION

function usage {
  echo "$0 -h|--help"
  echo "$0 [-d DISTRIB_FILE] [--prefix PREFIX] BENCHDIR+"
  echo "     -h|--help        print this message"
  echo "     -d DISTRIB_FILE  set the distribution where to get the bench data from. If not given, reads from the standard input."
  echo "     --prefix PREFIX  set the prefix in which the tables will be downloaded."
  echo "     BENCHDIR         the directories where the benchs are remotely stored."
}

BENCHDIR=()
PREFIX="."
DISTRIB_FILE=""
DISTRIB_FILE_TMP=""

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
    --prefix)
    PREFIX="$2"
    shift # past argument
    shift # past value
    ;;
    *)
    BENCHDIR+=("$1")
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


#########################################
# MAIN FUNCTION

VM_ID=0

function manage_vm {
  echo "==============================="
  echo "== $*"
  CONNEXION="$1"
  shift
  for DISTANT_DIR in "${BENCHDIR[@]}"; do
    LOCAL_DIR="${PREFIX}/${DISTANT_DIR}"
    # create the directory and the file if they don't exit
    mkdir -p "${LOCAL_DIR}"
    if [[ ! -e "${LOCAL_DIR}/table.csv" ]]; then
      echo "TEST emerge_time emerge_success pdepa_time pdepa_success pdepa_alt_time pdepa_alt_success feature_full feature_loaded" > "${LOCAL_DIR}/table.csv"
    fi
    # fill the file
    ssh "${CONNEXION}" "sed '1d' ${DISTANT_DIR}/table.csv" >> "${LOCAL_DIR}/table.csv"
    echo ""
  done
  echo "== ${CONNEXION} finished"
}


for line in "${DATA[@]}"; do
  manage_vm $line
  VM_ID=$((VM_ID + 1))
done



