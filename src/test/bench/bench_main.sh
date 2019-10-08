#!/bin/bash

# maintainer: Michael Lienhardt
# email: michael.lienhardt@laposte.net
# license: GPLv3

#########################################
# PARAMETER MANIPULATION

function usage {
  echo "$0 -h|--help"
  echo "$0 [-d BENCHDIR] [-f LIST_FILE] [-c CONCUR] [NB_TEST] [NB_CP_MIN] [NB_CP_MAX]"
  echo "     -h|--help        print this message"
  echo "     -d BENCHDIR      sets the directory where to store the benchs"
  echo "     -f LIST_FILE     sets the file storing the list of tests"
  echo "     -c CONCUR        sets the number of concurrent tests"
  echo "     -k DOCKER_IMAGE  sets the docker image to use"
  echo "     NB_TEST          sets the number of tests to perform"
  echo "     NB_CP_MIN        sets the min number of cp in a test"
  echo "     NB_CP_MAX        sets the max number of cp in a test"
}

BENCHDIR="bench"
LIST_FILE="tests.txt"
DOCKER_IMAGE="gzoumix/pdepa:latest"
CONCURRENCE=1
NB_TEST=1000
NB_CP_MAX=10

arg_id=0
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
    -f)
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
    *)
    if [[ $arg_id -eq 0 ]]; then
      NB_TEST=$1
    elif [[ $arg_id -eq 1 ]]; then
      NB_CP_MIN=$1
    elif [[ $arg_id -eq 2 ]]; then
      NB_CP_MAX=$1
    else
      echo "Wrong number of arguments" && usage && exit 1
    fi
    shift
    arg_id=$((arg_id+1))
    ;;
  esac
done



#########################################
# MAIN FUNCTION

docker run "${DOCKER_IMAGE}" bash -c "python /opt/pdepa/src/test/bench/bench_gen.py ${NB_TEST} ${NB_CP_MIN} ${NB_CP_MAX}" > "${LIST_FILE}"
./bench_run.sh -d "${BENCHDIR}" -c "${CONCURRENCE}" -k "${DOCKER_IMAGE}" "${LIST_FILE}"
./bench_data.sh -d "${BENCHDIR}"

