#!/bin/bash

# maintainer: Michael Lienhardt
# email: michael.lienhardt@laposte.net
# license: GPLv3



#########################################
# PARAMETER MANIPULATION

function usage {
  echo "$0 -h|--help"
  echo "$0 [-d BENCHDIR]"
  echo "     -h|--help        print this message"
  echo "     -d BENCHDIR      sets the directory where to store the benchs"
}

BENCHDIR="bench"

while [[ $# -gt 0 ]]; do
  case "$1" in
    -h|--help)
    [[ $# -ne 2 ]] && echo "Wrong number of arguments"
    usage
    exit 0
    ;;
    -d)
    BENCHDIR="$2"
    shift # past argument
    shift # past value
    ;;
    *)
    echo "Wrong number of arguments" && usage && exit 1
    ;;
  esac
done

### FILE NAMES
# number of features loaded
PDEPA_LOAD="${BENCHDIR}/pdepa_load.dat"
PDEPA_LOAD_STAT="${BENCHDIR}/pdepa_load.txt"

# computation time
PDEPA_TIME="${BENCHDIR}/pdepa_time.dat"
EMERGE_TIME="${BENCHDIR}/emerge_time.dat"
FULL_TIME="${BENCHDIR}/full_time.dat"

PDEPA_TIME_STAT="${BENCHDIR}/pdepa_time.txt"
EMERGE_TIME_STAT="${BENCHDIR}/emerge_time.txt"
FULL_TIME_STAT="${BENCHDIR}/full_time.txt"

# failure
INCOMPLETE_EMERGE="${BENCHDIR}/emerge_fail.dat"
INCOMPLETE_PDEPA="${BENCHDIR}/pdepa_fail.dat"
INCOMPLETE_COMMON="${BENCHDIR}/common_fail.dat"



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

function stat_number {
  INPUT="$1"
  OUTPUT="$2"
  COLUMN="$3"
  nb='0'
  sum='0'
  square='0'
  min='86400'
  max="0"
  for i in $(cut -d' ' -f ${COLUMN} "$INPUT"); do
    nb=$((nb + 1))
    sum=$(echo "scale=3; $sum + $i" | bc)
    square=$(echo "scale=3; $square + (${i}^2)" | bc)
    min=$(echo "scale=3; if( $i < $min ) $i else $min" | bc)
    max=$(echo "scale=3; if( $i < $max ) $max else $i" | bc)
  done
  mean=$(echo "scale=3; $sum / $nb" | bc)
  variance=$(echo "scale=3; ($square / ${nb}) - (${mean}^2)" | bc)
  create_file "$OUTPUT"
  echo "mean $mean" >> "$OUTPUT"
  echo "variance $variance" >> "$OUTPUT"
  echo "deviation $(echo "scale=3; sqrt($variance)" | bc)" >> "$OUTPUT"
  echo "min ${min}" >> "$OUTPUT"
  echo "max ${max}" >> "$OUTPUT"
}



#########################################
# MAIN

NB_TEST_ALL=$(find "${BENCHDIR}" -name "pdepa.out" | wc -l)
NB_TOTAL_FEATURES=$(grep "with .* features" "$(find "${BENCHDIR}/" -name "pdepa_alt.out" -print -and -quit)" | cut -d' ' -f3)


#########################################
# first, create the feature loaded file
# which gives the order

create_file "${PDEPA_LOAD}"
for i in $(find "${BENCHDIR}" -name "pdepa.out" -printf "%P\n"); do
  N=$(grep '^loaded' "${BENCHDIR}/$i" | cut -d' ' -f2) # the number of loaded features
  N=$(echo "scale=3; ($N * 100) / ${NB_TOTAL_FEATURES}" | bc) # percent of the full set of features
  echo "$(dirname $i) $N" >> "${PDEPA_LOAD}"
done
sort -t' ' -k 2 -g -o "${PDEPA_LOAD}" "${PDEPA_LOAD}"
LIST=$(cut -d' ' -f 1 "${PDEPA_LOAD}")

stat_number "$PDEPA_LOAD" "$PDEPA_LOAD_STAT" 2

# add the column names to the file
#sed -i '1i name number' "${PDEPA_LOAD}"


#########################################
# second, create the time files

# first, generate the emerge file
create_file "$EMERGE_TIME"
for i in $LIST; do
  T=$(get_time "${BENCHDIR}/$i/emerge.out")
  echo "$i $T" >> "${EMERGE_TIME}"
done

# second, generate the pdepa file
create_file "${PDEPA_TIME}"
for i in $LIST; do
  T=$(get_time "${BENCHDIR}/$i/pdepa.out")
  echo "$i $T" >> "${PDEPA_TIME}"
done

# third, generate the pdepa_alt file
create_file "${FULL_TIME}"
for i in $LIST; do
  T=$(get_time "${BENCHDIR}/$i/pdepa_alt.out")
  echo "$i $T" >> "${FULL_TIME}"
done

stat_number "${EMERGE_TIME}" "${EMERGE_TIME_STAT}" 2
stat_number "${PDEPA_TIME}" "${PDEPA_TIME_STAT}" 2
stat_number "${FULL_TIME}" "${FULL_TIME_STAT}" 2

# add the column names to the files
#sed -i '1i name time' "${EMERGE_TIME}"
#sed -i '1i name time' "${PDEPA_TIME}"
#sed -i '1i name time' "${FULL_TIME}"


#########################################
# third, check emerge completeness

LIST=$(cut -d' ' -f 1 "${PDEPA_LOAD}")
LIST=($LIST) # get an array so we have direct lookup
MAX_E=$((${NB_TEST_ALL} - 1))


create_file "${INCOMPLETE_EMERGE}"
create_file "${INCOMPLETE_PDEPA}"
for j in $(seq 0 "${MAX_E}"); do
  k=$((j+1))
  i="${LIST[$j]}"
  EFAIL='nan'
  # ! [ebuild    => emerge does not try to install anything
  # REQUIRED_USE => emerge complains about the REQUIRED_USE not being set
  # dependency .* conflict  => emerge found a slot conflict and cannot proceed
  # conflict and not slot   => emerge found a conflict not linked to a slot
  if ! grep -q '^\[ebuild' "${BENCHDIR}/$i/emerge.out" || grep -q 'REQUIRED_USE\|dependency .* conflict' "${BENCHDIR}/$i/emerge.out" ; then
    EFAIL='1'
  else
    TMP=$(grep 'confict' "${BENCHDIR}/$i/emerge.out")
    if [ "$TMP" != "" ] && { echo "$TMP" | grep -q -v 'slot' ; }; then
      EFAIL='1'
    fi
  fi
  [ "$EFAIL" = "1" ] && echo "$i $k 1" >> "${INCOMPLETE_EMERGE}"
  [ "$(cat "${BENCHDIR}/$i/pdepa.res")" = "fail" ] &&  echo "$i $k 1" >> "${INCOMPLETE_PDEPA}"
done
sort -o "${INCOMPLETE_EMERGE}" "${INCOMPLETE_EMERGE}"
sort -o "${INCOMPLETE_PDEPA}" "${INCOMPLETE_PDEPA}"

# compute common failure
comm -12 "${INCOMPLETE_EMERGE}" "${INCOMPLETE_PDEPA}" > "${INCOMPLETE_COMMON}"
# remove common lines
PATTERN=$(while read line; do echo -n "^$line\\|"; done < ${INCOMPLETE_COMMON} | sed 's!/!\\/!g')
if [[ "${#PATTERN}" -ne 0 ]]; then
  PATTERN="${PATTERN::-2}"
  sed -i "/${PATTERN}/d" "${INCOMPLETE_EMERGE}"
  sed -i "/${PATTERN}/d" "${INCOMPLETE_PDEPA}"
fi


# add the column names to the files
#sed -i '1i name fail' "${INCOMPLETE_PDEPA}"
#sed -i '1i name fail' "${INCOMPLETE_EMERGE}"
#sed -i '1i name fail' "${INCOMPLETE_COMMON}"




