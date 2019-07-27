#!/bin/bash

NB_TOTAL_FEATURES='670123'
NB_TEST_FULL='21'

NB_TEST_ALL=$(find bench -name "pdepa.out" | wc -l)


# file names
PDEPA_TIME="pdepa_time.dat"
EMERGE_TIME="emerge_time.dat"
FULL_TIME="full_time.dat"

PDEPA_TIME_STAT="pdepa_time.txt"
EMERGE_TIME_STAT="emerge_time.txt"
FULL_TIME_STAT="full_time.txt"

PDEPA_LOAD="pdepa_load.dat"
PDEPA_LOAD_STAT="pdepa_load.txt"

INCOMPLETE_EMERGE="emerge_fail.dat"
INCOMPLETE_PDEPA="pdepa_fail.dat"


#########################################
# functions
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
# first, create the feature loaded file
# which gives the order

create_file "${PDEPA_LOAD}"
for i in $(find bench -name "pdepa.out" -printf "%P\n"); do
  N=$(grep '^loaded' "bench/$i" | cut -d' ' -f 3) # the number of loaded features
  N=$(echo "scale=3; ($N * 100) / ${NB_TOTAL_FEATURES}" | bc) # percent of the full set of features
  echo "$(dirname $i) $N" >> "${PDEPA_LOAD}"
done
sort -t' ' -k 2 -g -o "${PDEPA_LOAD}" "${PDEPA_LOAD}"
LIST=$(cut -d' ' -f 1 "${PDEPA_LOAD}")

stat_number "$PDEPA_LOAD" "$PDEPA_LOAD_STAT" 2

# add the column names to the file
sed -i '1i name number' "${PDEPA_LOAD}"


#########################################
# second, create the time files

# first, create the file for pdepa, since it is used as reference for the emerge file
create_file "${PDEPA_TIME}"
for i in $LIST; do
  T=$(get_time "bench/$i/pdepa.out")
  echo "$(dirname $i) $T" >> "${PDEPA_TIME}"
done

# third, generate the emerge file
create_file "$EMERGE_TIME"
for i in $LIST; do
  T=$(get_time "bench/$i/emerge.out")
  echo "$i $T" >> "${EMERGE_TIME}"
done

stat_number "$PDEPA_TIME" "$PDEPA_TIME_STAT" 2
stat_number "$EMERGE_TIME" "$EMERGE_TIME_STAT" 2

# add the column names to the files
sed -i '1i name time' "${PDEPA_TIME}"
sed -i '1i name time' "${EMERGE_TIME}"


#########################################
# third, check emerge completeness

create_file "${INCOMPLETE_EMERGE}"
create_file "${INCOMPLETE_PDEPA}"
for i in $LIST; do
  EFAIL='nan'
  # ! [ebuild    => emerge does not try to install anything
  # REQUIRED_USE => emerge complains about the REQUIRED_USE not being set
  # dependency .* conflict  => emerge found a slot conflict and cannot proceed
  # conflict and not slot   => emerge found a conflict not linked to a slot
  if ! grep -q '^\[ebuild' "bench/$i/emerge.out" || grep -q 'REQUIRED_USE\|dependency .* conflict' "bench/$i/emerge.out" ; then
    EFAIL='1'
  else
    TMP=$(grep 'confict' "bench/$i/emerge.out")
    if [ "$TMP" != "" ] && { echo "$TMP" | grep -q -v 'slot' ; }; then
      EFAIL='1'
    fi
  fi
  echo "$i $EFAIL" >> "${INCOMPLETE_EMERGE}"

  if [ "$(cat "bench/$i/pdepa.res")" = "success" ]; then
    echo "$i nan" >> "${INCOMPLETE_PDEPA}"
  else
    echo "$i -1" >> "${INCOMPLETE_PDEPA}"
  fi
done

# add the column names to the files
sed -i '1i name fail' "${INCOMPLETE_PDEPA}"
sed -i '1i name fail' "${INCOMPLETE_EMERGE}"


#########################################
# fourth, do the tests on full
LIST=($LIST) # get an array so we have direct lookup
MAX_J=$((${NB_TEST_FULL} - 1))
MAX_E=$((${NB_TEST_ALL} - 1))

rm $(find "bench" -name "full.???")
create_file "$FULL_TIME"
for j in $(seq 0 "${MAX_J}"); do
  k=$(echo "(($j * ${MAX_E} * 10) + 5) / (${MAX_J} * 10)" | bc)
  i="${LIST[$k]}"
  { time  python statistics.py check -u -m $(cat "bench/$i/list.txt") ; } &> "bench/$i/full.out"
  { [ "$?" -eq '0' ] && echo "success" || echo "fail" ; } > "bench/$i/full.res"
  T=$(get_time "bench/$i/full.out")
  echo "$i $((k + 1)) $T" >> "${FULL_TIME}"
done

stat_number "$FULL_TIME" "$FULL_TIME_STAT" 3

# add the column names to the file
sed -i '1i name index time' "${FULL_TIME}"

