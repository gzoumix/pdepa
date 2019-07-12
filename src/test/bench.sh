#!/bin/bash

# should be tested with: sys-auth/polkit dev-vcs/git dev-util/pycharm-community www-servers/apache x11-base/xorg-server gnome-base/gnome kde-plasma/plasma-meta xfce-base/xfce4-meta www-client/firefox net-im/pidgin media-video/vlc

PDEDADIR=../main/
BENCHDIR=bench

# setup the bench repository
#[ -e "${BENCHDIR}" ] && rm -r "${BENCHDIR}"
#mkdir "${BENCHDIR}"

PYTHONPATH="$PYTHONPATH:$(pwd)/../main"

for i in "$@"; do
  #cp="$(dirname "$i")-$(basename "$i")"
  mkdir -p "${BENCHDIR}/$i"
  # emerge
  { time emerge -p --autounmask y --autounmask-continue y --autounmask-backtrack y "$i" ; } &> "${BENCHDIR}/$i/emerge.out"
  { [ "$?" -eq '0' ] && echo "success" || echo "fail" ; } > "${BENCHDIR}/$i/emerge.res"
  # analysis
  { time python statistics.py check -du  "$i" ; } &> "${BENCHDIR}/$i/dep.out"
  { [ "$?" -eq '0' ] && echo "success" || echo "fail" ; } > "${BENCHDIR}/$i/dep.res"
  # pdepa
  { time  python ../main/pdepa.py -U -C -p --  "$i" ; } &> "${BENCHDIR}/$i/pdepa.out"
  { [ "$?" -eq '0' ] && echo "success" || echo "fail" ; } > "${BENCHDIR}/$i/pdepa.res"
done

