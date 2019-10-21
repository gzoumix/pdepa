#!/usr/bin/python

__author__     = "Michael Lienhardt"
__copyright__  = "Copyright 2019-2020, Michael Lienhardt"
__license__    = "GPL3"
__version__    = "1"
__maintainer__ = "Michael Lienhardt"
__email__      = "michael.lienhardt@onera.fr"
__status__     = "Prototype"


import os
import argparse

import pandas as pd
import matplotlib.pyplot as plt


header_load_dat = ('id', 'percent')
header_time_dat = ('id', 'time')
header_fail_dat = ('id', 'index', 'is_fail')
header_stat = ('name', 'val')

load_files = ("pdepa_load",)
time_files = ("pdepa_time", "emerge_time", "full_time")
fail_files = ("emerge_fail", "pdepa_fail", "common_fail")

converters = {'percent': float, 'time': float, 'index': int, 'is_fail':int, 'val':float}

BENCHDIR = "bench"
SAVEDIR = os.path.join(os.getenv("HOME"), 'Downloads')


def load_table(name, ext, header):
  res = pd.read_csv(os.path.join(BENCHDIR, f"{name}.{ext}"), header=None, sep=' ', names=header, converters=converters)
  res.set_index(header[0], inplace=True)
  return res

def setup_tables():
  load_tables = { name: ( load_table(name, 'dat', header_load_dat), load_table(name, 'txt', header_stat) ) for name in load_files}
  time_tables = { name: ( load_table(name, 'dat', header_time_dat), load_table(name, 'txt', header_stat) ) for name in time_files}
  fail_tables = { name: load_table(name, 'dat', header_fail_dat) for name in fail_files}

  return load_tables, time_tables, fail_tables


def get_stat_info(table_stat):
  mean = table_stat.at['mean','val']
  deviation = table_stat.at['deviation','val']
  val_min = table_stat.at['min','val']
  val_max = table_stat.at['max','val']
  return mean, deviation, val_min, val_max

def save_table(name, column, table_pair):
  time_table, stat_table = table_pair
  time_table[column].plot(legend=True)
  mean, deviation, val_min, val_max = get_stat_info(stat_table)
  plt.axhspan(mean - deviation, mean + deviation, color='#ffaaff77' )
  plt.axhline(mean, color='r', linestyle='--')
  plt.axhline(val_min, color='b', linestyle='--')
  plt.axhline(val_max, color='b', linestyle='--')
  plt.yticks((val_min, mean, val_max))
  plt.savefig(os.path.join(SAVEDIR,f"{BENCHDIR}_{name}.svg"), format='svg')
  plt.clf()


def save_fail(last_idx, fail_tables):
  df = pd.DataFrame()
  for name, table in fail_tables.items():
    table.set_index('index', inplace=True)
    table.sort_index(inplace=True)
    table[name] = table['is_fail']
    if(df.empty): df = table[[name]]
    else: df = df.join(table[name])
  df.plot.bar()
  plt.yticks((0,1))
  plt.xticks(tuple(plt.xticks()[0]) + (last_idx,))
  plt.savefig(os.path.join(SAVEDIR,f"{BENCHDIR}_fail.svg"), format='svg')
  plt.clf()


def main_manage_parameter():
  global BENCHDIR

  parser = argparse.ArgumentParser()
  parser.add_argument('benchdir', nargs='?', default=BENCHDIR)
  args = parser.parse_args()
  BENCHDIR = args.benchdir


if(__name__ == "__main__"):
  main_manage_parameter()
  load_tables, time_tables, fail_tables = setup_tables()

  for name, table_pair in load_tables.items():
    save_table(name, 'percent', table_pair)

  for name, table_pair in time_tables.items():
    save_table(name, 'time', table_pair)

  last_idx = len(load_tables[load_files[0]][0]) - 1
  save_fail(last_idx, fail_tables)




