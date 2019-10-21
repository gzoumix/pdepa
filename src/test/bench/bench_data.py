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
import matplotlib.patches as mpatches


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


global_size = None
global_xticks = None
nb_xticks = 6

def compute_xticks():
  global global_size
  global global_xticks
  global nb_xticks
  last_idx = global_size - 1
  global_xticks = tuple(round((last_idx*nb) / (nb_xticks-1)) for nb in range(nb_xticks))


def load_table(name, ext, header):
  res = pd.read_csv(os.path.join(BENCHDIR, f"{name}.{ext}"), header=None, sep=' ', names=header, converters=converters)
  return res

def setup_tables():
  load_tables = { name: ( load_table(name, 'dat', header_load_dat), load_table(name, 'txt', header_stat) ) for name in load_files}
  time_tables = { name: ( load_table(name, 'dat', header_time_dat), load_table(name, 'txt', header_stat) ) for name in time_files}
  fail_tables = { name: load_table(name, 'dat', header_fail_dat) for name in fail_files}

  global global_size
  global_size = len(load_tables[load_files[0]][0])
  compute_xticks()

  return load_tables, time_tables, fail_tables


def get_stat_info(table_stat):
  table_stat.set_index('name', inplace=True)
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

  # yticks
  plt.yticks((val_min, mean, val_max))
  # xticks
  global global_xticks
  plt.xticks(global_xticks)

  print(f"saving file {BENCHDIR}_{name}.svg: ticks = {plt.xticks()[0]}")

  plt.savefig(os.path.join(SAVEDIR,f"{BENCHDIR}_{name}.svg"), format='svg')

  plt.clf()


def create_fail_table(fail_tables):
  global global_size
  # create the data
  data = {name.split('_')[0]: [0 for i in range(global_size)] for name in fail_tables.keys()}
  for name, table in fail_tables.items():
    name = name.split('_')[0]
    table.set_index('index', inplace=True)
    table.sort_index(inplace=True)
    for idx, v in table['is_fail'].items(): data[name][idx] = v
  # return the table
  return pd.DataFrame(data=data)

def save_fail_old(fail_tables):
  # create and display the table
  df = create_fail_table(fail_tables)
  df.plot.bar()

  # yticks
  #plt.yticks((0,1))
  # xticks
  global global_xticks
  plt.xticks(global_xticks)

  print(f"saving file {BENCHDIR}_fail.svg: ticks = {plt.xticks()[0]}")

  plt.savefig(os.path.join(SAVEDIR,f"{BENCHDIR}_fail.svg"), format='svg')
  plt.clf()


def save_fail(fail_tables):
  handles_fail = []
  handles_nofail = []

  for name, table in fail_tables.items():
    name = name.split('_')[0]
    data = sorted(table['index'].values)
    if(data): handles_fail.append(plt.bar(data, height=1, label=name))
    else: handles_nofail.append(mpatches.Patch(color='none', label=f"{name}: no failure"))

  global global_xticks
  plt.xticks(global_xticks)
  
  plt.legend(handles=handles_fail + handles_nofail)
  plt.savefig(os.path.join(SAVEDIR,f"{BENCHDIR}_fail.svg"), format='svg')


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

  save_fail(fail_tables)




