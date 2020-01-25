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
import math

import pandas as pd
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches

from matplotlib import style
# style.use('ggplot')



color_map_simple = {
  'feature_loaded_pct': { 'main':'darkorange', 'std':'bisque', 'mean':'burlywood', 'extreme':'orange'},
  'emerge_time': { 'main':'dodgerblue', 'std':'lightskyblue', 'mean':'deepskyblue', 'extreme':'steelblue'},
  'pdepa_time': { 'main':'dodgerblue', 'std':'lightskyblue', 'mean':'deepskyblue', 'extreme':'steelblue'},
  'standard_time': { 'main':'dodgerblue', 'std':'lightskyblue', 'mean':'deepskyblue', 'extreme':'steelblue'},
  'emerge_memory': { 'main':'dodgerblue', 'std':'lightskyblue', 'mean':'deepskyblue', 'extreme':'steelblue'},
  'pdepa_memory': { 'main':'dodgerblue', 'std':'lightskyblue', 'mean':'deepskyblue', 'extreme':'steelblue'},
  'standard_memory': { 'main':'dodgerblue', 'std':'lightskyblue', 'mean':'deepskyblue', 'extreme':'steelblue'},
}
color_map_failure = {
  'emerge_success':'lightblue',
  'pdepa_success':'red',
  'standard_success':'orange',
}


def save_graph_simple(path, series, stats, xticks, color_map):
  series.plot(legend=True, color=color_map['main'])
  mean, deviation, val_min, val_max = stats['mean'], stats['std'], stats['min'], stats['max']
  plt.axhspan(mean - deviation, mean + deviation, color=color_map['std'] )
  plt.axhline(mean, color=color_map['mean'], linestyle='--')
  plt.axhline(val_min, color=color_map['extreme'], linestyle='--')
  plt.axhline(val_max, color=color_map['extreme'], linestyle='--')
  # plt.axhspan(mean - deviation, mean + deviation, color='#ffaaff77' )
  # plt.axhline(mean, color='r', linestyle='--')
  # plt.axhline(val_min, color='b', linestyle='--')
  # plt.axhline(val_max, color='b', linestyle='--')

  # yticks
  plt.yticks((val_min, mean, val_max))
  plt.xticks(xticks)

  print(f"saving file {path}: ticks = {plt.xticks()[0]}")

  plt.savefig(path, format='svg')
  plt.clf()


def save_graph_fail(path, series_list, color_map):
  pass




converter_success = lambda x: int(x == 'False')
converters = {
  'TEST': str,
  'emerge_time': float, 'emerge_memory': float, 'emerge_success': converter_success,
  'pdepa_time': float, 'pdepa_memory': float, 'pdepa_success': converter_success,
  'standard_time': float, 'standard_memory': float, 'standard_success': converter_success,
  'feature_full':int, 'feature_loaded':int
}

column_sum = frozenset( ('emerge_time', 'pdepa_time', 'standard_time', 'emerge_memory', 'pdepa_memory', 'standard_memory', 'feature_loaded', 'emerge_success', 'pdepa_success', 'standard_success', ) )
column_compare = frozenset( ('feature_full', ) )

# column_sum = frozenset( ('emerge_time', 'pdepa_time', 'pdepa_alt_time', 'feature_loaded', ) )
# column_compare = frozenset( ('emerge_success', 'pdepa_success', 'pdepa_alt_success', 'feature_full') )

column_graph_simple = {
  'feature_loaded_pct':'feature loaded percent',
  'emerge_time':'emerge time', 'pdepa_time':'pdepa time', 'standard_time':'standard approach time',
  'emerge_memory':'emerge memory', 'pdepa_memory':'pdepa memory', 'standard_memory':'standard approach memory',
}
column_graph_failure = {
  'emerge_success':'emerge failure', 'pdepa_success':'pdepa failure', 'standard_success':'standard approach failure',  
}

def main_manage_parameter():

  parser = argparse.ArgumentParser()
  parser.add_argument('-d', '--dir', default=".", help="the directory in which to store the statistics")
  parser.add_argument('-n', '--nb_xticks', default=6, type=int, help="the number of x ticks in the generated graphs")
  parser.add_argument('benchdir', nargs='+', help="the directories where to find the bench data in table.csv")
  args = parser.parse_args()
  save_path = os.path.abspath(args.dir)
  nb_xticks = args.nb_xticks
  benchs = tuple(pd.read_csv(os.path.join(path, 'table.csv'), sep=' ', converters=converters, index_col='TEST') for path in args.benchdir)
  return save_path, nb_xticks, benchs


if(__name__ == "__main__"):
  save_path, nb_xticks, benchs = main_manage_parameter()
  bench_nb = len(benchs)

  # 1. get the global statistics
  bench_full = pd.concat(benchs, ignore_index=True)
  bench_full['feature_loaded_pct'] = (100 * bench_full['feature_loaded']) / bench_full['feature_full']
  stats = { column: bench_full[column].describe() for column in column_graph_simple.keys() }
  pd.DataFrame(stats).to_csv(path_or_buf=os.path.join(save_path, 'stats.txt'), index=True, sep=' ', header=True)


  # 2. combine all the benchs
  if(bench_nb > 1):
    bench_main = benchs[0].copy()
    for bench in benchs[1:]:
      for column, series in bench.items():
        if(column in column_sum): bench_main[column] += series
        elif(column in column_compare):
          if(not bench_main[column].equals(series)): raise Exception(f"Difference on column {column}")
        else: raise Exception(f"Unknown column {column}")
    for column in column_sum:
      bench_main[column] = bench_main[column] / bench_nb
    bench_main = bench_main.sort_values(by=['feature_loaded']).reset_index()
    feature_nb = bench_main['feature_full'][0]
    bench_main['feature_loaded_pct'] = (100 * bench_main['feature_loaded']) / feature_nb

    bench_main.to_csv(path_or_buf=os.path.join(save_path, 'table.csv'), index=False, sep=' ', header=True)

    # 2.2. also save the statistics between benches
    benchs_stds = {'COLUMN':[], 'std':[], 'min':[], 'max':[],}
    for column in column_sum:
      column_count = benchs[0][column].count()
      column_stat = pd.DataFrame({i:benchs[i][column] for i in range(bench_nb)}).transpose().describe().transpose()
      column_std = column_stat['std']
      benchs_stds['COLUMN'].append(column)
      benchs_stds['std'].append(math.sqrt((column_std**2).sum()/column_count))
      benchs_stds['min'].append(column_std.min())
      benchs_stds['max'].append(column_std.max())
    benchs_stds = pd.DataFrame(benchs_stds).set_index('COLUMN')
    benchs_stds.loc['feature_loaded_pct'] = (100 * benchs_stds.loc['feature_loaded']) / feature_nb
    benchs_stds.to_csv(path_or_buf=os.path.join(save_path, 'bench_stds.csv'), index=True, sep=' ', header=True)
  else:
    bench_main = benchs[0]
    bench_main = bench_main.sort_values(by=['feature_loaded']).reset_index()
    feature_nb = bench_main['feature_full'][0]
    bench_main['feature_loaded_pct'] = (100 * bench_main['feature_loaded']) / feature_nb


  # 4. print the graphs
  bench_main['TEST'].to_csv(path_or_buf=os.path.join(save_path, 'order.txt'), index=False, sep=' ', header=False)
  test_nb = bench_main.shape[0]
  xticks = tuple(round((test_nb*nb) / (nb_xticks-1)) for nb in range(nb_xticks))
  print(test_nb, xticks)
  for column, name in column_graph_simple.items():
    path = os.path.join(save_path, f"{column}.svg")
    series = bench_main[column].rename(name)
    save_graph_simple(path, series, stats[column], xticks, color_map_simple[column])
  
  bench_failure = bench_main[list(column_graph_failure.keys())].rename(columns=column_graph_failure)
  bench_failure.plot.bar()
  plt.xticks(xticks)
  path = os.path.join(save_path, 'failure.svg')
  print(f"saving file {path}: ticks = {plt.xticks()[0]}")
  plt.savefig(path, format='svg')
  plt.clf()


