#!/usr/bin/python

__author__ = "Michael Lienhardt"
__copyright__ = "Copyright 2019, Michael Lienhardt"
__license__ = "GPL3"
__version__ = "1"
__maintainer__ = "Michael Lienhardt"
__email__ = "michael lienhardt@onera.fr"
__status__ = "Prototype"

import time
import argparse
import random

import z3
import portage

import sys
import os
sys.path.append(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'main'))
import gzoumlib.gzoumLogic as gzl
import package.repository as repo


use_enum = repo.repository.config.exp_use
mask_enum = repo.repository.config.exp_mask
installed_enum = repo.repository.config.exp_installed


class analyser(object):
  config_default = repo.repository.config(None, None, None)
  config_use = repo.repository.config(use_enum.use_all, None, installed_enum.inst_all)
  config_mask = repo.repository.config(None, mask_enum.mask_all, None)
  config_all = repo.repository.config(use_enum.use_all, mask_enum.mask_all, installed_enum.inst_all)
  def __init__(self, config):
    self._repo = repo.repository(config)
    self._common_features = self._repo._fixed_iuse
    self._all_features = set()
    self._loaded_cp = set()
    self._fm = []
    self._solution = None

  def load_all_cpv(self):
    print('all')
    all_cp = portage.portdb.cp_all()
    for cp in all_cp: self.load_cp(cp)

  def load_deps(self, cps):
    for cp in cps:
      added_cpv = self.load_cp(cp)
      deps = { self._repo.get_package(dep)._cp for cpv in added_cpv for dep in self._repo.get_package(cpv)._dep_package }
      for dep in deps: self.load_deps(dep)

  def load_cp(self, cp):
    added_cpv = set()
    if(cp not in self._loaded_cp):
      self._loaded_cp.add(cp)
      self._fm.append( (cp, self._repo.get_cp(cp)) )
      cpvs = self._repo.get_atom(cp)
      added_cpv.update(cpvs)
      for cpv in cpvs:
        p = self._repo.get_package(cpv)
        self._all_features.update(p._use_map.values())
        self._fm.append( (p._name, p.get_spc()) )
    return added_cpv

  def test_solve(self, cps):
    z3_translator = gzl.toZ3Visitor().visit
    z3_solver = z3.Solver()
    z3_solver.add(z3_translator(gzl.And([gzl.Or(self._repo.get_atom(cp)) for cp in cps])))
    for cp_,c in self._fm:
      z3_solver.add(z3_translator(c))
    if(z3_solver.check() == z3.sat): self._solution = z3_solver.model()
    else: self._solution = None

  def write_fm(self, fname):
    c = gzl.And(*tuple(el[1] for el in self._fm))
    converter = analyser.toCNFConverter()
    converter.convert(c)
    with open(fname, 'w') as f:
      f.write(str(converter))

  class toCNFConverter():
    """
    Class that converts a BoolExp expression into a CNF representation, based on the z3 'tseitin-cnf' tactic
    """
    def __init__(self):
      self._cnf = []
      self._var_dict = {}
      self._curr_id = 1

    def convert(self, c):
      """
      Main conversion function
      Parameter:
        c (BoolExp): the boolean expression to translate
      returns a pair of:
        var_id (dict): maps all variables in c into a index into the CNF constraint
        cnf (list of list of int): the CNF constraint, where variables are encoded as positive int, and negation of a variable is encoded as -variable_id
      """
      z3_translator = gzl.toZ3Visitor()
      z3_constraint = z3_translator.visit(c)
      goal = z3.Goal()
      goal.add(z3_constraint)
      tactic = z3.Tactic('tseitin-cnf')
      z3_cnf = tactic(goal)
      self._cnf = []
      self._var_dict = {}
      self._curr_id = 1
      for z3_c in z3_cnf[0]: self.visit_or(z3_c)
      self._var_translation = { k.decl().name(): v_id for k, v_id in self._var_dict.items() }
      return self

    def visit_or(self, el):
      if(el.num_args() > 1):
        res = tuple(map(self.visit_not, el.children()))
      elif(el.num_args() is 1):
        res = (self.visit_not(el),)
      else:
        res = (self.visit_var(el),)
      self._cnf.append(res)

    def visit_not(self, el):
      if(el.num_args() is 1):
        return -1 * self.visit_var(el.children()[0])
      else:
        return self.visit_var(el)

    def visit_var(self, el):
      res = self._var_dict.get(el)
      if(res is None):
        res = self._curr_id
        self._curr_id = self._curr_id + 1
        self._var_dict[el] = res
      return res

    def get_cnf(self): return self._cnf
    def get_var_translation(self): return self._var_translation
    def __str__(self):
      res = "p cnf {} {}\n".format(len(self._var_dict), len(self._cnf))
      for c in self._cnf:
        res = res + "{} 0\n".format(" ".join(map(str, c)))
      return res


if(__name__ == '__main__'):
  parser = argparse.ArgumentParser()
  subparsers = parser.add_subparsers()

  # subparser for the full loading the gentoo feature model and checking the installation of a package category
  dep_parser = subparsers.add_parser('check')
  dep_parser.add_argument("package", nargs='+', help="the cp to install")
  dep_parser.add_argument("-d", action="store_true",  help="load only the dependencies of the cp to install, instead of the whole feature model")
  dep_parser.add_argument("-u", action="store_true",  help="explore use flags")
  dep_parser.add_argument("-m", action="store_true",  help="explore masked packages")

  # subparser for generating a testing bash script
  stat_parser = subparsers.add_parser('stat')
  stat_parser.add_argument("nb_test", default="1000", help="number of test to perform")
  stat_parser.add_argument("max_length", default="1", help="max length of the list")


  args = parser.parse_args()

  def statistics_load(f):
    begin = time.time()
    f()
    end = time.time()
    print("load took {}s".format(end - begin))
    print(" loaded {} cp".format(len(test._repo._cps)))
    print(" and {} packages".format(len(test._repo._packages)))
    print(" with {} features (among which {} are shared)".format(len(test._all_features), len(test._common_features)))


  if((not hasattr(args, 'package')) and (not hasattr(args, 'nb_test'))): # print the CNF of the whole feature model
    test = analyser(analyser.config_all)
    statistics_load(test.load_all_cpv)
    begin = time.time()
    test.write_fm("portage.cnf")
    end = time.time()
    print("translated the portage feature model and wrote the file in {}s".format(end - begin))
  elif(hasattr(args, 'package')): # test installation of cp
    cps = args.package
    config = None
    if(args.u):
      if(args.m): config = analyser.config_all
      else: config = analyser.config_use
    elif(args.m): config = analyser.config_mask
    else: config = analyser.config_default

    test = analyser(config)

    if(args.d): f = lambda: test.load_deps(cps)
    else: f = test.load_all_cpv
    statistics_load(f)
    begin = time.time()
    test.test_solve(cps)
    end = time.time()
    print("found {} for dependency solving of {} in {}s".format(("an error" if(test._solution is None) else "a solution"), cps, end - begin))
    if(test._solution is None): exit(1)
    else: exit(0)
  elif(hasattr(args, 'nb_test')):
    nb_test = int(args.nb_test)
    max_length = int(args.max_length) + 1
    all_cp = portage.portdb.cp_all()
    with open("statistics.sh", 'w') as f:
      f.write("""#!/bin/bash

BENCHDIR=bench
# setup the bench repository
[ -e "${{BENCHDIR}}" ] || mkdir "${{BENCHDIR}}"

PYTHONPATH="$PYTHONPATH:$(pwd)/../main"

i=0
function test {{
  DIR="${{BENCHDIR}}/test_$i"
  i=$((i+1))

  mkdir "${{DIR}}"
  echo "$@" > "${{DIR}}/list.txt"
  # emerge
  #{{ time emerge -p --backtrack=300 --autounmask y --autounmask-keep-keywords y --autounmask-keep-masks y --autounmask-continue y --autounmask-backtrack y "$@" ; }} &> "${{DIR}}/emerge.out"
  {{ time emerge -p --autounmask y --autounmask-continue y --autounmask-backtrack y "$@" ; }} &> "${{DIR}}/emerge.out"
  {{ [ "$?" -eq '0' ] && echo "success" || echo "fail" ; }} > "${{DIR}}/emerge.res"
  # pdepa
  #{{ time  python ../main/pdepa.py -U -C -p --  "$@" ; }} &> "${{DIR}}/pdepa.out"
  {{ time  python ../main/pdepa.py -U -C -M -p --  "$@" ; }} &> "${{DIR}}/pdepa.out"
  {{ [ "$?" -eq '0' ] && echo "success" || echo "fail" ; }} > "${{DIR}}/pdepa.res"
}}

{}
      """.format('\n'.join(['test ' + ' '.join(random.choices(all_cp, k=random.randrange(1,max_length))) for i in range(nb_test)])))


  else: raise Exception("bad arguments")
