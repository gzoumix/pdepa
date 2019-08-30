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
sys.path.append(os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))), 'main'))
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

  def print_fm(self):
    c = gzl.And(*tuple(el[1] for el in self._fm))
    converter = analyser.toCNFConverter()
    converter.convert(c)
    print(str(converter))

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

self_program_name = None
def main_manage_parameter():
  parser = argparse.ArgumentParser()
  parser.set_defaults(cmd=None)
  subparsers = parser.add_subparsers()

  common_parser = argparse.ArgumentParser()
  common_parser.add_argument("-U", "--explore-use", type=use_enum, choices=list(use_enum), default=None, const=use_enum.use_all, nargs='?', action='store', help="allow the tool to set use flags")
  common_parser.add_argument("-M", "--explore-mask", type=mask_enum, choices=list(mask_enum), default=None, const=mask_enum.mask_all, nargs='?', action='store',  help="allow the tool to unmask packages")
  common_parser.add_argument("-C", "--explore-installed", type=installed_enum, choices=list(installed_enum), default=None, const=installed_enum.inst_all, nargs='?', action='store', help="allow the tool to also consider the installed packages in its dependency computation")
  common_parser.add_argument("-v", "--verbose", action="count", default=0, help="increase tool verbosity")
  common_parser.add_argument("--", dest="sep", help="separator between the option and the list of packages")

  dep_parser = subparsers.add_parser('check', parents=[common_parser], add_help=False)
  dep_parser.set_defaults(cmd='check')
  dep_parser.add_argument("package", nargs='+', help="the cp to install")
  dep_parser.add_argument("-d", action="store_true",  help="load only the dependencies of the cp to install, instead of the whole feature model")

  cnf_parser = subparsers.add_parser('cnf', parents=[common_parser], add_help=False)
  cnf_parser.set_defaults(cmd='cnf')

  #
  global self_program_name
  self_program_name = parser.prog

  args = parser.parse_args()
  #print("config: {} {} {} {} {}".format(args.explore_use, args.explore_mask, args.explore_installed, args.optimize, args.verbose))

  repo_conf = repo.repository.config(args.explore_use, args.explore_mask, args.explore_installed)
  return args.verbose, repo_conf, args.cmd, args



if(__name__ == '__main__'):
  verbose, repo_conf, cmd, args = main_manage_parameter()
  test = analyser(repo_conf)

  def statistics_load(f):
    begin = time.time()
    f()
    end = time.time()
    print("load took {}s".format(end - begin))
    print(" loaded {} cp".format(len(test._repo._cps)))
    print(" and {} packages".format(len(test._repo._packages)))
    print(" with {} features (among which {} are shared)".format(len(test._all_features), len(test._common_features)))


  if(cmd == "cnf"): # print the CNF of the whole feature model
    test.load_all_cpv()
    test.print_fm("portage.cnf")
  elif(cmd == "check"): # test installation of cp
    cps = args.package
    config = None

    if(args.d): f = lambda: test.load_deps(cps)
    else: f = test.load_all_cpv
    statistics_load(f)
    begin = time.time()
    test.test_solve(cps)
    end = time.time()
    print("found {} for dependency solving of {} in {}s".format(("an error" if(test._solution is None) else "a solution"), cps, end - begin))
    if(test._solution is None): exit(1)
    else: exit(0)
  else: raise Exception("bad arguments")
