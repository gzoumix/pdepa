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
  config = repo.repository.config(use_enum.use_all, mask_enum.mask_all, None)
  def __init__(self):
    self._repo = repo.repository(analyser.config)
    self._common_features = self._repo._fixed_iuse
    self._all_features = None
    self._fm = None
    self._solution = None

  def load_all_cpv(self):
    self._fm = []
    self._all_features = set()
    all_cp = portage.portdb.cp_all()
    for cp in all_cp:
      self._fm.append( (cp, self._repo.get_cp(cp)) )
      for cpv in self._repo.get_atom(cp):
        p = self._repo.get_package(cpv)
        self._all_features.update(p._use_map.values())
        self._fm.append( (p._name, p.get_spc()) )

  def test_solve(self, cp):
    z3_translator = gzl.toZ3Visitor().visit
    z3_solver = z3.Solver()
    z3_solver.add(z3_translator(gzl.Or(self._repo.get_atom(cp))))
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
  parser.add_argument("package", nargs='?', help="the list of packages to install. For more flexibility, every element of the list can follow the DEPEND syntax")
  args = parser.parse_args()

  cpv = args.package
  if(cpv is None): print("TODO: load the portage feature model and translate it into CNF form")
  else: print("TODO: load the portage feature model and check dependencies of cp: {}".format(cpv))

  test = analyser()
  begin = time.time()
  test.load_all_cpv()
  end = time.time()
  print("load took {}s".format(end - begin))
  print(" loaded {} cp".format(len(test._repo._cps)))
  print(" and {} packages".format(len(test._repo._packages)))
  print(" with {} features (among which {} are shared)".format(len(test._all_features), len(test._common_features)))
  if(cpv is None):
    begin = time.time()
    test.write_fm("portage.cnf")
    end = time.time()
    print("translated the portage feature model and wrote the file in {}s".format(end - begin))
  else:  
    begin = time.time()
    test.test_solve(cpv)
    end = time.time()
    print("found {} for dependency solving of {} in {}s".format(("an error" if(test._solution is None) else "a solution"), cpv, end - begin))
