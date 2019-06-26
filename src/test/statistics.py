#!/usr/bin/python

__author__ = "Michael Lienhardt"
__copyright__ = "Copyright 2019, Michael Lienhardt"
__license__ = "GPL3"
__version__ = "1"
__maintainer__ = "Michael Lienhardt"
__email__ = "michael lienhardt@onera.fr"
__status__ = "Prototype"

import time

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

  def test_solve(self, cpv):
    z3_translator = gzl.toZ3Visitor().visit
    z3_solver = z3.Solver()
    z3_solver.add(z3_translator(cpv))
    for cp_,c in self._fm:
      print("loading fm from {}".format(cp_))
      z3_solver.add(z3_translator(c))
    if(z3_solver.check() == z3.sat): self._solution = z3_solver.model()
    else: self._solution = None




if(__name__ == '__main__'):
  cpv = 'kde-plasma/plasma-meta-5.15.5'
  test = analyser()
  begin = time.time()
  test.load_all_cpv()
  end = time.time()
  print("load took {}s".format(end - begin))
  print(" loaded {} cp".format(len(test._repo._cps)))
  print(" and {} packages".format(len(test._repo._packages)))
  print(" with {} features (among which {} are shared)".format(len(test._all_features), len(test._common_features)))
  begin = time.time()
  test.test_solve(cpv)
  end = time.time()
  print("found {} for dependency solving of {} in {}s".format(("an error" if(test._solution is None) else "a solution"), cpv, end - begin))
