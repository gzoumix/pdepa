#!/usr/bin/python

__author__ = "Michael Lienhardt"
__copyright__ = "Copyright 2019, Michael Lienhardt"
__license__ = "GPL3"
__version__ = "1"
__maintainer__ = "Michael Lienhardt"
__email__ = "michael lienhardt@onera.fr"
__status__ = "Prototype"

import time

import portage

import sys
import os
sys.path.append(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'main'))
import package.repository as repo


use_enum = repo.repository.config.exp_use
mask_enum = repo.repository.config.exp_mask
installed_enum = repo.repository.config.exp_installed


class analyser(object):
  config = repo.repository.config(use_enum.use_all, mask_enum.mask_all, None)
  def __init__(self):
    self._repo = repo.repository(analyser.config)
    self._common_features = self._repo._fixed_iuse

  def load_all_cpv(self):
    constraint = []
    features = set()
    all_cp = portage.portdb.cp_all()
    for cp in all_cp:
      constraint.append(self._repo.get_cp(cp))
      for cpv in self._repo.get_atom(cp):
        p = self._repo.get_package(cpv)
        features.update(p._iuse_declared)
        constraint.append(p.get_spc())
    return features, constraint

if(__name__ == '__main__'):
  test = analyser()
  begin = time.time()
  features, constraint = test.load_all_cpv()
  end = time.time()
  print("load took {}s".format(end - begin))
  print(" loaded {} cp".format(len(test._repo._cps)))
  print(" and {} packages".format(len(test._repo._packages)))
  print(" with {} features (among which {} are shared)".format(len(features), len(test._common_features)))
