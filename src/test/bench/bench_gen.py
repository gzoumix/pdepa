#!/usr/bin/python

__author__ = "Michael Lienhardt"
__copyright__ = "Copyright 2019, Michael Lienhardt"
__license__ = "GPL3"
__version__ = "1"
__maintainer__ = "Michael Lienhardt"
__email__ = "michael lienhardt@onera.fr"
__status__ = "Prototype"

import argparse
import random

import portage

self_program_name = None
def main_manage_parameter():
  parser = argparse.ArgumentParser()
  parser.add_argument("nb_test", default="1000", help="number of test to perform")
  parser.add_argument("max_length", default="10", help="max length of the list")
  #
  global self_program_name
  self_program_name = parser.prog

  args = parser.parse_args()
  return int(args.nb_test), int(args.max_length) + 1


if(__name__ == '__main__'):
  nb_test, max_length = main_manage_parameter()
  all_cp = portage.portdb.cp_all()
  for i in range(nb_test):
    print(' '.join(random.choices(all_cp, k=random.randrange(1,max_length))))

