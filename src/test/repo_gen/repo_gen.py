#!/usr/bin/python

__author__     = "Jacopo Mauro & Michael Lienhardt"
__copyright__  = "Copyright 2019-2020, Michael Lienhardt"
__license__    = "GPL3"
__version__    = "1"
__maintainer__ = "Michael Lienhardt"
__email__      = "michael.lienhardt@onera.fr"
__status__     = "Prototype"

import os
import argparse
import time
import subprocess
import tempfile
import random


def get_package_name(category, package_id, with_category=True):
  """
  This function returns the name of a package from its id, possibly with its category.
  Parameters:
    category (str): the category of the package
    package_id (int): the id of the package
    with_categoryt (bool): if the category is included in the name or not
  Returns: the name of the package
  """
  if(with_category): return f"{category}/package_{package_id}"
  else: return f"package_{package_id}"


package_model = """
EAPI=6
DESCRIPTION="{}"
SLOT="0"
KEYWORDS="amd64 sh sparc x86"
IUSE="{}"
REQUIRED_USE="{}"
DEPEND="{}"
"""

def generate_package(package_id, config):
  """
  This function generates the ebuild file of the package id in parameter.
  Parameters:
    package_id (int): the id of the package to generate
    config (object): the repository configuration from the user input (created by argparse)
  Returns: the string of the ebuild of the package
  """
  # 1. find the number of features in the package, the length of its REQUIRED_USE, and the number of its dependencies
  nb_features = random.randrange(config.vmin, config.vmax+1)
  nb_clauses  = random.randrange(config.cmin, config.cmax+1)
  nb_shared   = random.randrange(config.smin, config.smax+1)

  # 2. run the tool that generates the constraint that will become the REQUIRED_USE
  cmd = config.cmd_core + ("-v", str(nb_features), "-c", str(nb_clauses),)
  process = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
  stdout, stderr = process.communicate()

  # 3. the description of the package
  description = f"package {package_id}, with {nb_features} features, {nb_clauses} clauses and {nb_shared} shared features"
  # 4. the iuse of the package
  iuse = ' '.join([f"f_{i}" for i in range(1, nb_features+1)])
  # 5. the required_use of the package
  lines = ()
  with open(config.tempfile, 'r') as f:
    lines = f.readlines()
  lines = [ [int(i) for i in line.split(' ')[:-1]] for line in lines[1:] ]
  lines = [ [(f"!f_{-i}" if(i<0) else f"f_{i}") for i in line] for line in lines ]
  required_use = ' '.join([ f"|| ( {' '.join(line)} )" for line in lines ])
  # 6. the dependencies of the package
  conditions = random.choices(range(1, nb_features+1), k=nb_shared)
  dependencies = random.choices(tuple(get_package_name(config.repo_name, pid) for pid in range(package_id)) + tuple(get_package_name(config.repo_name, pid) for pid in range(package_id+1, config.nb_package)), k=nb_shared)
  depend = ' '.join(f"f_{cond}? ( {dep} )" for cond, dep in zip(conditions, dependencies))

  return package_model.format(description, iuse, required_use, depend)


makefile_model = """
# author     = "Michael Lienhardt"
# copyright  = "Copyright 2019-2020, Michael Lienhardt"
# license    = "GPL3"
# version    = "1"
# maintainer = "Michael Lienhardt"
# email      = "michael.lienhardt@onera.fr"
# status     = "Prototype"

LOCAL_DIR:="$(shell pwd)"
REPO_NAME:={}
MANIFESTS:={}

LOCATION_ROOT:="/etc/portage"
# LOCATION_ROOT:=.
LOCATION_CATEGORIES:=${{LOCATION_ROOT}}/categories
LOCATION_CATEGORIES_ORIGINAL:=${{LOCATION_CATEGORIES}}.original
LOCATION_REPOS:=${{LOCATION_ROOT}}/repos.conf
LOCATION_REPOS_ORIGINAL:=${{LOCATION_REPOS}}.original

install: categories_no_original categories_original repos_no_original repos_original setup_portage_conf ${{MANIFESTS}}

clean:
	rm ${{LOCATION_CATEGORIES}}
	mv ${{LOCATION_CATEGORIES_ORIGINAL}} ${{LOCATION_CATEGORIES}}
	rm ${{LOCATION_REPOS}}
	mv ${{LOCATION_REPOS_ORIGINAL}} ${{LOCATION_REPOS}}
	rm ${{LOCATION_ROOT}}/make.conf
	mv ${{LOCATION_ROOT}}/make.conf.original ${{LOCATION_ROOT}}/make.conf
	rm ${{LOCATION_ROOT}}/make.profile
	mv ${{LOCATION_ROOT}}/make.profile.original ${{LOCATION_ROOT}}/make.profile

categories_no_original:
ifneq (,$(wildcard ${{LOCATION_CATEGORIES_ORIGINAL}}))
	$(error ERROR: ${{LOCATION_CATEGORIES_ORIGINAL}} already exists)
endif

categories_original:
ifneq (,$(wildcard "${{LOCATION_CATEGORIES}}"))
	mv "${{LOCATION_CATEGORIES}}" "${{LOCATION_CATEGORIES_ORIGINAL}}"
else
	echo > "${{LOCATION_CATEGORIES_ORIGINAL}}"
endif


repos_no_original:
ifneq (,$(wildcard ${{LOCATION_REPOS_ORIGINAL}}))
	$(error ERROR: ${{LOCATION_REPOS_ORIGINAL}} already exists)
endif

repos_original:
ifneq (,$(wildcard "${{LOCATION_REPOS}}"))
	mv "${{LOCATION_REPOS}}" "${{LOCATION_REPOS_ORIGINAL}}"
else
	echo > "${{LOCATION_REPOS_ORIGINAL}}"
endif

setup_portage_conf: profiles/repo_name profiles/default/eapi profiles/default/make.defaults metadata/layout.conf
	echo ${{REPO_NAME}} > "${{LOCATION_CATEGORIES}}"
	echo [DEFAULT] >> ${{LOCATION_REPOS}}
	echo main-repo = ${{REPO_NAME}} >> ${{LOCATION_REPOS}}
	echo  >> ${{LOCATION_REPOS}}
	echo [${{REPO_NAME}}] >> ${{LOCATION_REPOS}}
	echo location = ${{LOCAL_DIR}} >> ${{LOCATION_REPOS}}
	echo masters= >> ${{LOCATION_REPOS}}
	echo auto-sync = no >> ${{LOCATION_REPOS}}
	mv ${{LOCATION_ROOT}}/make.conf ${{LOCATION_ROOT}}/make.conf.original
	touch ${{LOCATION_ROOT}}/make.conf
	mv ${{LOCATION_ROOT}}/make.profile ${{LOCATION_ROOT}}/make.profile.original
	ln -s ${{LOCAL_DIR}}/profiles/default ${{LOCATION_ROOT}}/make.profile

profiles/repo_name:
	mkdir -p profiles
	echo ${{REPO_NAME}} > profiles/repo_name

profiles/default/eapi:
	mkdir -p profiles/default
	echo 6 > profiles/default/eapi
	echo >> profiles/default/eapi

profiles/default/make.defaults:
	mkdir -p profiles/default
	echo 'ARCH="amd64"' > profiles/default/make.defaults
	echo 'ACCEPT_KEYWORDS="$${{ARCH}}"' >> profiles/default/make.defaults
	echo  >> profiles/default/make.defaults

metadata/layout.conf:
	mkdir -p metadata
	echo masters= > metadata/layout.conf

%/Manifest:
	cd $(shell dirname $@) ; ebuild *.ebuild manifest
"""

def generate_makefile(config):
  """
  This function generates the text of the Makefile that install/desinstall the repo to/from gentoo
  Paraemters:
    config (object):the repository configuration from the user input (created by argparse)
  Returns: the string of the Makefile
  """
  manifests = ' '.join([f"{get_package_name(config.repo_name, package_id)}/Manifest" for package_id in range(config.nb_package)])
  return makefile_model.format(config.repo_name, manifests)


def main_manage_parameter():
  """
  This function declares and manages the different option of this executable.
  Returns: the repository configuration from the user input
  """
  parser = argparse.ArgumentParser()
  parser.add_argument('-d', '--dir', default=None, help="the directory in which to store the repo")
  parser.add_argument('--exec_path', default="Power-Law-Random-SAT-Generator/CreateSAT", help="path to the CreateSAT executable")
  parser.add_argument('-n', '--nb_package', default=6, type=int, help="the number of packages in the generated repository")
  parser.add_argument('-g', default="p", choices=["p", "d", "u"], help="choose between power-law distributed variables (p) or double power-law (d) or uniform (u)")
  parser.add_argument('--vmin', type=int, default=1, help="the minimal number of features in a package")
  parser.add_argument('--vmax', type=int, default=1, help="the maximal number of features in a package")
  parser.add_argument('--cmin', type=int, default=1, help="the minimal number of clauses / scaling factor in the REQUIRED_USE of a package")
  parser.add_argument('--cmax', type=int, default=1, help="the maximal number of clauses / scaling factor in the REQUIRED_USE of a package")
  parser.add_argument('--smin', type=int, default=1, help="the minimal number of dependencies in the DEPEND of a package")
  parser.add_argument('--smax', type=int, default=1, help="the maximal number of dependencies in the DEPEND of a package")
  parser.add_argument('-k', type=int,  default=1, help="for double power-law only: this is the average clause length")
  parser.add_argument('-b', type=int,  default=1, help="for double power-law only: power-law exponent of clauses")
  parser.add_argument('-p', type=int,  default=1, help="<power-law exponent of variables>")
  parser.add_argument('-u', type=bool, default=False, help="should variables be unique per clause (True) or not (False)")
  parser.add_argument('-q', type=int,  default=1, help="start quietly")
  parser.add_argument('-s', type=int, help="seed value (int), system time is used if none is given")
  parser.add_argument('repo_name', help="the name of the repository")
  args = parser.parse_args()

  # setup the system with the user input
  random.seed(args.s)
  if(args.dir is None): args.dir = args.repo_name
  args.dir_packages = os.path.join(args.dir, args.repo_name)
  os.makedirs(args.dir_packages, exist_ok=True)
  args.tempdir = tempfile.mkdtemp()
  args.tempfile_base = os.path.join(args.tempdir, "constraint")
  args.tempfile = f"{args.tempfile_base}.cnf"

  # create the core command line to execute
  args.cmd_core = (args.exec_path, "-u", ("1" if(args.u) else "0"), "-f", args.tempfile_base, "-g", str(args.g),)
  if(args.g == "p"):   args.cmd_core = args.cmd_core + ("-k", str(args.k), "-b", str(args.b),)
  elif(args.g == "d"): args.cmd_core = args.cmd_core + ("-p", str(args.p),)

  return args


if(__name__ == "__main__"):
  # 1. get the repository configuration from the user input
  config = main_manage_parameter()
  # 2. generates all packages
  for package_id in range(config.nb_package):
    ebuild_txt = generate_package(package_id, config)
    package_name = get_package_name(config.repo_name, package_id, with_category=False)
    dir_package = os.path.join(config.dir_packages, package_name)
    os.mkdir(dir_package)
    with open(os.path.join(dir_package, f"{package_name}-0.ebuild"), 'w') as f:
      f.write(ebuild_txt)

  # 3. cleanup
  if(config.nb_package > 0): os.remove(config.tempfile)
  os.rmdir(config.tempdir)

  # 4. add the Makefile
  with open(os.path.join(config.dir, "Makefile"), 'w') as f:
    f.write(generate_makefile(config))

