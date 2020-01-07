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

package_model = """
EAPI=6
DESCRIPTION="{}"
SLOT="0"
KEYWORDS="amd64 sh sparc x86"
IUSE="{}"
REQUIRED_USE="{}"
DEPEND="{}"
"""

def get_package_name(category, package_id, with_category=True):
  if(with_category): return f"{category}/package_{package_id}"
  else: return f"package_{package_id}"

def generate_package(package_id, config):
  nb_features = random.randrange(config.vmin, config.vmax+1)
  nb_clauses  = random.randrange(config.cmin, config.cmax+1)
  nb_shared   = random.randrange(config.smin, config.smax+1)

  cmd = config.cmd_core + ("-v", str(nb_features), "-c", str(nb_clauses),)
  process = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
  stdout, stderr = process.communicate()

  description = f"package {package_id}, with {nb_features} features, {nb_clauses} clauses and {nb_shared} shared features"
  iuse = ' '.join([f"f_{i}" for i in range(1, nb_features+1)])
  lines = ()
  with open(config.tempfile, 'r') as f:
    lines = f.readlines()
  lines = [ [int(i) for i in line.split(' ')[:-1]] for line in lines[1:] ]
  lines = [ [(f"!f_{-i}" if(i<0) else f"f_{i}") for i in line] for line in lines ]
  required_use = ' '.join([ f"||({' '.join(line)})" for line in lines ])

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

install: categories_no_original categories_original repos_no_original repos_original mv_portage_conf ${{MANIFESTS}}
	echo icse2020 > "${{LOCATION_CATEGORIES}}"
	echo [DEFAULT] >> ${{LOCATION_REPOS}}
	echo main-repo = ${{REPO_NAME}} >> ${{LOCATION_REPOS}}
	echo  >> ${{LOCATION_REPOS}}
	echo [${{REPO_NAME}}] >> ${{LOCATION_REPOS}}
	echo location = ${{LOCAL_DIR}} >> ${{LOCATION_REPOS}}
	echo masters= >> ${{LOCATION_REPOS}}
	echo auto-sync = no >> ${{LOCATION_REPOS}}

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

mv_portage_conf:
	mv ${{LOCATION_ROOT}}/make.conf ${{LOCATION_ROOT}}/make.conf.original
	touch ${{LOCATION_ROOT}}/make.conf
	mv ${{LOCATION_ROOT}}/make.profile ${{LOCATION_ROOT}}/make.profile.original
	mkdir ${{LOCATION_ROOT}}/make.profile

%/Manifest:
	cd $(shell dirname $@) ; ebuild *.ebuild manifest
"""

def generate_makefile(config):
  manifests = ' '.join([f"{get_package_name(config.repo_name, package_id)}/Manifest" for package_id in range(config.nb_package)])
  return makefile_model.format(config.repo_name, manifests)


def main_manage_parameter():
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
  config = main_manage_parameter()
  for package_id in range(config.nb_package):
    ebuild_txt = generate_package(package_id, config)
    package_name = get_package_name(config.repo_name, package_id, with_category=False)
    dir_package = os.path.join(config.dir_packages, package_name)
    os.mkdir(dir_package)
    with open(os.path.join(dir_package, f"{package_name}-0.ebuid"), 'w') as f:
      f.write(ebuild_txt)

  # cleanup
  if(config.nb_package > 0): os.remove(config.tempfile)
  os.rmdir(config.tempdir)

  # add the rest of the repo content
  dir_profiles = os.path.join(config.dir, "profiles")
  os.mkdir(dir_profiles)
  with open(os.path.join(dir_profiles, "repo_name"), 'w') as f:
    f.write(config.repo_name)

  with open(os.path.join(config.dir, "Makefile"), 'w') as f:
    f.write(generate_makefile(config))


  # DIR = "./icse"
  # NAME = "icse"

  # FM_NUM = 100
  # FEATURE_NUM = 100
  # SHARED_FEATURES_POSSIBLE_NUMS = range(0,6)
  # CONSTRAINTS_NUM = 400

  # CNF_GEN_CMD = ["Power-Law-Random-SAT-Generator/CreateSAT", "-g", "u", "-k", "3", "-u", "1"] #, "-q"]

  # # -s seed
  # # -f file
  # # -v {} -c {}


  # # generate directory FMcat if it does not exist
  # pathlib.Path("{}/{}".format(DIR,NAME)).mkdir(parents=True, exist_ok=True)

  # for i in range(FM_NUM):

  #     # generate the CNF file

  #     opt = ["-s", "{}".format(i)]
  #     opt += ["-f", "{}/{}".format(DIR,i)]
  #     opt += ["-v", "{}".format(FEATURE_NUM), "-c", "{}".format(CONSTRAINTS_NUM)]

  #     process = subprocess.Popen(CNF_GEN_CMD + opt,
  #                                stdout=subprocess.PIPE,
  #                                stderr=subprocess.PIPE)
  #     stdout, stderr = process.communicate()

  #     # load the clauses in memory and delete the cnf file
  #     with open(DIR + "/{}.cnf".format(i)) as f:
  #         lines = f.readlines()
  #     os.remove(DIR + "/{}.cnf".format(i))
  #     lines = [x for x in lines if not x.startswith("c") and not x.startswith("p")]
  #     clauses = [[int(x) for x in y.split(" ")] for y in lines]

  #     # start content
  #     content = """EAPI=6
  # DESCRIPTION="FM {}, features {}, shared features {}, constraints {}"
  # SLOT="0"
  # KEYWORDS="amd64 sh sparc x86"
  # """.format(FM_NUM, FEATURE_NUM, SHARED_FEATURES_POSSIBLE_NUMS, CONSTRAINTS_NUM)

  #     # generate IUSE
  #     content += "IUSE=\""
  #     for j in range(1,FEATURE_NUM+1):
  #         content += " f{}".format(j)
  #     content += "\"\n"

  #     # generate REQUIRED_USE
  #     content += "REQUIRED_USE=\""
  #     for j in clauses:
  #         content += " || ("
  #         for k in j:
  #             if k > 0:
  #                 content += " f{}".format(k)
  #             elif k < 0:
  #                 content += " !f{}".format(-k)
  #         content += " )"
  #     content += "\"\n"

  #     # generate shared feature constraints
  #     n = random.choice(SHARED_FEATURES_POSSIBLE_NUMS)
  #     if n > 0:
  #         shared_features = random.choices(list(range(i)) + list(range(i+1,FM_NUM)), k=n)
  #         content += "DEPEND=\""
  #         for j in range(n):
  #             content += " f{}? ( {}/FM{} )".format(j+1, NAME, shared_features[j])
  #         content += "\"\n"

  #     #write ebuild file
  #     pathlib.Path("{}/{}/FM{}".format(DIR,NAME,i)).mkdir(parents=True, exist_ok=True)
  #     with open("{}/{}/FM{}/FM{}-0.ebuild".format(DIR,NAME,i,i), "w") as f:
  #         f.write(content)

  #     # write metadata
  #     pathlib.Path(DIR + "/metadata").mkdir(parents=True, exist_ok=True)
  #     with open(DIR + "/metadata/layout.conf", "w") as f:
  #         f.write("repo-name={}\nmasters=".format(NAME))

  #     # write categories
  #     with open(DIR + "/categories", "w") as f:
  #         f.write("{}\n".format(NAME))


