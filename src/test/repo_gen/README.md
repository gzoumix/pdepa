
# Random Repository Generator

The script ebuild_gen.py creates a [portage](https://wiki.gentoo.org/wiki/Portage) repository containing randomly generated packages.
The purpose of this tool is to test the correctness, completeness and efficiency of portage-like package dependency managers, like [portage](https://wiki.gentoo.org/wiki/Portage) itself, [pdepa](https://github.com/gzoumix/pdepa) (the tool developped here), or [pmerge](https://wiki.gentoo.org/wiki/Pkgcore).

This tool is a proof of concept based on the [Power-Law Random SAT Generator](https://github.com/RalfRothenberger/Power-Law-Random-SAT-Generator) tool that can generate random SAT constraints.
More precisely, for each generated package:
 * we use the SAT generator to generate the REQUIRED_USE of that package
 * we randomly generate as many use-conditional dependencies as requested
 * and similarily for conflicts
Additionally, every generated repository includes a Makefile that configures portage-like package dependency managers to use that repository:
 * `make install` configures the dependency managers to use the repository
 * `make clean` restores the original dependency managers configuration


## Installation

To use this tool, the SAT generator must be installed first.
This can be done by running the following commands:

```
git clone https://github.com/RalfRothenberger/Power-Law-Random-SAT-Generator.git
cd Power-Law-Random-SAT-Generator
make
```

Then, since `repo_gen` is written in python3, no other installation step is required.

## Usage

To run the generator, one calls the command `python3 ebuild_gen.py repo_name` with relevant option in the current folder.
This will create a folder named with the name of the repository (here `repo_name`) and containing the generated repository with its Makefile.

The number of packages, their use flags, constraints and dependencies can be controlled by setting the corresponding option, as shown in the following help.
Note that some options are inherited from the SAT generator tool to control the generation of the REQUIRED_USE constraint.
```
usage: repo_gen.py [-h] [-d DIR] [--exec_path EXEC_PATH] [-n NB_PACKAGE] [-g {p,d,u}] [--vmin VMIN] [--vmax VMAX] [--cmin CMIN] [--cmax CMAX] [--smin SMIN] [--smax SMAX] [-k K] [-b B] [-p P] [-u U] [-q Q] [-s S] repo_name

positional arguments:
  repo_name             the name of the repository

optional arguments:
  -h, --help                                show this help message and exit
  -d DIR, --dir DIR                         the directory in which to store the repo
  --exec_path EXEC_PATH                     path to the CreateSAT executable (the SAT generator)
  -n NB_PACKAGE, --nb_package NB_PACKAGE    the number of packages in the generated repository
  -g {p,d,u}                                choose between power-law distributed variables (p) or double power-law (d) or uniform (u)
  --vmin VMIN                               the minimal number of features in a package
  --vmax VMAX                               the maximal number of features in a package
  --cmin CMIN                               the minimal number of clauses / scaling factor in the REQUIRED_USE of a package
  --cmax CMAX                               the maximal number of clauses / scaling factor in the REQUIRED_USE of a package
  --dmin DMIN                               the minimal number of dependencies in the DEPEND of a package
  --dmax DMAX                               the maximal number of dependencies in the DEPEND of a package
  --smin SMIN                               the minimal number of conflicts in the DEPEND of a package
  --smax SMAX                               the maximal number of conflicts in the DEPEND of a package
  -k K                                      for double power-law only: this is the average clause length
  -b B                                      for double power-law only: power-law exponent of clauses
  -p P                                      <power-law exponent of variables>
  -u U                                      should variables be unique per clause (True) or not (False)
  -q Q                                      start quietly
  -s S                                      seed value (int), system time is used if none is given
```