

# PDEPA: A [PMS](https://dev.gentoo.org/~ulm/pms/head/pms.html)-valid dependency analyser for [Gentoo](https://gentoo.org)

This project provides a sound implementation for dependency analysis in [Portage](https://wiki.gentoo.org/wiki/Portage), the package manager of [Gentoo](https://gentoo.org).
The soundness of this work is given by recent advances in the theory of [Software Product Lines](https://en.wikipedia.org/wiki/Software_product_line).
The name of this project, `pdepa`, stands for `Portage Dependency Analyser`.


The `pdepa` program developped in this repository is placed in the `src/main/` directory.
Two side utilities are also present in this repository:
 * a set of bash and python3 scripts to perform benchs on the `pdepa` tool, placed in the `src/test/bench/` directory
 * a tool that can generate a random portage repository (again with the objective to analyse `pdepa`), placed in the `src/test/repo_gen/` directory


## Dependencies

The tool is implemented in python3, and relies on the following libraries:
 * portage (distributed with e.g., [Gentoo](https://gentoo.org)) which is used to query the portage's package database. A big thanks to [Zac Medico](https://github.com/zmedico) for his help and insights in how to use the portage API.
 * lrparsing (distributed with `pip install lrparsing`) which is used to parse the packages' dependencies
 * z3 solver (distributed with `pip install z3-solver` or `USE=python emerge sci-mathematics/z3` in gentoo) which is used to analyse the packages' dependencies

## Functionalities

Currently, `pdepa` is a package dependency solver, i.e., it takes in argument a list of atoms and computes the set of packages to install (and how their use flags must be configured) together with the atoms in parameter so all package dependencies are met.

In the future, we want to add a planner to `pdepa` and a hook to gentoo's `ebuild` tool so it could install the computed set of packages.

### Tool Usage

`pdepa` can only be executed in an environment where portage is installed, with a compatible package repository.
`pdepa` can then be called to compute the dependency of any atom.
For instance, to know how to install `pip` (the python package manager), one can run
```bash
pdepa.py dev-pyton/pip
```

When the tool succeeds, it generates four files:
 * `install-package.sh` is a script that installs the packages computed by `pdepa`, using portage's `emerge` tool
 * `install.keywords` is a keyword configuration file that unkeywords all the keyworded packages required in `install-package.sh`
 * `install.mask` is a mask configuration file that unmasks all the masked packages required in `install-package.sh`
 * `install.use` is a use configuration file that sets the use flags of all the packages required in `install-package.sh`
*WARNING*: since `pdepa` has no planner for now, the order in which the packages must be installed/uninstalled is not set. In many cases this causes the generated scripts to fail due to emerge complains. This will be solved in future releases of the tool.


If the tool fails, it outputs an error message that precisely (but maybe not very clearly for now) gives the reason of the failure.
For instance, trying to install `kde-plasma/plasma-meta` fails:
```bash
$ ./pdepa.py kde-plasma/plasma-meta
Failure due to the following conflicting dependencies:
IN sys-apps/accountsservice-0.6.50-r1: REQUIRED_USE
  => constraint: ^^ ( consolekit elogind systemd )
  => with full use: abi_x86_64 elibc_glibc amd64 userland_GNU kernel_linux introspection
  => translated: False
```
This message states that failure is due to the `REQUIRED_USE` of the package `sys-apps/accountsservice-0.6.50-r1` not being validated (it translates to `False` with the current use flag configuration).

Instead, trying to install `kde-plasma/plasma-meta` while allowing to change the use flag configuration succeeds:
```bash
user@localhost ~/src/main $ time python pdepa.py -U -- kde-plasma/plasma-meta

real    1m5.350s
user    1m1.445s
sys     0m2.068s
```

### Options
The current options of `pdepa` are as follow
```
usage: pdepa.py [-h] [-U [{all,+,-}]] [-M [{all,keyword,mask}]] [-C [{all,newuse}]] [-O] [-p] [-v] [--] package [package ...]

positional arguments:
  package                                                    the list of packages to install. For more flexibility,
                                                             every element of the list can follow the DEPEND syntax

optional arguments:
  -h, --help                                                      show this help message and exit
  -U [{all,+,-}], --explore-use [{all,+,-}]                       allow the tool to set use flags
  -M [{all,keyword,mask}], --explore-mask [{all,keyword,mask}]    allow the tool to unmask packages
  -C [{all,newuse}], --explore-installed [{all,newuse}]           allow the tool to also consider the installed packages in its dependency computation
  -O, --optimize                                                  the tool will optimize the solution (installing less packages, unmasking less packages and changing less use flags when relevant)
  -p, --pretend                                                   do not generate the installation files
  -v, --verbose                                                   increase tool verbosity
  --                                                              separator between the option and the list of packages
```


`pdepa` by default only considers the available packages (those not masked nor keyworded) with their current use flag configuration, but this behavior can be changed with some options:
 * `-U [{all,+,-}], --explore-use [{all,+,-}]` allows the tool to explore different use flags configuration:
   * `all` (default) means that it can set and unset any use flags (except the ones enforced by the profile)
   * `+` means that it can only set use flags
   * `-` means that it can only unset use flags
 * `-M [{all,keyword,mask}], --explore-mask [{all,keyword,mask}]`  allows the tool to unmask packages:
   * `all` (default) means that it can unmask and unkeyword any package
   * `keyword` means that it can only unkeyword packages
   * `mask` means that it can only unmask packages
 * `-C [{all,newuse}], --explore-installed [{all,newuse}]` allows the tool to explore the installed packages configuration
   * `all` means that the use flags of installed packages (except the deprecated ones) can be explored like other packages (with the `-U` option)
   * `newuse` means that installed packages will be explored with the user-given configuration, and not the one used during their installation

In opposite of the dependency solver implemented in portage, `pdepa` is based on constraint simplification and solving, not on graph exploration and backtracking.
This is why there are no options to control backtracking in `pdepa`.
On the other hand, `pdepa` has a `--optimize` option: a constraint solver by default has no criteria to prefer a solution compared to another one and thus returns a set of packages and use flag configuration, randomly chosen among all possible solutions of the input problem. The `--optimize` option modifies the solver's answer to give a minimal set of packages to install/uninstall.




## Current Status

This tool is a prototype under development.
The core functionalities are present, but some other important functionalities are missing, and the user interface (in particular, the information messages) can be improved.

### TODO

* add a planner to `pdepa` so it can install the computed set of packages.
* test the possibility of interractive configuration where the user, upon failure of the solver, can explore where the current use flag/mask configuration fails and update it to allow the solver to proceed
* improve error messages
* optimize `pdepa`: currently, it uses about 5 times more memory than [`emerge`](https://wiki.gentoo.org/wiki/Portage#emerge) and is about 11 times slower.

