

# PDEPA: A [PMS](https://dev.gentoo.org/~ulm/pms/head/pms.html)-valid dependency analyser for [Gentoo](https://gentoo.org)

This project aims at providing a sound implementation for dependency analysis in [Portage](https://wiki.gentoo.org/wiki/Portage), the package manager of [Gentoo](https://gentoo.org).
The soundness of this work is given by recent advances in the theory of [Software Product Lines]().
The name of this project, `pdepa` stands for `Portage Dependency Analyser`.

## Dependencies

The tool is implemented in python3, and relies on the following libraries:
 * portage (distributed with e.g., [Gentoo](https://gentoo.org)) which is used to query the portage's package database. A big thanks to [Zac Medico](https://github.com/zmedico) for his help and insights in how to use the portage API.
 * lrparsing (distributed with `pip install lrparsing`) which is used to parse the packages' dependencies
 * z3 solver (distributed with `pip install z3-solver`) which is used to analyse the packages' dependencies

## Functionalities

Currently, `pdepa` offers the following functionalities

### Dependency solving

`pdepa` takes in argument a list of atoms and computes the set of packages to install together with the atoms in parameter so all package dependencies are met.

#### Options
`pdepa` by default only considers the available packages (those not masked nor keyworded) and the use flag configuration from the user, but this can be changed with some options:
 * `-U [{all,+,-}], --explore-use [{all,+,-}]` allows the tool to set use flags:
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

#### Tool Usage

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

If the tool fails, it outputs an error message that precisely (but maybe not very clearly for now) gives the reason of the failure.
For instance, trying to install `kde-plasma/plasma-meta` fails:
```bash
user@localhost ~/src/main $ ./pdepa.py kde-plasma/plasma-meta
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

## Current Status

This tool is a prototype under development.
The core functionalities are present, but some other important functionalities are missing, and the user interface (in particular, the information messages) can be improved.

### TODO

* since it is not possible to use emerge, we need to add our own planner that then call ebuild.
* interractive configuration
* better user interaction