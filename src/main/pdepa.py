#!/usr/bin/python

__author__     = "Michael Lienhardt"
__copyright__  = "Copyright 2019-2020, Michael Lienhardt"
__license__    = "GPL3"
__version__    = "1"
__maintainer__ = "Michael Lienhardt"
__email__      = "michael.lienhardt@onera.fr"
__status__     = "Prototype"

import argparse
import z3

import gzoumlib.gzoumLogic as gzl
from gzoumlib.gzoumUtils import container, emptyset, dictmerge
import package.repository as repository



class dep_solver(object):
  """
  This class implements the fixpoint solver described in the "Lazy Product Discovery in Huge Configuration Spaces" article published in ICSE2020
  """
  class config(object):
    """
    This class stores the different configuration option of the solver
    """
    __slots__ = "_use", "_installed", "_optimize"
    def __init__(self, use, installed, optimize):
      """
      Constructor of the dep_solver.config class
      Parameters:
        use (repository.repository.config.exp_use): which useflag configuration can be explored during the package dependency solving
        installed (repository.repository.config.exp_installed): how to manage the already installed package during the package dependency solving
        optimize (bool): triggers the post processing of the SAT solver's output to remove useless packages
      """
      self._use = use
      self._installed = installed
      self._optimize = optimize
      
  __slots__ = (
    '_repo', '_config', '_z3_translator', '_z3_solver', '_input_count', '_loaded_els', '_loaded_map',
    '_solution', '_conflict', '_c_solver', '_c_info'
  )

  """
  In portage, two elements have constraints:
   - package (named "cpv" in the rest of this file, to follow portage's standard):
       a package is characterised with a .ebuild file and naturally, has constraints structured in REQUIRED_USE, DEPEND, RDEPEND, BDEPEND and PDEPEND
   - package group (named "cp" in the rest of this file, to follow portage's standard):
       some packages are simply different versions of the same software.
       To avoid override when installing two versions of the same software, portage introduced the notion of SLOT: two packages of the same software can be installed at the same time if they have a different SLOT.
       In this implementation, we encode this conflicting constraint in an object -- a package group -- corresponding to the software level (while packages are at the version level)
  The following object "kind" stores the two possible kind of a constraint container: either a cpv or a cp.
  """
  kind = container(cpv=0, cp=1)
  def __init__(self, repo, dep_solver_conf):
    """
    Constructor of the fixpoint solver
    Parameters:
      repo (repository.repository): the package repository from which we load cpvs and cps
      dep_solver_conf (dep_solver.config): the configuration of this solver
    """
    self._repo = repo
    self._config = dep_solver_conf
    self._z3_translator = gzl.toZ3Visitor()
    self._z3_solver = z3.Solver()
    self._z3_solver.set(unsat_core=True)
    self._loaded_els = set()
    self._loaded_map = {}
    self._solution = ()
    self._conflict = None
    #
    if(self._config._installed is not None): # we can touch the current installation, while still enforcing the required packages
      required_depend = self._repo.get_required_depend()
      dummy_package = self._repo.get_dummy_package(name='world', depend=required_depend)
      constraint = self._z3_translator.visit(dummy_package.get_spc())
      self._manage_constraint(constraint, dummy_package._name, dep_solver.kind.cpv)
    # else: it is managed with the fixed_product that sets every installed packages to True


  def add(self, depend):
    """
    This method adds a new dependency constraint in the solver, which in turn, look for a solution
    Parameters:
      depend (str with the DEPEND syntax): the added constraint
    """
    if(self._conflict is not None): return
    if(not self._add(depend)): return
    self._solution = None
    i = 0
    while((self._solution is None) and (self._z3_solver.check() == z3.sat)):
     if(not self._step()): return
    self._conclude()

  def _add(self, depend):
    """
    This method creates a dummy package with the intput constraint as its dependency, and preprocesses this new package
    Parameters:
      depend (str with the DEPEND syntax): the added constraint
    """
    dummy_package = self._repo.get_dummy_package(name='input', depend=depend)
    dummy_package.compute_spc()
    constraint = self._z3_translator.visit(gzl.And(tuple(el[0] for el in dummy_package._spc_depend)))
    return self._manage_constraint(constraint, dummy_package._name, dep_solver.kind.cpv)

  def _step(self):
    """
    This method implements a soling step in our fixpoint-based solver
    """
    # 1. look for a solution of the current constraint
    self._solution = self._z3_solver.model()
    self._solution = { str(var) for var in self._z3_translator._var_map.values() if(self._solution[var]) }
    # 2. look for cpvs in the solution that have not been loaded    
    new_packages = self._get_package_from_sol(self._solution)
    new_packages.difference_update(self._loaded_els)
    if(len(new_packages) is not 0):
      self._solution = None # since we have new cpvs, we didn't consider their constraint, and so the solution is not real
      # 3. for all the new cpvs
      for cpv in new_packages:
        # 3.1. load it and its constraint
        package = self._repo.get_package(cpv)
        constraint = self._z3_translator.visit(self._repo.get_spc(cpv))
        # 3.2. pre-process the cpv, and fails if a problem is found
        if(not self._manage_constraint(constraint, cpv, dep_solver.kind.cpv)): return False
        # 3.3. check if the cp of this cpv was loaded, and if not, loads it and pre-processes it
        if((package._cp is not None) and (package._cp not in self._loaded_els)):
          constraint = self._z3_translator.visit(self._repo.get_cp(package._cp))
          if(not self._manage_constraint(constraint, package._cp, dep_solver.kind.cp)): return False
    return True # we found a solution

  def _conclude(self):
    """
    This method concludes the solving process:
      if no solution was found, it extracts relevant information that identifies the origin of the error
      if a solution was found and must be optimized, it calls the optimize method
    """
    if(self._solution is None):
      unsat = self._z3_solver.unsat_core()
      self._conflict = (
        frozenset(k for k,v in self._loaded_map.items() if((v[0] is dep_solver.kind.cpv) and (v[1] in unsat))),
        frozenset(k for k,v in self._loaded_map.items() if((v[0] is dep_solver.kind.cp) and (v[1] in unsat)))
      )
    elif(self._config._optimize): self._optimize()

  def _manage_constraint(self, constraint, name, kind):
    """
    This method pre-process a constraint container (either a cpv or a cp) and manages simple cases before sending its constraint to the SAT solver
    Parameters:
      constraint (gzoumlib.gzoumLogic.SPC): the constraint of the package
      name (str): the name of the container
      kind (int from dep_solver.kind): the kind of the container (either kind.cpv or kind.cp)
    """
    # 1. check if the contraint is False: if yes the container cannot be installed: failure
    if(constraint is False):
      if(kind is dep_solver.kind.cpv): self._conflict = (frozenset((name,)), emptyset)
      elif(kind is dep_solver.kind.cp): self._conflict = (emptyset, frozenset((name,)))
      return False
    # 2. otherwise, if the constraint is not True, we add it to the solver (and keep a reference to it to manage failure)
    elif(constraint is not True):
      refbool = z3.Bool("{}:{}".format(kind, name))
      self._loaded_map[name] = (kind, refbool)
      self._z3_solver.assert_and_track(constraint, refbool)
    self._loaded_els.add(name)
    return True

  def _optimize(self):
    """
    The current implementation of the optimization is based on minimizing the number of selected cpvs, by asking the SAT solver to minimize that number.
    """
    optimize = z3.Optimize()
    cpvs = set()
    packages = set()
    # add the constraint
    for k,v in self._loaded_map.items():
      if(v[0] is dep_solver.kind.cpv):
        p = self._repo.get_package(k)
        cpvs.add(k)
        packages.add(p)
        optimize.add(self._z3_translator.visit(p.get_spc()))
      else: optimize.add(self._z3_translator.visit(self._repo.get_cp(k)))
    # define the optimization criteria
    optimize.minimize(z3.Sum(tuple(z3.If(self._z3_translator.visit(cpv), 1, 0) for cpv in cpvs)))
    # forbid to use non loaded packages
    simplify = gzl.substitutionVisitor({}).visit
    for p in packages:
      to_disable = p._dep_package.difference(cpvs)
      if(len(to_disable) is not 0):
        optimize.add(self._z3_translator.visit(simplify(gzl.Not(gzl.Or(*to_disable)))))
        cpvs.update(to_disable)
    # get the model
    optimize.check()
    self._solution = optimize.model()
    self._solution = { str(var) for var in self._z3_translator._var_map.values() if(self._solution[var]) }



  def sat(self):
    """
    This method returns if the solver's constraint is satisfiable.
    Returns: if the solver's constraint is satisfiable.
    """
    return self._conflict is None

  def model(self):
    """
    This method returns a model of the solver's constraint, when it is satisfiable.
    The model is a tuple of the following four elements:
      solution_packages: the set of package name present in the model
      solution_use: a map from the package in solution_packages to its set of selected use flags
      solution_mask: a dictionay mapping a subset package names from solution_packages to a pair (to_unmask, to_unkeyword)
      solution_uninstall: the set of package names to uninstall
    Returns: a model of the solver's constraint, when it is satisfiable.
    """
    if(self._solution is None): return None

    # 1. compute the solution_packages
    # 1'. additionally, extract all relevant information to compute solution_use
    solution_packages = set()
    solution_use_tmp = {}
    for f in self._solution:
      if(self._repo.feature_is_iuse(f)):
        cpv, iuse = self._repo.feature_deconstruct(f)
        #if(self._repo.is_package_installed(cpv)): print("{} [{}]=> {}".format(f, self._repo.get_package(cpv)._eapi, self._repo.is_package_deprecated(cpv)))
        use = solution_use_tmp.get(cpv)
        if(use is None):
          use = []
          solution_use_tmp[cpv] = use
        use.append(iuse)
      else: solution_packages.add(f)
    # 2. compute solution_use
    solution_use = {}
    for cpv, use in solution_use_tmp.items():
      package = self._repo.get_package(cpv)
      product = { iuse: ((iuse in use) or package._fixed_product.get(f)) for iuse,f in package._use_map.items() }
      solution_use[cpv] = product
    # 3. compute solution_mask
    solution_mask = {}
    for cpv in solution_packages:
      if(not self._repo.is_package_deprecated(cpv)):
        masked = self._repo.is_package_masked(cpv)
        keyworded = self._repo.is_package_keyworded(cpv)
        if(masked or keyworded):
          #print("found that {} is [{},{}]".format(cpv, masked, keyworded))
          solution_mask[cpv] = (masked, keyworded)
    # 4. compute solution_uninstall
    if(self._config._installed is None): solution_uninstall = frozenset()
    else:
      # we remove package that are not updated, i.e., that have no equivlance in solution_packages with the same cp and slot 
      cps = { (p._cp, p._slot): p._name for p in map(self._repo.get_package, self._repo.get_installed_packages()) }
      for p in map(self._repo.get_package, solution_packages): cps.pop((p._cp, p._slot), None)
      solution_uninstall = frozenset(cps.values())
    #
    return solution_packages, solution_use, solution_mask, solution_uninstall


  # helper dictionary to display failure messages
  conflict_info = container(
    req=("REQUIRED_USE", lambda p,i: f"req_{p}:{i}", lambda x: x._required_use),
    dep=("DEPEND", lambda p,i: f"dep_{p}:{i}", lambda x: x._depend),
    bdep=("BDEPEND", lambda p,i: f"bdep_{p}:{i}", lambda x: x._bdepend),
    rdep=("RDEPEND", lambda p,i: f"rdep_{p}:{i}", lambda x: x._rdepend),
    pdep=("PDEPEND", lambda p,i: f"pdep_{p}:{i}", lambda x: x._pdepend)
  )
  def conflict(self):
    """
    This method returns a string describing the reason for the solver's failure (or None when the solver didn't fail).
    Returns: a string describing the reason for the solver's failure (or None when the solver didn't fail).
    """
    if(self._conflict is None): return None
    # 1. get a solver specifically for error messaging
    self._c_solver = z3.Solver()
    self._c_solver.set(unsat_core=True)
    self._c_info = {}
    # 2. for more precise failure messages, each atomic constraint is added individually in the solver
    #  additionally, every constraint is registered in self._c_info with a corresponding error message
    for cpv in self._conflict[0]: # TODO: need to manage the product
      package = self._repo.get_package(cpv)
      #
      for i,req_data in enumerate(package._spc_required_use):
        err = self._conflict_register_constraint(package, dep_solver.conflict_info.req, i, req_data)
        if(err is not None): return err

      for i,dep_data in enumerate(package._spc_depend):
        err = self._conflict_register_constraint(package, dep_solver.conflict_info.dep, i, dep_data)
        if(err is not None): return err

      for i,bdep_data in enumerate(package._spc_bdepend):
        err = self._conflict_register_constraint(package, dep_solver.conflict_info.bdep, i, bdep_data)
        if(err is not None): return err

      for i,rdep_data in enumerate(package._spc_rdepend):
        err = self._conflict_register_constraint(package, dep_solver.conflict_info.rdep, i, rdep_data)
        if(err is not None): return err

      for i,pdep_data in enumerate(package._spc_pdepend):
        err = self._conflict_register_constraint(package, dep_solver.conflict_info.pdep, i, pdep_data)
        if(err is not None): return err
    # 3. ask the solver to compute the unsat core
    reason = []
    self._c_solver.check()
    unsat = self._c_solver.unsat_core()
    print(unsat)
    # 3. for every variable in the unsat core, add the corresponding error message (from self._c_info) in the reason list
    for bool_var, local_reason in self._c_info.items():
      if(bool_var in unsat): reason.append(local_reason)
    return reason

  def _conflict_register_constraint(self, package, c_info, i, c_data):
    """
    This method registers a possible failure causing constraint.
    Parameters:
      package (repository.package): the package containing the constraint
      c_info (value from dep_solver.conflict_info): getter helper to extract information from the input package
      i (int): index of the constraint
      c_data (gzoumlib.gzoumLogic.SPC): the constraint
    Returns: None, or a failure reason list, if the input constraint (c_data) is False
    """
    data = (c_info, package, c_data)
    #print("Adding {} from {}: {}".format(c_info[0], package._name, c_info[2](package)[c_data[1]:c_data[2]]))
    #print("  => {}".format(gzl.toStringDebugVisitor().visit(c_data[0])))
    constraint = self._z3_translator.visit(c_data[0])
    if(constraint is False): return [data]
    elif(constraint is not True):
      id_bool = z3.Bool(c_info[1](package._name,i))
      self._c_info[id_bool] = data
      self._c_solver.assert_and_track(constraint, id_bool)
    return None


  def _get_package_from_sol(self, solution):
    """
    This method returns the set of variable names from the input solution that corerspond to a cpv.
    Parameters:
      solution (str collection): a collection of variable names
    Returns: the set of variable names from the input solution that corerspond to a cpv.
    """
    return { f for f in solution if(self._repo.feature_is_package(f)) }


#def get_configuration(constraint, grounded=False):
#  get_variables = gzl.SPC_getVariablesVisitor().visit
#  loaded_packages = set()
#  solution = None
#  solver = z3.Solver()
#  #print(constraint._content[0])
#  #print(z3_translator.visit(constraint._content[0]).__class__.__name__)
#  solver.add(z3_translator.visit(constraint))
#  load = (lambda p: repository.get_package(p).get_ground_spc()) if(grounded) else (lambda p: repository.get_package(p).get_core_spc())
#  while((solution is None) and (solver.check() == z3.sat)):
#    solution = solver.model()
#    solution = { str(var) for var in z3_translator._var_map.values() if(solution[var]) }
#    #print(solution)
#    new_packages = { f for f in solution if("%" not in f) }
#    new_packages.difference_update(loaded_packages)
#    if(len(new_packages) is not 0):
#      loaded_packages.update(new_packages)
#      solution = None
#      for p in new_packages:
#        new_c = load(p)
#        solver.add(z3_translator.visit(new_c))
#  return solution

def print_model(solution_packages, solution_use, solution_mask, solution_uninstall):
  """
  This function print the input model on the standard output.
  Parameters:
    solution_packages: the set of package name present in the model
    solution_use: a map from the package in solution_packages to its set of selected use flags
    solution_mask: a dictionay mapping a subset package names from solution_packages to a pair (to_unmask, to_unkeyword)
    solution_uninstall: the set of package names to uninstall
  """
  for cpv in solution_packages:
    suse = solution_use.get(cpv)
    if(suse is None): print(f"[ebuild N] {cpv}")
    else: print(f"[ebuild N] {cpv} USE=\"{' '.join([('' if v else '-') + use for use, v in suse.items()])}\"")
  for cpv in solution_uninstall:
    print(f"[ebuild D] {cpv}")



# Configuration variable for the following function (need to be refactored in a user defined input)
self_program_name = None # set during parameter parsing
path_emerge_script = './install-package.sh'
path_use_flag_configuration = './install.use'
path_mask_configuration = './install.mask'
path_keywords_configuration = './install.keywords'

def generate_installation_files(solution_packages, solution_use, solution_mask, solution_uninstall):
  """
  This function generates scripts and configuration file intended to install the input model.
  WARNING: this function does not properly work, since it does not include a planner. The functionality hinted here must thus be refined in future work.
  Parameters:
    solution_packages: the set of package name present in the model
    solution_use: a map from the package in solution_packages to its set of selected use flags
    solution_mask: a dictionay mapping a subset package names from solution_packages to a pair (to_unmask, to_unkeyword)
    solution_uninstall: the set of package names to uninstall
  """
  with open(path_emerge_script, 'w') as f:
    f.write("#!/bin/bash\n")
    f.write("\n")
    f.write("# File auto-generated by the {} tool\n".format(self_program_name))
    f.write("# Do not update, any modification on this file will will overwritten by the tool\n")
    f.write("\n")
    if(len(solution_packages) is not 0):
      f.write("emerge -p --newuse {}\n".format(" ".join(["=" + cpv for cpv in solution_packages])))
    if(len(solution_uninstall) is not 0):
      f.write("emerge -p --unmerge {}\n".format(" ".join(["=" + cpv for cpv in solution_uninstall])))
    f.write("\n")

  with open(path_use_flag_configuration, 'w') as f:
    f.write("# File auto-generated by the {} tool\n".format(self_program_name))
    f.write("# Do not update, any modification on this file will will overwritten by the tool\n")
    f.write("\n")
    for cpv, use_selection in solution_use.items():
      string = "={} ".format(cpv)
      string = string + " ".join([('' if(selected) else '-') + iuse for iuse,selected in use_selection.items()]) + "\n"
      f.write(string)
    f.write("\n")

  with open(path_mask_configuration, 'w') as f:
    f.write("# File auto-generated by the hyportage tool\n")
    f.write("# Do not update, any modification on this file will will overwritten by the tool\n")
    f.write("\n")
    for cpv, masking in solution_mask.items():
      if(masking[0]): f.write("={}\n".format(cpv))
    f.write("\n")

  with open(path_keywords_configuration, 'w') as f:
    f.write("# File auto-generated by the hyportage tool\n")
    f.write("# Do not update, any modification on this file will will overwritten by the tool\n")
    f.write("\n")
    for cpv, masking in solution_mask.items():
      if(masking[1]): f.write("={} **\n".format(cpv))
    f.write("\n")


def print_reason(repo, reason):
  """
  This function prints the failure reason in input on the standard output.
  Parameters:
    repo (repository.repository): the repository the solver used to generate the failure reason
    reason: the failure reason
  """
  spc_to_string = gzl.toStringDebugVisitor().visit
  for c_kind,package,c_info in reason:
    print("IN {}: {}".format(package._name, c_kind[0]))
    c, sb, se = c_info
    print("  => constraint: {}".format(c_kind[2](package)[sb:se]))
    print("  => with full use: {}".format(" ".join(list(filter(lambda x: x is not None, map(lambda kv: (repo.feature_deconstruct(kv[0])[1] if(kv[1]) else None), package.get_fixed_product().items()))))))
    print("  => translated: {}".format(spc_to_string(c)))
    print("")



def main_manage_parameter():
  """
  This function declares and manages the parameters of the pdepa tool.
  """
  use_enum = repository.repository.config.exp_use
  mask_enum = repository.repository.config.exp_mask
  installed_enum = repository.repository.config.exp_installed
  parser = argparse.ArgumentParser()
  parser.add_argument("-U", "--explore-use", type=use_enum, choices=list(use_enum), default=None, const=use_enum.use_all, nargs='?', action='store', help="allow the tool to set use flags")
  parser.add_argument("-M", "--explore-mask", type=mask_enum, choices=list(mask_enum), default=None, const=mask_enum.mask_all, nargs='?', action='store',  help="allow the tool to unmask packages")
  parser.add_argument("-C", "--explore-installed", type=installed_enum, choices=list(installed_enum), default=None, const=installed_enum.inst_all, nargs='?', action='store', help="allow the tool to also consider the installed packages in its dependency computation")
  parser.add_argument("-O", "--optimize", action="store_true", help="the tool will optimize the solution (installing less packages, unmasking less packages and changing less use flags when relevant)")
  parser.add_argument("-p", "--pretend", action="store_true", help="do not generate the installation files")
  parser.add_argument("-v", "--verbose", action="count", default=0, help="increase tool verbosity")
  parser.add_argument("--", dest="sep", help="separator between the option and the list of packages")
  parser.add_argument("package", nargs='+', help="the list of packages to install. For more flexibility, every element of the list can follow the DEPEND syntax")
  #
  global self_program_name
  self_program_name = parser.prog

  args = parser.parse_args()
  #print("config: {} {} {} {} {}".format(args.explore_use, args.explore_mask, args.explore_installed, args.optimize, args.verbose))

  repo_conf = repository.repository.config(args.explore_use, args.explore_mask, args.explore_installed)
  dep_solver_conf = dep_solver.config(args.explore_use, args.explore_installed, args.optimize)
  return args.verbose, args.pretend, repo_conf, dep_solver_conf, ' '.join(args.package)




if(__name__ == '__main__'):
  # 1. get the user configuration of the pdepa tool
  verbose, pretend, repo_conf, dep_solver_conf, depend = main_manage_parameter()
  # 2. get the repository
  repo = repository.repository(repo_conf)
  # 3. get the solver and solve the input request
  solver = dep_solver(repo, dep_solver_conf)
  solver.add(depend)
  # 4. perform different output, depending on the user configuration and the result of the solver
  if(verbose > 0):
    print("loaded {} features".format(len(solver._z3_translator._var_map)))
  if(solver.sat()):
    solution_packages, solution_use, solution_mask, solution_uninstall = solver.model()
    print_model(solution_packages, solution_use, solution_mask, solution_uninstall)
    if(not pretend): generate_installation_files(solution_packages, solution_use, solution_mask, solution_uninstall)
    exit(0)
  else:
    print("Failure due to the following conflicting dependencies")
    reason = solver.conflict()
    #print(reason)
    print_reason(repo, reason)
    exit(1)

