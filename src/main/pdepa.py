#!/usr/bin/python

__author__ = "Michael Lienhardt"
__copyright__ = "Copyright 2019, Michael Lienhardt"
__license__ = "GPL3"
__version__ = "1"
__maintainer__ = "Michael Lienhardt"
__email__ = "michael lienhardt@onera.fr"
__status__ = "Prototype"

import argparse
import z3

import gzoumlib.gzoumLogic as gzl
from gzoumlib.gzoumUtils import container, emptyset, dictmerge
import package.repository as repository



class dep_solver(object):
  class config(object):
    __slots__ = "_use", "_installed", "_optimize"
    def __init__(self, use, installed, optimize):
      self._use = use
      self._installed = installed
      self._optimize = optimize
      
  __slots__ = (
    '_repo', '_config', '_z3_translator', '_z3_solver', '_input_count', '_loaded_els', '_loaded_map',
    '_solution', '_conflict', '_c_solver', '_c_info'
  )
  kind = container(package=0, cp=1)
  def __init__(self, repo, dep_solver_conf):
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
      self._manage_constraint(constraint, dummy_package._name, dep_solver.kind.package)
    # else: it is managed with the fixed_product that sets every installed packages to True


  def add(self, depend):
    if(self._conflict is not None): return
    if(not self._add(depend)): return
    self._solution = None
    i = 0
    while((self._solution is None) and (self._z3_solver.check() == z3.sat)):
     if(not self._step()): return
    self._conclude()

  def _add(self, depend):
    dummy_package = self._repo.get_dummy_package(name='input', depend=depend)
    dummy_package.compute_spc()
    constraint = self._z3_translator.visit(gzl.And(tuple(el[0] for el in dummy_package._spc_depend)))
    return self._manage_constraint(constraint, dummy_package._name, dep_solver.kind.package)

  def _step(self):
    self._solution = self._z3_solver.model()
    self._solution = { str(var) for var in self._z3_translator._var_map.values() if(self._solution[var]) }
    #print(" solution: {}".print(self._solution))
    
    new_packages = self._get_package_from_sol(self._solution)
    new_packages.difference_update(self._loaded_els)
    if(len(new_packages) is not 0):
      self._solution = None
      for cpv in new_packages:
        package = self._repo.get_package(cpv)
        constraint = self._z3_translator.visit(self._repo.get_spc(cpv))
        #print("Adding {}: {}".format(cpv, tostring(self._repo.get_spc(cpv))))
        #print("Adding {}".format(cpv))
        #print("  => {}".format(constraint))
        if(not self._manage_constraint(constraint, cpv, dep_solver.kind.package)): return False
        if((package._cp is not None) and (package._cp not in self._loaded_els)):
          constraint = self._z3_translator.visit(self._repo.get_cp(package._cp))
          if(not self._manage_constraint(constraint, package._cp, dep_solver.kind.cp)): return False
    return True

  def _conclude(self):
    if(self._solution is None):
      unsat = self._z3_solver.unsat_core()
      self._conflict = (
        frozenset(k for k,v in self._loaded_map.items() if((v[0] is dep_solver.kind.package) and (v[1] in unsat))),
        frozenset(k for k,v in self._loaded_map.items() if((v[0] is dep_solver.kind.cp) and (v[1] in unsat)))
      )
    elif(self._config._optimize): self._optimize()

  def _manage_constraint(self, constraint, name, kind):
    if(constraint is False):
      if(kind is dep_solver.kind.package): self._conflict = (frozenset((name,)), emptyset)
      elif(kind is dep_solver.kind.cp): self._conflict = (emptyset, frozenset((name,)))
      return False
    elif(constraint is not True):
      refbool = z3.Bool("{}:{}".format(kind, name))
      self._loaded_map[name] = (kind, refbool)
      self._z3_solver.assert_and_track(constraint, refbool)
    self._loaded_els.add(name)
    return True

  def _optimize(self):
    optimize = z3.Optimize()
    cpvs = set()
    packages = set()
    # add the constraint
    for k,v in self._loaded_map.items():
      if(v[0] is dep_solver.kind.package):
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



  def sat(self): return self._conflict is None

  def model(self):
    if(self._solution is None): return None

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
    #
    solution_use = {}
    for cpv, use in solution_use_tmp.items():
      package = self._repo.get_package(cpv)
      product = { iuse: ((iuse in use) or package._fixed_product.get(f)) for iuse,f in package._use_map.items() }
      solution_use[cpv] = product
    #
    solution_mask = {}
    for cpv in solution_packages:
      if(not self._repo.is_package_deprecated(cpv)):
        masked = self._repo.is_package_masked(cpv)
        keyworded = self._repo.is_package_keyworded(cpv)
        if(masked or keyworded):
          #print("found that {} is [{},{}]".format(cpv, masked, keyworded))
          solution_mask[cpv] = (masked, keyworded)
    #
    if(self._config._installed is None): solution_uninstall = frozenset()
    else:
      # we remove package that are not updated, i.e., that have no equivlance in solution_packages with the same cp and slot 
      cps = { (p._cp, p._slot): p._name for p in map(self._repo.get_package, self._repo.get_installed_packages()) }
      for p in map(self._repo.get_package, solution_packages): cps.pop((p._cp, p._slot), None)
      solution_uninstall = frozenset(cps.values())
    #
    return solution_packages, solution_use, solution_mask, solution_uninstall


  conflict_info = container(
    req=("REQUIRED_USE", lambda p,i: "req_{}:{}".format(p,i), lambda x: x._required_use),
    dep=("DEPEND", lambda p,i: "dep_{}:{}".format(p,i), lambda x: x._depend),
    bdep=("BDEPEND", lambda p,i: "bdep_{}:{}".format(p,i), lambda x: x._bdepend),
    rdep=("RDEPEND", lambda p,i: "rdep_{}:{}".format(p,i), lambda x: x._rdepend),
    pdep=("PDEPEND", lambda p,i: "pdep_{}:{}".format(p,i), lambda x: x._pdepend)
  )
  def conflict(self):
    if(self._conflict is None): return None
    self._c_solver = z3.Solver()
    self._c_solver.set(unsat_core=True)
    self._c_info = {}
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

      #product_name = "prod_{}".format(p)
      #spc_product = ...
    # reason lookup
    reason = []
    self._c_solver.check()
    unsat = self._c_solver.unsat_core()
    print(unsat)
    for bool_var, local_reason in self._c_info.items():
      if(bool_var in unsat): reason.append(local_reason)
    return reason

  def _conflict_register_constraint(self, package, c_info, i, c_data):
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


  def _get_package_bool(self, package_name): return self._z3_translator._var_map[package_name]
  def _get_package_from_sol(self, solution): return { f for f in solution if(self._repo.feature_is_package(f)) }


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
  for cpv in solution_packages:
    suse = solution_use.get(cpv)
    if(suse is None): print('[ebuild N] {}'.format(cpv))
    else: print('[ebuild N] {} USE="{}"'.format(cpv, " ".join([("" if v else "-") + use for use, v in suse.items()])))
  for cpv in solution_uninstall:
    print('[ebuild D] {}'.format(cpv))


self_program_name = None # set during parameter parsing

path_emerge_script = './install-package.sh'
path_use_flag_configuration = './install.use'
path_mask_configuration = './install.mask'
path_keywords_configuration = './install.keywords'

def generate_installation_files(solution_packages, solution_use, solution_mask, solution_uninstall):
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
  spc_to_string = gzl.toStringDebugVisitor().visit
  for c_kind,package,c_info in reason:
    print("IN {}: {}".format(package._name, c_kind[0]))
    c, sb, se = c_info
    print("  => constraint: {}".format(c_kind[2](package)[sb:se]))
    print("  => with full use: {}".format(" ".join(list(filter(lambda x: x is not None, map(lambda kv: (repo.feature_deconstruct(kv[0])[1] if(kv[1]) else None), package.get_fixed_product().items()))))))
    print("  => translated: {}".format(spc_to_string(c)))
    print("")



def main_manage_parameter():
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
  verbose, pretend, repo_conf, dep_solver_conf, depend = main_manage_parameter()
  repo = repository.repository(repo_conf)
  solver = dep_solver(repo, dep_solver_conf)
  solver.add(depend)
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

