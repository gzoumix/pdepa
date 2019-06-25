#!/usr/bin/python

__author__ = "Michael Lienhardt"
__copyright__ = "Copyright 2019, Michael Lienhardt"
__license__ = "GPL3"
__version__ = "1"
__maintainer__ = "Michael Lienhardt"
__email__ = "michael lienhardt@onera.fr"
__status__ = "Prototype"

import enum

import portage
import portage._sets
import portage.versions
import portage.dep

from gzoumlib.gzoumUtils import dictlist, dictmerge
import package.syntax as syntax
import gzoumlib.gzoumLogic as gzl

identity = lambda x: x


#
# PACKAGE IMPLEMENTATION AND FM TRANSLATION
#



class package(object):
  """
  This class stores all relevant information concerning a specific portage package.
  Its main goal is to translate the DSL describing the dependencies between packages into SAT constraints.
  """
  def __init__(self, name, repo, eapi, slot, subslot, keywords, iuse_declared, use_user, use_installed, required_use, depend, bdepend, rdepend, pdepend, license):
    """ The constructor of a package.
    Parameters:
      name (string): the cpv of the package (e.g., "dev-python/pip-9.0.1-r1").
        It is possible to create dummy package with a non cpv name (see the repository.get_dummy_package method).
      repo (repository): the repository managing this package
      eapi (int): the eapi of the package
      slot (string): the slot of the package
      subslot (string): the subslot of the package
      keywords (string list): the list of accepted keywords for this package
      iuse_declared (string frozenset): the set of declared use flag for this package, including the implicit ones
      use_user (string frozenset): the set of use flags selected by the user
      use_installed (string frozenset): the set of use flags that was selected for this package's installation
      required_use (string): the REQUIRED_USE string
      depend (string): the DEPEND string
      bdepend (string): the BDEPEND string
      rdepend (string): the RDEPEND string
      pdepend (string): the PDEPEND string
      license (string): the LICENSE string
    """
    # core info on package
    self._repo = repo
    self._name = name
    self._eapi = eapi
    self._slot = slot
    self._subslot = subslot
    self._keywords = keywords
    self._iuse_declared = iuse_declared
    self._use_user = use_user
    self._use_installed = use_installed
    self._fixed_product = None
    self._full_fixed_product = None
    self._full_fixed_product_visitor = None
    self._required_use = required_use
    self._depend = depend
    self._bdepend = bdepend
    self._rdepend = rdepend
    self._pdepend = pdepend
    self._license = license

    # get the AST from the constraints
    self._tree_required_use = syntax.get_tree_require(self._required_use)
    self._tree_depend = syntax.get_tree_depend(self._depend)
    self._tree_bdepend = syntax.get_tree_depend(self._bdepend)
    self._tree_rdepend = syntax.get_tree_depend(self._rdepend)
    self._tree_pdepend = syntax.get_tree_depend(self._pdepend)

    # additional info on package name
    self._name_info = portage.versions.catpkgsplit(self._name, self._eapi)
    if(self._name_info is None): self._cp = None
    else: self._cp = "{}/{}".format(self._name_info[0], self._name_info[1])

    # mapping from use flags to features (so we don't need to recompute them each time)
    self._use_map = { iuse: repo._compute_feature_from_iuse(self._name, iuse) for iuse in self._iuse_declared } 
    if(self._eapi < 5): self._decl_iuse_local() # in the eapi < 5, not all iuse are declared: we need to parse the AST to get all of them
    #self._use_map[None] = self._name # feature corresponding to this package selection

    self._dep_atom = set()    # the set of atoms this package depends on
    self._dep_package = set() # the set of packages this one depends on (directly computed from the set of atoms)


  def get_feature(self, iuse=None):
    """Returns a feature related to this package.
    Parameter:
      iuse (string): if this parameter is None, then the returned feature is the one corresponding to this package.
        Otherwise, it is the one corresponding to the use flag in parameter for this package 
    """
    return self._use_map[iuse]


  def set_fixed_product(self, fixed_product):
    """ Sets the use flags whose value cannot be changed during our search space exploration
    Parameter:
      fixed_product (string->bool dict): a mapping from the set of unchangeable use flag to their boolean value (True = selected)
    """
    self._fixed_product = { self.get_feature(iuse): b for iuse, b in fixed_product.items() }


  def get_fixed_product(self):
    """Returns the fixed product of this package"""
    return self._fixed_product

  def get_full_fixed_product(self):
    """Return the fixed product of this package, including the fixed product of the packages this one depends on"""
    return self._full_fixed_product

  def compute_spc(self):
    """This method translates the dependency specifications of this package into SAT constraints.
    This method cannot be called on all loaded package, as computing this constraint requires to load the dependencies of this package...
    """
    if(self._full_fixed_product is None):
      # compute the constraint, and extract dependency information
      self._spc_required_use = self._get_spc_require(self._tree_required_use)
      self._spc_depend = self._get_spc_depend(self._tree_depend)
      self._spc_bdepend = self._get_spc_depend(self._tree_bdepend)
      self._spc_rdepend = self._get_spc_depend(self._tree_rdepend)
      self._spc_pdepend = self._get_spc_depend(self._tree_pdepend)

      # compute the full product from the dependencies
      self._full_fixed_product = dictmerge(self._fixed_product, *tuple(self._repo.get_package(cpv)._fixed_product for cpv in self._dep_package))
      self._full_fixed_product_visitor = gzl.substitutionVisitor(self._full_fixed_product).visit

      # apply the full product on the constraints
      for el in self._spc_required_use: el[0] = self._full_fixed_product_visitor(el[0])
      for el in self._spc_depend: el[0] = self._full_fixed_product_visitor(el[0])
      for el in self._spc_bdepend: el[0] = self._full_fixed_product_visitor(el[0])
      for el in self._spc_rdepend: el[0] = self._full_fixed_product_visitor(el[0])
      for el in self._spc_pdepend: el[0] = self._full_fixed_product_visitor(el[0])

  def get_spc(self):
    """Returns the feature model of this package.
    Note that a package's feature model always has the form "cpv => (REQUIRED_USE and DEPEND and BDEPEND and RDEPEND and PDEPEND )"
    """
    self.compute_spc()
    res = frozenset().union(
      (el[0] for el in self._spc_required_use),
      (el[0] for el in self._spc_depend),
      (el[0] for el in self._spc_bdepend),
      (el[0] for el in self._spc_rdepend),
      (el[0] for el in self._spc_pdepend)
    )
    return gzl.Implies(self._name, gzl.And(res))

  #######################################
  # COMPUTE THE USE FLAGS FROM PARSE TREE
  #######################################

  def _decl_iuse(self, iuse):
    res = self._repo._compute_feature_from_iuse(self._name, iuse)
    self._use_map[iuse] = res
    self._iuse_added.add(iuse)

  def _decl_iuse_condition(self, parse_tree):
    if(parse_tree[1][1] == "!"): self._decl_iuse(parse_tree[2][1])
    else: return self._decl_iuse(parse_tree[1][1])

  def _decl_iuse_selection(self, parse_tree): # the list of selected features, with contracted form...
    if(parse_tree[1][1] in ("!", '-')): self._decl_iuse(parse_tree[2][1])
    else: self._decl_iuse(parse_tree[1][1])
  
  # 1. from required_use
  def _decl_iuse_require_element(self, parse_tree):
    if((parse_tree[1][0].name == "choice") or (parse_tree[1][1] == "(")):
      for el in parse_tree:
        if((len(el) > 0) and (el[0].name == "require_element")): self._decl_iuse_require_element(el)
    elif(parse_tree[1][0].name == "condition"):
      self._decl_iuse_condition(parse_tree[1])
      for el in parse_tree:
        if((len(el) > 0) and (el[0].name == "require_element")): self._decl_iuse_require_element(el)
    elif(parse_tree[1][1] == "!"):
      self._decl_iuse(parse_tree[2][1])
    else: self._decl_iuse(parse_tree[1][1])
  
  def _decl_iuse_require(self, parse_tree):
    for el in parse_tree[1:]: self._decl_iuse_require_element(el)

  # 2. from depend
  def _decl_iuse_depend_element(self, parse_tree):
    if((parse_tree[1][0].name == "choice") or (parse_tree[1][1] == "(")):
      for el in parse_tree:
        if((len(el) > 0) and (el[0].name == "depend_element")): self._decl_iuse_depend_element(el)
    elif(parse_tree[1][0].name == "condition"):
      self._decl_iuse_condition(parse_tree[1])
      for el in parse_tree:
        if((len(el) > 0) and (el[0].name == "depend_element")): self._decl_iuse_depend_element(el)
    # otherwise, it is an atom
    for el in parse_tree:
      if((len(el) > 0) and (el[0].name == "selection")): self._decl_iuse_selection(el)

  def _decl_iuse_depend(self, parse_tree):
    for el in parse_tree[1:]: self._decl_iuse_depend_element(el)

  def _decl_iuse_local(self):
    self._iuse_added = set()
    self._decl_iuse_require(self._tree_required_use)
    self._decl_iuse_depend(self._tree_depend)
    self._decl_iuse_depend(self._tree_bdepend)
    self._decl_iuse_depend(self._tree_rdepend)
    self._decl_iuse_depend(self._tree_pdepend)
    self._iuse_declared = self._iuse_declared.union(self._iuse_added)

  #######################################
  # COMPUTE THE SPC FROM PARSE TREE
  #
  # Since the AST generated by lrparsing has a very unplesant structure,
  # it really makes no senes to describe how this translation works,
  # as it is only guided by the strange structure of the AST 
  #######################################

  def _set_range(self, node):
    """This method computes the range covered by an AST tree, and stores it in [self._parse_begin, self._parse_end]"""
    if((len(node) is 5) and (isinstance(node[1], str))):
      #print("   {}".format(tuple(node)))
      if(self._parse_begin is None): self._parse_begin = node[2]
      self._parse_end = node[2] + len(node[1])
    elif(len(node) is 2): self._set_range(node[1])
    else:
      self._set_range(node[1])
      self._set_range(node[-1])

  def _get_spc_condition(self, parse_tree):
    if parse_tree[1][1] == "!": return gzl.Not(self.get_feature(parse_tree[2][1]))
    else: return self.get_feature(parse_tree[1][1])

  @staticmethod
  def manage_selection(local_package, prefix, use, default, suffix):
    #print("  managing use flag '{}'".format(use))
    if(use not in local_package._iuse_declared):
      if(default is not None): local_use = default
      else: return False
    else: local_use = local_package.get_feature(use)
    return suffix(prefix(local_use)) # if suffix is not a conditional Implies or Iff, use might not be in package
  
  @staticmethod
  def manage_selection_list(local_package, selection_list):
    res = [ package.manage_selection(local_package, *selection) for selection in selection_list]
    if(len(res) is 0): return local_package._name
    else: return gzl.And(local_package._name, *res)
  
  @staticmethod
  def manage_node_choice(parse_tree):
    choice_string = parse_tree[1][1]
    if choice_string == syntax.CHOICE_STRING_OR: return gzl.Or
    if choice_string == syntax.CHOICE_STRING_XOR: return gzl.Xor
    if choice_string == syntax.CHOICE_STRING_AT_MOST_ONE: return gzl.Conflict
    if choice_string == syntax.CHOICE_STRING_BINDING_OR: return gzl.Or


  def _get_spc_selection(self, parse_tree): # the list of selected features, with contracted form...
    default = None
    suffix = identity
    if(parse_tree[1][1] in ("!", '-')): # negation, first case
      selection_type = gzl.Not
      use = parse_tree[2][1]
      i = 3
    else:
      selection_type = identity
      use = parse_tree[1][1]
      i = 2
    if((len(parse_tree) > i) and (parse_tree[i][1] == "(")):
      default = (parse_tree[i+1][1] == "+")
      i = i+3
    if len(parse_tree) > i:
      l_use = self.get_feature(use)
      suffix = (lambda e_use: gzl.Implies(l_use, e_use)) if(parse_tree[i][1] == "?") else (lambda e_use: gzl.Iff(l_use, e_use))
    return selection_type, use, default, suffix
  
  # 1. from required_use
  def _get_spc_require_element(self, parse_tree):
    if parse_tree[1][0].name == "choice":
      subs = tuple(self._get_spc_require_element(el) for el in parse_tree if((len(el) > 0) and (el[0].name == "require_element")))
      C = package.manage_node_choice(parse_tree[1])
      return C(subs)
    if parse_tree[1][0].name == "condition":
      subs = tuple(self._get_spc_require_element(el) for el in parse_tree if((len(el) > 0) and (el[0].name == "require_element")))
      return gzl.Implies(self._get_spc_condition(parse_tree[1]), gzl.And(subs) if(len(subs) > 1) else subs[0])
    if parse_tree[1][1] == "(":  # inner
      subs = tuple(self._get_spc_require_element(el) for el in parse_tree if((len(el) > 0) and (el[0].name == "require_element")))
      return gzl.And(subs) if(len(subs) > 1) else subs[0]
    # otherwise, it is a use flag
    neg = parse_tree[1][1] == "!"
    if neg: return gzl.Not(self.get_feature(parse_tree[2][1]))
    else: return self.get_feature(parse_tree[1][1])
  
  def _get_spc_require_in(self, el):
    self._parse_begin = None
    self._parse_end = None
    self._set_range(el)
    return self._get_spc_require_element(el)

  def _get_spc_require(self, parse_tree):
    return tuple( [self._get_spc_require_in(el), self._parse_begin, self._parse_end] for el in parse_tree[1:])

  # 2. from depend
  def _get_spc_depend_element(self, parse_tree):
    if parse_tree[1][0].name == "choice":
      subs = tuple(self._get_spc_depend_element(el) for el in parse_tree if((len(el) > 0) and (el[0].name == "depend_element")))
      C = package.manage_node_choice(parse_tree[1])
      return C(subs)
    if parse_tree[1][0].name == "condition":
      subs = tuple(self._get_spc_depend_element(el) for el in parse_tree if((len(el) > 0) and (el[0].name == "depend_element")))
      return gzl.Implies(self._get_spc_condition(parse_tree[1]), gzl.And(subs) if(len(subs) > 1) else subs[0])
    if parse_tree[1][1] == "(": # inner
      subs = tuple(self._get_spc_depend_element(el) for el in parse_tree if((len(el) > 0) and (el[0].name == "depend_element")))
      return gzl.And(subs) if(len(subs) > 1) else subs[0]
    # otherwise, it is an atom
    neg = identity
    if parse_tree[1][1] == "!": # not atom
      if parse_tree[2][1] == "!":
        neg = gzl.Not
        atom = parse_tree[3][1]
        i = 4
      else:
        neg = gzl.Not
        atom = parse_tree[2][1]
        i = 3
    else:
      atom = parse_tree[1][1]
      i = 2
    dependencies = self._repo.get_atom(atom)
    self._dep_atom.add(atom)
    self._dep_package.update(dependencies)
    if(neg is not identity): return neg(gzl.Or(dependencies))
    else:
      selection_list = [ self._get_spc_selection(el) for el in parse_tree if((len(el) > 0) and (el[0].name == "selection")) ]
      #print("SELECTION in {} for {}: {}".format(self._name, atom, [('!' if(selection_type is gzl.Not) else 'id', use, default, '?' if(suffix is gzl.Implies) else '<=>') for selection_type, use, default, suffix in selection_list]))
      return neg(gzl.Or([ package.manage_selection_list(self._repo.get_package(local_cpv), selection_list) for local_cpv in dependencies ]))

  def _get_spc_depend_in(self, el):
    self._parse_begin = None
    self._parse_end = None
    self._set_range(el)
    return self._get_spc_depend_element(el)

  def _get_spc_depend(self, parse_tree):
    return tuple( [self._get_spc_depend_in(el), self._parse_begin, self._parse_end] for el in parse_tree[1:])
  


#
# PACKAGE REPOSITORY IMPLEMENTATION
#

repo_emptyset = frozenset()  # empty set
repo_emptyconstraint = ''    # empty constraint (for both REQUIRED_USE and DEPEND syntax)
def string_to_frozenset(el, sep=" "):
  if(len(el) is 0): return repo_emptyset
  else: return frozenset(el.split(sep))

class repository(object):
  """
  This class implements a repository, i.e., a collection of packages.
  It is based on the portage query API, and so any package that is accessible via portage is part of this repository.
  """
  class config(object):
    """
    This is the configuration class for a repository
     and is used to specify the visibility and default package configuration models of this repository.
    """
    class exp_use(enum.Enum):
      use_all="all"  # we explore all use flag configuration
      use_plus="+"   # we only explore adding new use flags to a configuration
      use_minus="-"  # we only explore removing use flags from a configuration
      def __str__(self): return self.value
    class exp_mask(enum.Enum):
      mask_all="all"         # all packages are visible
      mask_keyword="keyword" # only keyworded packages are visible
      mask_mask="mask"       # only masked packages are visible
      def __str__(self): return self.value
    class exp_installed(enum.Enum):
      inst_all="all"       # the configuration of the installed package can be arbitrarily changed
      inst_newuse="newuse" # the configuration of the installed package is the one from the user configuration files
      def __str__(self): return self.value
    __slots__ = "_use", "_mask", "_installed"
    def __init__(self, use=None, mask=None, installed=None):
      """ The repository configuration constructor.
      Parameters:
        use (repository.config.exp_use): specify the use flag exploration model (default: None = no exploration)
        mask (repository.config.exp_mask): specify the visibility exploration model (default: None = no exploration)
        mask (repository.config.exp_installed): specify the installed package exploration model (default: None = no exploration)
      """
      self._use = use
      self._mask = mask
      self._installed = installed

  __slots__ = (
    '_packages', '_atoms', '_cps', '_portdb', '_vardb', '_config',
    '_installed_packages', '_fixed_use', '_fixed_iuse', '_fixed_product',
    '_get_fixed_product_normal', '_get_fixed_product_installed',
    '_filter_constraint', '_get_atom', '_dummy_count'
  )
  def __init__(self, repo_conf):
    """ This is the repository constructor.
    Parameter:
      repo_conf (repository.config): the configuration of this repository
    """
    self._packages = {}                                   # map cpv => package
    self._atoms = {}                                      # map atom => list of matched cpvs
    self._cps = {}                                        # map cp => constraint encoding SLOT conflicts
    self._portdb = portage.portdb                         # reference to the portage database
    self._vardb = portage.db['/']['vartree'].dbapi        # reference to the installed package database
    self._config = portage.config(clone=portage.settings) # reference to the portage utility that get core information for a specify cpv

    self._installed_packages = frozenset(self._vardb.cpv_all()) # I do that because cpv_exists is a disk access...

    # computation of the global fixed product, i.e., the features set by the profile and that cannot be changed by the user
    self._fixed_use = self._config.useforce.difference(self._config.usemask)
    self._fixed_iuse = self._config.useforce.union(self._config.usemask)
    self._fixed_product = self._compute_fixed_product(self._fixed_iuse, self._fixed_use)

    # setup the repository w.r.t. the given configuration
    self._setup_get_atom(repo_conf._mask)
    self._setup_get_fixed_product(repo_conf._use, repo_conf._installed)
    self._setup_filter_constraint(repo_conf._installed)

    self._dummy_count = 0 # for dummy packages


  ###########################################
  # BASE API
  ###########################################

  def get_package(self, cpv):
    """ Returns the package corresponding to the input cpv
    Parameter:
      cpv (string): the cpv of the expected package
    returns the package corresponding to the input cpv, or none if no such package exists in the portage database
    """
    res = self._packages.get(cpv)
    if(res is None):
      if(self._portdb.cpv_exists(cpv)):      # normal package
        res = self._build_package_from_config(cpv)
      elif(cpv in self._installed_packages): # deprecated package
        res = self._build_package_from_vardb(cpv)
      else: return None                      # invalid package
      self._packages[cpv] = res
    return res

  def get_spc(self, cpv):
    package = self.get_package(cpv)
    return package.get_spc()

  def get_dummy_package(self, name=None, iuse=repo_emptyset, required_use=repo_emptyconstraint, depend=repo_emptyconstraint, bdepend=repo_emptyconstraint, rdepend=repo_emptyconstraint, pdepend=repo_emptyconstraint):
    """ Constructs a dummy package that can contain arbitrary dependencies.
    Parameters:
      name (string): the name of the dummy package. If the name is None (as per default), the name of the package will be automatically generated
      iuse (string frozenset): the set of use flags of the package
      required_use (string): the REQUIRED_USE string
      depend (string): the DEPEND string
      bdepend (string): the BDEPEND string
      rdepend (string): the RDEPEND string
      pdepend (string): the PDEPEND string
    """
    if(name is None): name = '[dummy-{}]'.format(self._dummy_count)
    dummy_package = self._packages.get(name)
    if(dummy_package is None):
      self._dummy_count = self._dummy_count + 1
      dummy_package = package(
        name, self, 7, '0', '0', # package name, repo, EAPI, SLOT, SUBSLOT
        repo_emptyset, iuse, repo_emptyset, repo_emptyset, # keyword, use_referenceable, use_user, use_installed,
        required_use, depend, bdepend, rdepend, pdepend, repo_emptyconstraint) # required_use, depend, bdepend, rdepend, pdepend, license
      dummy_package.set_fixed_product({})
      self._packages[name] = dummy_package
    return dummy_package


  def get_cp(self, cp):
    """ Returns the SLOT constraint corresponding to the input cp.
    Parameter:
      cp (string): the category/package for which we want the SLOT constraint
    """
    res = self._cps.get(cp)
    if(res is None):
      packages = [self.get_package(cpv) for cpv in self.get_atom(cp)]
      slots = dictlist()
      for p in packages: slots.add(p._slot, p._name)
      res = [ gzl.Conflict(names) for names in slots.values() if(len(names) > 1) ]
      if(len(res) > 1): res = gzl.And(res)
      elif(len(res) is 1): res = res[0]
      else: res = True
      self._cps[cp] = res
    return res


  def get_atom(self, atom):
    """ Returns the set of cpvs that match the given atom.
    Parameter:
      atom (string): the atom for which we want to get the set of matching packages
    """
    res = self._atoms.get(atom)
    if(res is None):
      res = self._get_atom(atom)
      self._atoms[atom] = res
    return res


  ###########################################
  # PACKAGE QUERY
  ###########################################

  def is_package_installed(self, cpv):
    """ Returns if the cpv in parameter is installed.
    Parameter:
      cpv (string): the name of the package
    """
    return cpv in self._installed_packages

  def is_package_deprecated(self, cpv):
    """ Returns if the cpv in parameter is deprecated (i.e., installed but not in the portage database anymore).
    Parameter:
      cpv (string): the name of the package
    """
    if(self._portdb.cpv_exists(cpv)): return False
    elif(self.is_package_installed(cpv)): return True
    else: return None

  def is_package_keyworded(self, cpv):
    """ Returns if the cpv in parameter is masked by a keyword.
    Parameter:
      cpv (string): the name of the package
    """
    return 'missing keyword' in portage.getmaskingstatus(cpv, portdb=portage.portdb)

  def is_package_masked(self, cpv):
    """ Returns if the cpv in parameter is masked.
    Parameter:
      cpv (string): the name of the package
    """
    return 'package.mask' in portage.getmaskingstatus(cpv, portdb=portage.portdb)

  def get_installed_packages(self):
    """ Returns the set of all the installed package names. """
    return self._installed_packages

  @staticmethod
  def get_required_depend():
    """ Returns a DEPEND constraint corresponding to all the atom the user wants installed. """
    required_atoms = portage._sets.load_default_config(portage.settings, portage.db[portage.settings['EROOT']]).getSetAtoms('world')
    return ' '.join(required_atoms)


  ###########################################
  # REPOSITORY SETUP W.R.T. INPUT CONFIG
  ###########################################

  # 1. SETUP: get_atom method
  def _setup_get_atom(self, exp_mask):
    """ This method defines the behavior of the get_atom method w.r.t. repository configuration.
    Parameter:
      exp_mask (repository.config.exp_mask): the visibility model of this repository
    """
    if(exp_mask is None): res_tmp = self._get_atom_mask_none
    elif(exp_mask is repository.config.exp_mask.mask_all): res_tmp = self._get_atom_mask_all
    elif(exp_mask is repository.config.exp_mask.mask_keyword): res_tmp = self._get_atom_mask_keyword
    elif(exp_mask is repository.config.exp_mask.mask_mask): res_tmp = self._get_atom_mask_mask
    # an atom matches all matched package from the portage database, plus the installed ones
    self._get_atom = lambda atom: frozenset(res_tmp(atom)).union(self._vardb.match(atom))

  @staticmethod
  def _get_atom_mask_none(atom):    # default visibility model
    return portage.portdb.match(atom)
  @staticmethod
  def _get_atom_mask_all(atom):     # complete visibility
    return portage.portdb.xmatch("match-all", atom)
  @staticmethod
  def _get_atom_mask_keyword(atom): # only normal and keyworded packages are visible
    return filter(repository._get_atom_mask_keyword_filter, portage.portdb.xmatch("match-all", atom))
  @staticmethod
  def _get_atom_mask_mask(atom):    # only normal and masked packages are visible
    return filter(repository._get_atom_mask_mask_filter, portage.portdb.xmatch("match-all", atom))
  @staticmethod
  def _get_atom_mask_keyword_filter(cpv):
    l = portage.getmaskingstatus(cpv, portdb=portage.portdb)
    ll = len(l)
    return (ll is 0) or ((ll is 1) and (l[0][0] == 'm'))
    #return (ll is 0) or ((ll is 1) and (l[0] == 'missing keyword'))
  @staticmethod
  def _get_atom_mask_keyword_filter(cpv):
    l = portage.getmaskingstatus(cpv, portdb=portage.portdb)
    ll = len(l)
    return (ll is 0) or ((ll is 1) and (l[0][0] == 'p'))
    #return (ll is 0) or ((ll is 1) and (l[0] == 'package.mask'))


  # 2. SETUP: the _get_fixed_product method (this gives all the features that are externally set for a given package)
  def _setup_get_fixed_product(self, exp_use, exp_installed):
    """ This method defines which use flags cannot be explored w.r.t. the repository configuration.
    This is done by specifying a `fixed product` for every package, i.e., which use flags cannot be changed, and which are selected.
    Parameters:
      exp_use (repository.config.exp_use): the use flag exploration model
      exp_installed (repository.config.exp_installed): the installed package exploration model
    """
    if(exp_use is None):
      self._get_fixed_product_normal = self._get_fixed_product_use_user
    elif(exp_use is repository.config.exp_use.use_all):
      self._get_fixed_product_normal = self._get_fixed_product_use_all      
    elif(exp_use is repository.config.exp_use.use_plus):
      self._get_fixed_product_normal = self._get_fixed_product_use_plus
    elif(exp_use is repository.config.exp_use.use_minus):
      self._get_fixed_product_normal = self._get_fixed_product_use_minus

    if(exp_installed is None):
      self._get_fixed_product_installed = self._get_fixed_product_use_installed
    elif(exp_installed is repository.config.exp_installed.inst_newuse):
      self._get_fixed_product_installed = self._get_fixed_product_use_user
    elif(exp_installed is repository.config.exp_installed.inst_all):
      self._get_fixed_product_installed = self._get_fixed_product_normal


  def _get_fixed_product_use_user(self, package):
    use = package._use_user.union(self._fixed_use).intersection(package._iuse_declared)
    return self._compute_fixed_product(package._iuse_declared, use)

  def _get_fixed_product_use_all(self, package):
    dom = self._fixed_iuse.intersection(package._iuse_declared)
    use = self._fixed_use.intersection(package._iuse_declared)
    return self._compute_fixed_product(dom, use)

  def _get_fixed_product_use_plus(self, package):
    dom = package._use_user.union(self._fixed_iuse).intersection(package._iuse_declared)
    use = package._use_user.union(self._fixed_use).intersection(package._iuse_declared)
    return self._compute_fixed_product(dom, use)

  def _get_fixed_product_use_minus(self, package):
    dom = package._iuse_declared.difference(package._use_user).union(self._fixed_iuse).intersection(package._iuse_declared)
    return self._compute_fixed_product(dom, self._fixed_use)

  def _get_fixed_product_use_installed(self, package):
    use = package._use_installed.union(self._fixed_use).intersection(package._iuse_declared)
    return self._compute_fixed_product(package._iuse_declared, use)

  @staticmethod
  def _compute_fixed_product(dom, use):
    return { iuse:(iuse in use) for iuse in dom }


  # 3. SETUP: the filter_constraint method
  def _setup_filter_constraint(self, exp_installed):
    """ Setup the constraint of installed package w.r.t. the repository configuration.
    Parameter:
      exp_installed (repository.config.exp_installed): the installed package exploration model
    """
    def res(installed, constraint):
      if(installed and (exp_installed is None)): return repo_emptyconstraint
      else: return constraint
    self._filter_constraint = res


  #######################################
  # 3. PACKAGE CONSTRUCTION 
  #######################################

  # translate use flags into features and reciprocally
  _iuse_separator = "%"
  def _compute_feature_from_iuse(self, cpv, iuse):
    if(iuse in self._fixed_iuse): return "{}{}".format(repository._iuse_separator, iuse)
    else: return "{}{}{}".format(cpv, repository._iuse_separator, iuse)
  @staticmethod
  def feature_is_package(f): return repository._iuse_separator not in f
  @staticmethod
  def feature_is_iuse(f): return repository._iuse_separator in f
  @staticmethod
  def feature_deconstruct(f): return f.split(repository._iuse_separator, 1)


  # loads a package from the normal portage tree
  def _build_package_from_config(self, cpv):
    self._config.setcpv(cpv, mydb=portage.portdb)
    installed = self.is_package_installed(cpv)
    use_installed = string_to_frozenset(self._vardb.aux_get(cpv, ['USE'])[0]) if(installed) else None
    eapi = int(self._config['EAPI'])
    slots = self._config['SLOT'].split("/")
    iuse_declared = frozenset(self._config['IUSE_EFFECTIVE'].split(' ') if(eapi > 4) else self._config['IUSE'].split(' '))
    use = string_to_frozenset(self._config['PORTAGE_USE'])
    res = package(
      cpv,
      self,
      eapi,
      slots[0],
      slots[1] if len(slots) > 1 else "0",
      frozenset(self._config['KEYWORDS'].split(' ')),
      iuse_declared,
      use,
      use_installed,
      self._filter_constraint(installed, self._config['REQUIRED_USE']),
      self._filter_constraint(installed, self._config['DEPEND']),
      self._filter_constraint(installed, self._config['BDEPEND']),
      self._filter_constraint(installed, self._config['RDEPEND']),
      self._filter_constraint(installed, self._config['PDEPEND']),
      self._config['LICENSE']
    )
    if(installed): res.set_fixed_product(self._get_fixed_product_installed(res))
    else: res.set_fixed_product(self._get_fixed_product_normal(res))
    return res


  # loads a package from the var tree, i.e., an installed package
  _build_package_from_vardb_keys = ('EAPI', 'SLOT', 'KEYWORDS', 'IUSE', 'USE', 'REQUIRED_USE', 'DEPEND', 'BDEPEND', 'RDEPEND', 'PDEPEND', 'LICENSE')
  def _build_package_from_vardb(self, cpv):
    config = dict(zip(repository._build_package_from_vardb_keys, self._vardb.aux_get(cpv, repository._build_package_from_vardb_keys)))
    eapi = int(config['EAPI'])
    slots = config['SLOT'].split("/")
    iuse_referenceable = string_to_frozenset(self._config['IUSE'])
    use_installed = string_to_frozenset(config['USE'])
    iuse_declared = use_installed.union(iuse_referenceable)
    res = package(
      cpv,
      self,
      eapi,
      slots[0],
      slots[1] if len(slots) > 1 else "0",
      frozenset(config['KEYWORDS'].split(' ')),
      iuse_declared,
      None,
      use_installed,
      self._filter_constraint(True, config['REQUIRED_USE']),
      self._filter_constraint(True, config['DEPEND']),
      self._filter_constraint(True, config['BDEPEND']),
      self._filter_constraint(True, config['RDEPEND']),
      self._filter_constraint(True, config['PDEPEND']),
      config['LICENSE']
    )
    res.set_fixed_product(self._get_fixed_product_use_installed(res))
    return res


# maybe it would be cleaner to manage everything with substitution, and only substitution...
# I'll check that. Is it less efficient? It shouldn't be: we always need to to a parse of the SPC tree, and the lookup in a dict is O(1)
# merging two dict (or copying) is in O(n)? if so, then that merging will take time! Maybe we don't need to merge, maybe we can just traverse the SPC several times, which isn't good for memory
# so restricting the set of packages and features right away is the way to go, to avoid too much data

  #def get_install_use(self, cpv):
  #  if(self._vardb.cpv_exists(cpv)):
  #    res = frozenset(self._vardb.aux_get(package, ['USE'])[0])
  #    package = self.get_package(cpv)
  #    return { k:(k in res) for k in package._product }
  #  else: return None

  # variant for computing the final spc, depending on the use configuration


#get_package = main_repository.get_package
#get_atom = main_repository.get_atom
#get_group = main_repository.get_group
