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

_iuse_separator = "%"
def feature_deconstruct(f): return f.split(_iuse_separator, 1)
def feature_is_package(f): return _iuse_separator not in f
def feature_is_iuse(f): return _iuse_separator in f


def manage_selection(local_package, prefix, use, default, suffix):
  #print("  managing use flag '{}'".format(use))
  if(use not in local_package._use_map):
    if(default is not None): local_use = default
    else: return False
  else: local_use = local_package.get_feature(use, local=False)
  return suffix(prefix(local_use)) # if suffix is not a conditional Implies or Iff, use might not be in package

def manage_selection_list(local_package, selection_list):
  res = [ manage_selection(local_package, *selection) for selection in selection_list]
  if(len(res) is 0): return local_package._name
  else: return gzl.And(local_package._name, *res)

def manage_node_choice(parse_tree):
  choice_string = parse_tree[1][1]
  if choice_string == syntax.CHOICE_STRING_OR: return gzl.Or
  if choice_string == syntax.CHOICE_STRING_XOR: return gzl.Xor
  if choice_string == syntax.CHOICE_STRING_AT_MOST_ONE: return gzl.Conflict
  if choice_string == syntax.CHOICE_STRING_BINDING_OR: return gzl.Or


class package(object):
  def __init__(self, name, repo, eapi, slot, subslot, keywords, iuse_declared, use, required_use, depend, bdepend, rdepend, pdepend, license):
    # core info on package
    self._repo = repo
    self._name = name
    self._eapi = eapi
    self._slot = slot
    self._subslot = subslot
    self._keywords = keywords
    self._iuse_declared = iuse_declared
    self._use = use
    self._fixed_product = None
    self._fixed_full_product_visitor = None
    self._required_use = required_use
    self._depend = depend
    self._bdepend = bdepend
    self._rdepend = rdepend
    self._pdepend = pdepend
    self._license = license

    self._tree_required_use = syntax.get_tree_require(self._required_use)
    self._tree_depend = syntax.get_tree_depend(self._depend)
    self._tree_bdepend = syntax.get_tree_depend(self._bdepend)
    self._tree_rdepend = syntax.get_tree_depend(self._rdepend)
    self._tree_pdepend = syntax.get_tree_depend(self._pdepend)

    # additional info on package name
    self._name_info = portage.versions.catpkgsplit(self._name, self._eapi)
    #print("{}[{}] => {}".format(self._name, self._eapi, self._name_info))
    if(self._name_info is None): self._group = None
    else: self._group = "{}/{}".format(self._name_info[0], self._name_info[1])

    # additional info for dependency analysis
    self._use_map = { iuse: self._feature_from_iuse(iuse) for iuse in self._iuse_declared }
    self._iuse_added = set()
    if(self._eapi < 5): self._decl_iuse_local() # in the eapi < 5, not all iuse are declared

    self._dep_atom = set()
    self._dep_package = set()

  def set_fixed_product(self, fixed_product):
    #print("l96 => {}: fixed product is {}".format(self._name, fixed_product))
    self._fixed_product = fixed_product

  def get_full_use(self):
    if(self._fixed_full_product_visitor is None): return None
    else: return self._fixed_full_product_visitor._true

  def compute_spc(self):
    if(self._fixed_full_product_visitor is None):
      fixed_full_product = dictmerge(self._fixed_product, *tuple(self._repo.get_package(cpv)._fixed_product for p in self._dep_package))
      self._fixed_full_product_visitor = gzl.SPC_SubstitutionVisitor(fixed_full_product)
      self._spc_required_use = self._get_spc_require(self._tree_required_use)
      self._spc_depend = self._get_spc_depend(self._tree_depend)
      self._spc_bdepend = self._get_spc_depend(self._tree_bdepend)
      self._spc_rdepend = self._get_spc_depend(self._tree_rdepend)
      self._spc_pdepend = self._get_spc_depend(self._tree_pdepend)

  def get_spc(self):
    self.compute_spc()
    res = frozenset().union(
      (el[0] for el in self._spc_required_use),
      (el[0] for el in self._spc_depend),
      (el[0] for el in self._spc_bdepend),
      (el[0] for el in self._spc_rdepend),
      (el[0] for el in self._spc_pdepend)
    )
    return gzl.Implies(self._name, gzl.And(res))

  def get_feature(self, iuse, local=True): return self._use_map.get(iuse)
    #res = self._use_map.get(iuse)
    #if((res is None) and local): # Allow to declare use flags only locally, for EAPI<5
    #  res = feature_from_iuse(iuse, self._name)
    #  self._use_map[iuse] = res
    #  self._product[res] = False
    #  self._iuse_added.add(iuse)
    #return res

  def _feature_from_iuse(self, iuse):
    if(iuse in self._repo._fixed_iuse): return "{}{}".format(_iuse_separator, iuse)
    else: return "{}{}{}".format(self._name, _iuse_separator, iuse)

  #######################################
  # COMPUTE THE USE FLAGS FROM PARSE TREE
  #######################################

  def _decl_iuse(self, iuse):
    res = self._feature_from_iuse(iuse)
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
    self._decl_iuse_require(self._tree_required_use)
    self._decl_iuse_depend(self._tree_depend)
    self._decl_iuse_depend(self._tree_bdepend)
    self._decl_iuse_depend(self._tree_rdepend)
    self._decl_iuse_depend(self._tree_pdepend)

  #######################################
  # COMPUTE THE SPC FROM PARSE TREE
  #######################################

  def _set_range(self, node):
    #print("{}: node[0]={}".format(len(node), node[0]))
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
      C = manage_node_choice(parse_tree[1])
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
    return tuple( (self._fixed_full_product_visitor.visit(self._get_spc_require_in(el)), self._parse_begin, self._parse_end) for el in parse_tree[1:])

  # 2. from depend
  def _get_spc_depend_element(self, parse_tree):
    if parse_tree[1][0].name == "choice":
      subs = tuple(self._get_spc_depend_element(el) for el in parse_tree if((len(el) > 0) and (el[0].name == "depend_element")))
      C = manage_node_choice(parse_tree[1])
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
      return neg(gzl.Or([ manage_selection_list(self._repo.get_package(local_cpv), selection_list) for local_cpv in dependencies ]))

  def _get_spc_depend_in(self, el):
    self._parse_begin = None
    self._parse_end = None
    self._set_range(el)
    return self._get_spc_depend_element(el)

  def _get_spc_depend(self, parse_tree):
    return tuple( (self._fixed_full_product_visitor.visit(self._get_spc_depend_in(el)), self._parse_begin, self._parse_end) for el in parse_tree[1:])
  

  ##########################################
  # DEPRECATED
  ##########################################

  #def is_installed(self): return self._installed_product is not None
  #def is_keyworded(self): return self._repo.is_package_keyworded(self._name)
  #def is_masked(self): return self._repo.is_package_masked(self._name)

  ## TODO: manage package live cycle
  ## WARNING: use the dependencies to know which sets of packages need to be loaded so we can correctly simplify the constraint w.r.t. the use flag selection

  #def get_features(self): return frozenset(self._use_map.keys())

  #def get_required_use(self): return self._required_use
  #def get_depend(self): return self._depend
  #def get_rdepend(self): return self._rdepend
  #def get_pdepend(self): return self._pdepend
  #def get_bdepend(self): return self._bdepend

  #def get_spc_required_use(self): return self.spc_from_require(self._required_use)
  #def get_spc_depend(self): return self.spc_from_depend(self._depend)
  #def get_spc_rdepend(self): return self.spc_from_depend(self._rdepend)
  #def get_spc_pdepend(self): return self.spc_from_depend(self._pdepend)
  #def get_spc_bdepend(self): return self.spc_from_depend(self._bdepend)

  #def get_core_spc(self):
  #  #print("loading constraint of package {}".format(self._name))
  #  if(self._core_spc is None):
  #    req = self.get_spc_required_use()
  #    dep = self.get_spc_depend()
  #    rdep = self.get_spc_rdepend()
  #    pdep = self.get_spc_pdepend()
  #    self._core_spc = gzl.SPC_SubstitutionVisitor(self._fixed_product).visit(gzl.Implies(self._name, gzl.And(req, dep, rdep, pdep)))
  #    #self._core_spc = gzl.Implies(self._name, gzl.And(req, dep, rdep, pdep))
  #  return self._core_spc



#
# PACKAGE REPOSITORY IMPLEMENTATION
#

repo_emptyset = frozenset()
repo_emptyconstraint = ''
def string_to_frozenset(el, sep=" "):
  if(len(el) is 0): return repo_emptyset
  else: return frozenset(el.split(sep))

class repository(object):
  class config(object):
    class exp_use(enum.Enum):
      use_all="all"
      use_plus="+"
      use_minus="-"
      def __str__(self): return self.value
    class exp_mask(enum.Enum):
      mask_all="all"
      mask_keyword="keyword"
      mask_mask="mask"
      def __str__(self): return self.value
    class exp_installed(enum.Enum):
      inst_all="all"
      inst_newuse="newuse"
      def __str__(self): return self.value
    __slots__ = "_use", "_mask", "_installed"
    def __init__(self, use=None, mask=None, installed=None):
      self._use = use
      self._mask = mask
      self._installed = installed

  __slots__ = (
    '_packages', '_atoms', '_groups', '_portdb', '_vardb', '_config',
    '_installed_packages', '_fixed_use', '_fixed_iuse', '_fixed_product',
    '_dummy_count', '_get_fixed_product', '_filter_constraint', 'get_atom'
  )
  def __init__(self, repo_conf):
    self._packages = {}
    self._atoms = {}
    self._groups = {}
    self._portdb = portage.portdb
    self._vardb = portage.db['/']['vartree'].dbapi
    self._config = portage.config(clone=portage.settings)

    self._installed_packages = frozenset(self._vardb.cpv_all()) # I do that because cpv_exists is a disk access...

    self._fixed_use = self._config.useforce.difference(self._config.usemask)
    self._fixed_iuse = self._config.useforce.union(self._config.usemask)
    self._fixed_product = { (_iuse_separator+iuse):(iuse in self._fixed_use) for iuse in self._fixed_iuse }

    self._setup_get_atom(repo_conf._mask)
    self._setup_get_fixed_product(repo_conf._use, repo_conf._installed)
    self._setup_filter_constraint(repo_conf._installed)

    self._dummy_count = 0 # for dummy packages



  # rest of the API (which includes get_spc and get_atom)
  def get_package(self, cpv):
    res = self._packages.get(cpv)
    if(res is None):
      if(self._portdb.cpv_exists(cpv)):
        res = self._build_package_from_config(cpv)
      elif(cpv in self._installed_packages):
        res = self._build_package_from_vardb(cpv)
      else: return None
      self._packages[cpv] = res
    return res

  def get_spc(self, cpv):
    package = self.get_package(cpv)
    return package.get_spc()

  def get_dummy_package(self, name=None, iuse=repo_emptyset, required_use=repo_emptyconstraint, depend=repo_emptyconstraint, bdepend=repo_emptyconstraint, rdepend=repo_emptyconstraint, pdepend=repo_emptyconstraint):
    if(name is None): name = '[dummy-{}]'.format(self._dummy_count)
    self._dummy_count = self._dummy_count + 1
    dummy_package = package(
      name, self, 7, '0', '0', # package name, repo, EAPI, SLOT, SUBSLOT
      repo_emptyset, iuse, repo_emptyset, # keyword, use_referenceable, use
      required_use, depend, bdepend, rdepend, pdepend, repo_emptyconstraint) # required_use, depend, bdepend, rdepend, pdepend, license
    dummy_package.set_fixed_product({})
    self._packages[name] = dummy_package
    return dummy_package


  def get_group(self, group):
    packages = [self.get_package(cpv) for cpv in self.get_atom(group)]
    slots = dictlist()
    for p in packages: slots.add(p._slot, p._name)
    res = [ gzl.Conflict(names) for names in slots.values() if(len(names) > 1) ]
    if(len(res) > 1): return gzl.And(res)
    elif(len(res) is 1): return res[0]
    else: return True

  def is_package_installed(self, cpv): return cpv in self._installed_packages
  def is_package_deprecated(self, cpv):
    if(self._portdb.cpv_exists(cpv)): return False
    elif(self.is_package_installed(cpv)): return True
    else: return None
  def is_package_keyworded(self, cpv): return 'missing keyword' in portage.getmaskingstatus(cpv, portdb=portage.portdb)
  def is_package_masked(self, cpv): return 'package.mask' in portage.getmaskingstatus(cpv, portdb=portage.portdb)

  def get_installed_packages(self): return self._installed_packages
  @staticmethod # get the atoms in the world set, makes sense...
  def get_required_depend():
    required_atoms = portage._sets.load_default_config(portage.settings, portage.db[portage.settings['EROOT']]).getSetAtoms('world')
    return ' '.join(required_atoms)


  ###########################################
  # local defs for implementation
  ###########################################

  # 1. SETUP: get_atom method
  def _setup_get_atom(self, exp_mask):
    if(exp_mask is None): res_tmp = self._get_atom_mask_none
    elif(exp_mask is repository.config.exp_mask.mask_all): res_tmp = self._get_atom_mask_all
    elif(exp_mask is repository.config.exp_mask.mask_keyword): res_tmp = self._get_atom_mask_keyword
    elif(exp_mask is repository.config.exp_mask.mask_mask): res_tmp = self._get_atom_mask_mask
    self.get_atom = lambda atom: frozenset(res_tmp(atom)).union(self._vardb.match(atom))

  @staticmethod
  def _get_atom_mask_none(atom): return portage.portdb.match(atom)
  @staticmethod
  def _get_atom_mask_all(atom): return portage.portdb.xmatch("match_all", atom)
  @staticmethod
  def _get_atom_mask_keyword(atom): return filter(repository._get_atom_mask_keyword_filter, portage.portdb.xmatch("match_all", atom))
  @staticmethod
  def _get_atom_mask_mask(atom): return filter(repository._get_atom_mask_mask_filter, portage.portdb.xmatch("match_all", atom))
  @staticmethod
  def _get_atom_mask_keyword_filter(cpv):
    l = portage.getmaskingstatus(cpv, portdb=portage.portdb)
    ll = len(l)
    return (ll is 0) or ((ll is 1) and (l[0] == 'missing keyword'))
  @staticmethod
  def _get_atom_mask_keyword_filter(cpv):
    l = portage.getmaskingstatus(cpv, portdb=portage.portdb)
    ll = len(l)
    return (ll is 0) or ((ll is 1) and (l[0] == 'package.mask'))


  # 2. SETUP: the _get_local_fixed_product method (this gives all the features that are externally set for a given package)
  def _setup_get_fixed_product(self, exp_use, exp_installed):
    def res(package, installed_use):
      #print("l478: {} vs {} => {}".format(exp_use.value, repository.config.exp_use.use_all.value, exp_use is repository.config.exp_use.use_all))
      if((installed_use is not None) and (exp_installed is None)): return self._get_fixed_product_none_installed(package, installed_use)
      elif(((installed_use is not None) and (exp_installed is repository.config.exp_installed.inst_newuse)) or ((installed_use is None) and (exp_use is None))):
        return self._get_fixed_product_none_uninstalled(package)
      elif(exp_use is repository.config.exp_use.use_all): return self._get_fixed_product_all(package)
      elif(exp_use is repository.config.exp_use.use_plus): return self._get_fixed_product_plus(package)
      elif(exp_use is repository.config.exp_use.use_minus): return self._get_fixed_product_minus(package)
      raise Exception()
    self._get_fixed_product = res

  def _get_fixed_product_none_installed(self, package, installed_use):
    return { feature:(iuse in installed_use) for iuse,feature in package._use_map.items() }

  def _get_fixed_product_none_uninstalled(self, package):
    use = package._use.union(self._fixed_use)
    return { feature:(iuse in use) for iuse,feature in package._use_map.items() }

  def _get_fixed_product_all(self, package): return self._fixed_product

  def _get_fixed_product_plus(self, package):
    return dictmerge({ package._use_map[f]:True for f in package._use }, self._fixed_product)

  def _get_fixed_product_minus(self, package):
    return dictmerge({ feature:True for iuse,feature in package._use_map.items() if(iuse not in package._use) }, self._fixed_product)

  # 3. SETUP: the filter_constraint method
  def _setup_filter_constraint(self, exp_installed):
    def res(installed, constraint):
      if(installed and (exp_installed is None)): return ''
      else: return constraint
    self._filter_constraint = res
    ## construction of the get_spc method w.r.t. use and config exploration
    #if(repo_conf._use is None): get_spc_tmp = self.get_spc_use_none
    #elif(repo_conf._use is repository.config.exp_use.use_all): get_spc_tmp = self.get_spc_use_all
    #elif(repo_conf._use is repository.config.exp_use.use_plus): get_spc_tmp = self.get_spc_use_plus
    #elif(repo_conf._use is repository.config.exp_use.use_minus): get_spc_tmp = self.get_spc_use_minus

    #if(repo_conf._config is None): self.get_spc = lambda package: self.get_spc_config_none(package, get_spc_tmp)
    #elif(repo_conf._config is repository.config.exp_config.conf_all): self.get_spc = get_spc_tmp
    #elif(repo_conf._config is repository.config.exp_config.conf_dep): self.get_spc = lambda package: self.get_spc_config_dependencies(package, get_spc_tmp)
    #elif(repo_conf._config is repository.config.exp_config.conf_use): self.get_spc = lambda package: self.get_spc_config_use(package, get_spc_tmp)


  #def _get_fixed_product_use_none(self, package): #return package.
  #  res = package.get_core_spc()
  #  subst = package._product.copy()
  #  for dep in package._dep_package: subst.update(self.get_package(dep)._product)
  #  return gzl.SPC_SubstitutionVisitor(subst).visit(res)
  #def get_spc_use_all(self, package): return package.get_core_spc()
  #def get_spc_use_plus(self, package):
  #  res = package.get_core_spc()
  #  subst = package._product.copy()
  #  for dep in package._dep_package: subst.update(self.get_package(dep)._product)
  #  return gzl.SPC_SubstitutionVisitor({ k:v for k,v in subst.items() if(not v) }).visit(res)
  #def get_spc_use_minus(self, package):
  #  res = package.get_core_spc()
  #  subst = package._product.copy()
  #  for dep in package._dep_package: subst.update(self.get_package(dep)._product)
  #  return gzl.SPC_SubstitutionVisitor({ k:v for k,v in subst.items() if(v) }).visit(res)

  # variant for getting atoms depending on masking status
  # no need to add boolean variable to encode their masking status: we just need to unmask the packages to install


  # variant for computing the final spc, depending on the config configuration
  #def get_spc_config_none(self, package, get_spc_tmp):
  #  if(self.is_package_installed(package._name)): return True
  #  else: return get_spc_tmp(package)
  #def get_spc_config_dependencies(self, package, get_spc_tmp):
  #  config = self.get_install_use(package._name)
  #  if(config is None): return get_spc_tmp(package)
  #  else: return gzl.SPC_SubstitutionVisitor(config).visit(package.get_core_spc())
  #def get_spc_config_use(self, package, get_spc_tmp):
  #  if(self.is_package_installed(package._name)): return get_spc_tmp(package)
  #  else:
  #    res = package.get_core_spc()
  #    subst = { p: self.is_package_installed(p) for p in res._dep_package }
  #    return gzl.SPC_SubstitutionVisitor(subst).visit(res)
      

  #######################################
  # 3. PACKAGE CONSTRUCTION 
  #######################################

  # loads a package from the normal portage tree
  def _build_package_from_config(self, cpv):
    self._config.setcpv(cpv, mydb=portage.portdb)
    installed = self.is_package_installed(cpv)
    installed_use = string_to_frozenset(self._vardb.aux_get(cpv, ['USE'])[0]) if(installed) else None
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
      self._filter_constraint(installed, self._config['REQUIRED_USE']),
      self._filter_constraint(installed, self._config['DEPEND']),
      self._filter_constraint(installed, self._config['BDEPEND']),
      self._filter_constraint(installed, self._config['RDEPEND']),
      self._filter_constraint(installed, self._config['PDEPEND']),
      self._config['LICENSE']
    )
    res.set_fixed_product(self._get_fixed_product(res, installed_use))
    return res
    ## computation of fixed product
    ## - if package is installed, and not newuse:
    ##    fixed_iuse_flags = decl_use
    ##    fixed_selected = USE from vardb
    ## - else:
    ##    fixed_iuse_flags = decl_use
    ##    fixed_selected = use_force
    ##    
    #fixed_use_selected = 
    #fixed_product = { use: (use in fixed_use_selected) for use in self._config.usemask.union(fixed_use_selected) }
    #use_selected = 

    #use_set = use_selected.union(iuse_declared)
    #product = { use: (use in use_selected) for use in use_set }


  # loads a package from the var tree, i.e., an installed package
  _build_package_from_vardb_keys = ('EAPI', 'SLOT', 'KEYWORDS', 'IUSE', 'USE', 'REQUIRED_USE', 'DEPEND', 'BDEPEND', 'RDEPEND', 'PDEPEND', 'LICENSE')
  def _build_package_from_vardb(self, cpv):
    config = dict(zip(repository._build_package_from_vardb_keys, self._vardb.aux_get(cpv, repository._build_package_from_vardb_keys)))
    eapi = int(config['EAPI'])
    slots = config['SLOT'].split("/")
    iuse_referenceable = string_to_frozenset(self._config['IUSE'])
    use = string_to_frozenset(config['USE'])
    iuse_declared = use.union(iuse_referenceable)
    res = package(
      cpv,
      self,
      eapi,
      slots[0],
      slots[1] if len(slots) > 1 else "0",
      frozenset(config['KEYWORDS'].split(' ')),
      iuse_declared,
      use,
      self._filter_constraint(True, config['REQUIRED_USE']),
      self._filter_constraint(True, config['DEPEND']),
      self._filter_constraint(True, config['BDEPEND']),
      self._filter_constraint(True, config['RDEPEND']),
      self._filter_constraint(True, config['PDEPEND']),
      config['LICENSE']
    )
    res.set_fixed_product(self._get_fixed_product_none_installed(res, use))
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
