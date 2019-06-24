#!/usr/bin/python

__author__ = "Michael Lienhardt"
__copyright__ = "Copyright 2019, Michael Lienhardt"
__license__ = "GPL3"
__version__ = "1"
__maintainer__ = "Michael Lienhardt"
__email__ = "michael lienhardt@onera.fr"
__status__ = "Prototype"


from gzoumlib.gzoumUtils import element, visitor, container, flatten, add_method

#
# SIMPLE PROPOSITIONAL CONSTRAINT IMPLEMENTATION
#

class SPC(element):
  __slots__ = "_content"
  def __init__(self, *args): self._content = tuple(flatten(args))

@add_method(SPC)
def check(self, model): return truthVisitor(model).visit(self)
@add_method(SPC)
def toString(self, debug=False):
  if(debug): return toStringDebugVisitor().visit(self)
  else: return toStringVisitor().visit(self)
@add_method(SPC)
def getVariables(self): return getVariablesVisitor().visit(self)
@add_method(SPC)
def subst(self, subst): return SubstitutionVisitor(subst).visit(self)

class And(SPC): pass
class Or(SPC): pass
class Xor(SPC): pass
class Conflict(SPC): pass
class Not(SPC):
  def __init__(self, arg): self._content = arg
class Implies(SPC):
  def __init__(self, left, right): SPC.__init__(self, left, right)
class Iff(SPC):
  def __init__(self, left, right): SPC.__init__(self, left, right)


# check if the constraint is true from the given model
class SPC_truthVisitor(visitor):
  __slots__ = "_model"
  def __init__(self, model=None): self._model = model
  def set_model(self, model): self._model = model

  def visit(self, el): return self.manage_sub(el)
  def manage_sub(self, sub):
    if(isinstance(sub, str)): return (sub in self._model)
    elif(isinstance(sub, bool)): return sub
    else: return sub.accept(self)

  def And(self, el):
    for sub in el._content:
      if(not self.manage_sub(sub)): return False
    return True
  def Or(self, el):
    for sub in el._content:
      if(self.manage_sub(sub)): return True
    return False
  def Xor(self, el):
    res = False
    for sub in el._content:
      if(self.manage_sub(sub)):
        if(res): return False
        else: res = True
    return res
  def Conflict(self, el):
    seen = False
    for sub in el._content:
      if(self.manage_sub(sub)):
        if(seen): return False
        else: seen = True
    return True
  def Not(self, el):
    return not self.manage_sub(el._content)
  def Implies(self, el):
    return self.manage_sub(el._content[0]) or (not self.manage_sub(el._content[1]))
  def Iff(self, el):
    v1 =  self.manage_sub(el._content[1])
    v2 = self.manage_sub(el._content[0])
    return (v1 and v2) or (not (v1 or v2))

# give a string for the constraint
class toStringDebugVisitor(visitor):
  def visit(self, el): return self.manage_sub(el)
  def manage_sub(self, sub): return sub.accept(self) if isinstance(sub, SPC) else str(sub)

  def And(self, el): return "And({})".format(", ".join([ self.manage_sub(sub) for sub in el._content ]))
  def Or(self, el):  return "Or({})".format(", ".join([ self.manage_sub(sub) for sub in el._content ]))
  def Xor(self, el):  return "Xor({})".format(", ".join([ self.manage_sub(sub) for sub in el._content ]))
  def Conflict(self, el):  return "CNF({})".format(", ".join([ self.manage_sub(sub) for sub in el._content ]))
  def Not(self, el): return "Not({})".format(self.manage_sub(el._content))
  def Implies(self, el): return "Implies({}, {})".format(self.manage_sub(el._content[0]), self.manage_sub(el._content[1]))
  def Iff(self, el): return "Iff({}, {})".format(self.manage_sub(el._content[0]), self.manage_sub(el._content[1]))


# give the variables in the constraint
class getVariablesVisitor(visitor):
  __slots__ = "_store"
  def visit(self, el, var_set):
    self._store = var_set
    self.manage_sub(el)
    return self._store

  def manage_sub(self, sub):
    if(isinstance(sub, str)): self._store.add(sub)
    elif(isinstance(sub, bool)): pass
    else: sub.accept(self)

  def And(self, el):
    for sub in el._content: self.manage_sub(sub)
  def Or(self, el):
    for sub in el._content: self.manage_sub(sub)
  def Xor(self, el):
    for sub in el._content: self.manage_sub(sub)
  def Conflict(self, el):
    for sub in el._content: self.manage_sub(sub)
  def Not(self, el): return self.manage_sub(el._content)
  def Implies(self, el):
    for sub in el._content: self.manage_sub(sub)
  def Iff(self, el):
    for sub in el._content: self.manage_sub(sub)


# apply a substitution on the constraint and returns the result
class substitutionVisitor(visitor):
  __slots__ = '_true', '_false', '_constraints'
  def __init__(self, substitution):
    self.set_substitution(substitution)
  def set_substitution(self, substitution):
    self._true = set([ f for f,v in substitution.items() if(v is True) ])
    self._false = set([ f for f,v in substitution.items() if(v is False) ])
    self._constraints = [ Iff(f,v) for f,v in substitution.items() if((not(v is False)) and (not(v is True))) ]

  def visit(self, el):
    if(len(self._constraints) > 0):
      self._constraints.append(self.manage_sub(el))
      return And(*self._constraints)
    else: return self.manage_sub(el)

  # constraints
  def manage_sub(self, sub):
    if(isinstance(sub, str)):
      if(sub in self._true): return True
      elif(sub in self._false): return False
      else: return sub
    elif(isinstance(sub, bool)): return sub
    else: return sub.accept(self)

  def And(self, el):
    res = tuple( self.manage_sub(sub) for sub in el._content )
    if(False in res): return False
    else:
      res = tuple( i for i in res if(i != True) )
      if(len(res) is 0): return True
      elif(len(res) is 1): return res[0]
      else: return And(res)
  def Or(self, el):
    res = tuple( self.manage_sub(sub) for sub in el._content )
    if(True in res): return True
    else:
      res = tuple( i for i in res if(i is not False) )
      if(len(res) is 0): return False
      elif(len(res) is 1): return res[0]
      else: return Or(res)
  def Xor(self, el):
    res = tuple( self.manage_sub(sub) for sub in el._content )
    seen = False
    val = True
    for el in res:
      if(el is True):
        if(seen): return False
        else: seen = True
      elif(el is not False): val = False
    if(val): return seen
    else:
      res = tuple(filter(lambda x: x not in (False, True), res))
      if(seen):
        if(len(res) is 1): return Not(res[0])
        else: return And(tuple(Not(el) for el in res))
      else: return Xor(res)
  def Conflict(self, el):
    res = tuple( self.manage_sub(sub) for sub in el._content )
    seen = False
    val = True
    for el in res:
      if(el is True):
        if(seen): return False
        else: seen = True
      elif(el is not False): val = False
    if(val): return True
    else:
      res = tuple(filter(lambda x: x not in (False, True), res))
      if(seen):
        if(len(res) is 1): return Not(res[0])
        else: return And(tuple(Not(el) for el in res))
      else: return Xor(res)
  def Not(self, el):
    res = self.manage_sub(el._content)
    if(res is True): return False
    elif(res is False): return True
    else: return Not(res)
  def Implies(self, el):
    res_left, res_right = tuple( self.manage_sub(sub) for sub in el._content )
    if((res_left is False) or (res_right is True)): return True
    elif(res_left is True):
      if(res_right is False): return False
      else: return res_right
    elif(res_right is False): return Not(res_left)
    else: return Implies(res_left, res_right)
  def Iff(self, el):
    res_left, res_right = tuple( self.manage_sub(sub) for sub in el._content )
    if(res_left is False):
      if(res_right is False): return True
      elif(res_right is True): return False
      else: return Not(res_right)
    elif(res_left is True):
      if(res_right is False): return False
      elif(res_right is True): return True
      else: return res_right
    else:
      if(res_right is False): return Not(res_left)
      elif(res_right is True): return res_left
      else: return Iff(res_left, res_right)


#
# ADD Z3 SUPPORT
#

try:
  import z3
  z3_loaded = True
except ImportError:
  z3_loaded = False

if(z3_loaded):
  class Z3ModelIterator(object):
    __slots__ = "_vars", "_solver"
    def __init__(self, vars, constraints):
      self._vars = vars
      self._solver = z3.Solver()
      #for c in constraints: self._solver.add(c)
      self._solver.add(constraints)
    def __iter__(self): return self
  
    def __next__(self):
      if(self._solver.check() == z3.sat):
        res = self._solver.model()
        self._solver.add(z3.Or([(z3.Not(var) if(res[var]) else var) for var in self._vars]))
        return [str(var) for var in self._vars if(res[var])] #[(str(var), res[var]) for var in self._vars]
      else: raise StopIteration
    def next(self): return self.__next__()


  class SPC_toZ3Visitor(visitor):
    __slots__ = "_var_map"
    def __init__(self):
      self._var_map = {}
  
    def visit(self, sub):
      #print(str(sub))
      if(isinstance(sub, str)):
        res = self._var_map.get(sub)
        if(res == None):
          res = z3.Bool(sub)
          self._var_map[sub] = res
        return res
      elif(isinstance(sub, bool)): return sub
      else: return sub.accept(self)
  
    def And(self, el): return z3.And(tuple( self.visit(sub) for sub in el._content ))
    def Or(self, el): return z3.Or(tuple( self.visit(sub) for sub in el._content ))
    def Xor(self, el):
      u = tuple(self.visit(sub) for sub in el._content)
      nb = len(u)
      if(nb > 2):
        res = [z3.Or(u)]
        for i in range(nb):
          res_conflict = tuple(u[j] for j in range(nb) if(j != i))
          res.append(z3.Implies(u[i], z3.Not(z3.Or(res_conflict))))
        return z3.And(res)
      elif(nb is 2):
        return z3.Xor(u[0], u[1])
      else: return u
    def Conflict(self, el):
      u = tuple(self.visit(sub) for sub in el._content)
      nb = len(u)
      if(nb > 1):
        res = []
        for i in range(nb):
          res_conflict = tuple(u[j] for j in range(nb) if(j != i))
          res.append(z3.Implies(u[i], z3.Not(z3.Or(res_conflict))))
        return z3.And(res)
      else: return u
    def Not(self, el): return z3.Not(self.visit(el._content))
    def Implies(self, el): return z3.Implies(self.visit(el._content[0]), self.visit(el._content[1]))
    def Iff(self, el): return self.visit(el._content[0]) == self.visit(el._content[1])

  @add_method(SPC)
  def getZ3Models(c):
    visitor = SPC_toZ3Visitor()
    z3_constraint = visitor.visit(c)
    return Z3ModelIterator(visitor._var_map.values(), z3_constraint)

  @add_method(SPC)
  def hasZ3Models(c):
    z3_constraint = SPC_toZ3Visitor().visit(c)
    solver = z3.Solver()
    solver.add(z3_constraint)
    return (solver.check() == z3.sat)

  

#def init_z3():
#  import z3
#  def 
