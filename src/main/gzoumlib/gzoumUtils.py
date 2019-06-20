#!/usr/bin/python

__author__ = "Michael Lienhardt"
__copyright__ = "Copyright 2018, Michael Lienhardt"
__license__ = "GPL3"
__version__ = "1"
__maintainer__ = "Michael Lienhardt"
__email__ = "michael lienhardt@laposte.net"
__status__ = "Prototype"

import re

# Simple containers for constants and enums

class container(object):
  def __init__(self, **kwargs): self.__dict__.update(kwargs)


# Simple skeleton for visitors
class element(object):
  def accept(self, visitor): return getattr(visitor, self.__class__.__name__)(self)

class visitor(object):
  def visit(self, el): return getattr(self, el.__class__.__name__)(el)


# flattening list, taken from http://rightfootin.blogspot.com/2006/09/more-on-python-flatten.html
def flatten(l, ltypes=(list, tuple, frozenset)):
  ltype = type(l)
  l = list(l)
  i = 0
  while i < len(l):
    while isinstance(l[i], ltypes):
      if not l[i]:
        l.pop(i)
        i -= 1
        break
      else:
        l[i:i + 1] = l[i]
    i += 1
  return ltype(l)


def dictmerge(*args):
  if(len(args) is 0): return {}
  else:
    res = args[0].copy()
    for i in range(1,len(args)): res.update(args[i])
    return res

# add attribute to a class, taken from https://medium.com/@mgarod/dynamically-add-a-method-to-a-class-in-python-c49204b85bd6
def add_method(cls, name=None):
  def decorator(func):
    setattr(cls, name if(name != None) else func.__name__, func)
    return func # returning func means func can still be used normally
  return decorator


# replace several substrings in one go, taken from https://gist.github.com/bgusach/a967e0587d6e01e889fd1d776c5f3729
def multireplace(string, replacements):
  substrs = sorted(replacements, key=len, reverse=True)
  regexp = re.compile('|'.join(map(re.escape, substrs)))
  return regexp.sub(lambda match: replacements[match.group(0)], string)

# useful dict of list method
class dictlist(dict):
  def add(self, k, v):
    l = self.get(k)
    if(l is None):
      l = [v]
      self[k] = l
    else: l.append(v)

emptyset = frozenset()


# Iterator combinator (not simple)

class subsetsit(object):
  __slots__ = "_ext_it", "_subit", "_include"
  def __init__(self,l, index=None):
    if(index == None): index = len(l)-1
    self._ext_it = l[index]
    self._include = False
    if(index > 0): self._subit = subsetsit(l, index - 1)
    else: self._subit = None

  def ext_get(self):
    if(self._subit == None):
      if(self._include): return self._ext_it.ext_get()
      else: return []
    else:
      res = self._subit.ext_get()
      if(self._include): res.extend(self._ext_it.ext_get())
      return res

  def ext_next(self):
    if(self._subit == None):
      if(self._include): self._ext_it.ext_next()
      else: self._include = True
    else:
      try: self._subit.ext_next()
      except StopIteration:
        if(self._include): self._ext_it.ext_next()
        else: self._include = True
        self._subit.ext_reset()

  def ext_reset(self):
    self._include = False
    self._ext_it.ext_reset()
    if(self._subit != None): self._subit.ext_reset()

  # standard API
  def __iter__(self): return self
  def next(self):
    if(self._include == None):
      self._include = False
      raise StopIteration
    else:
      res = self.ext_get()
      try:
        self.ext_next()
      except StopIteration:
        self._include = None
      return res




# to update and rename in "powerset"
class powerit(object):
  __slots__ = "_l", "_l_iter", "_val"
  def __init__(self, l):
    self._l = l
    self._l_iter = [ iter(d) for d in l ]
    self._val = None

  def __iter__(self): return self
  def next(self):
    if(self._val == None):
      self._val = [ it.next() for it in self._l_iter ]
      return list(self._val)
    else:
      for i, it in enumerate(self._l_iter):
        try:
          self._val[i] = it.next();
          return list(self._val)
        except StopIteration:
          self._l_iter[i] = iter(self._l[i])
          self._val[i] = self._l_iter[i].next();
      raise StopIteration
