#!/usr/bin/python

__author__ = "Michael Lienhardt"
__copyright__ = "Copyright 2019, Michael Lienhardt"
__license__ = "GPL3"
__version__ = "1"
__maintainer__ = "Michael Lienhardt"
__email__ = "michael lienhardt@onera.fr"
__status__ = "Prototype"

import lrparsing

#
# REQUIRED_USE AND *DEPEND GRAMMAR
#



CONSTRAINT_IMPLIES = '?'

CHOICE_STRING_OR = "||"
CHOICE_STRING_XOR = "^^"
CHOICE_STRING_AT_MOST_ONE = "??"
CHOICE_STRING_BINDING_OR = "||="

NEG_STRING_NONEG = ""
NEG_STRING_NEG = "!"
NEG_STRING_BLOCK = "!!"

re_use = r'[A-Za-z0-9][A-Za-z0-9+_@-]*'
re_slot = r'[A-Za-z0-9_][A-Za-z0-9+_.-]*'

re_all = (
  r'(~|((<|>)?=?))?'                   # version comparison for atoms
  + r'[0-9a-zA-Z_][0-9a-zA-Z.@/_+*-]*' # atoms or use flags
  + r'(:((('+ re_slot + r'(/' + re_slot + r')?)=?)|\*|=))?' # possible slot constraint
)

class CT(lrparsing.TokenRegistry):
  all_id = lrparsing.Token(re=re_all)
  # atom = token(re=re_atom) # it is never used because in conflict with "CT.use"
  # condition operators
  OR     = lrparsing.Token(CHOICE_STRING_OR)
  XOR    = lrparsing.Token(CHOICE_STRING_XOR)
  ONEMAX     = lrparsing.Token(CHOICE_STRING_AT_MOST_ONE)
  BINDING_OR = lrparsing.Token(CHOICE_STRING_BINDING_OR)
  NOT    = lrparsing.Token('!')
  IMPLIES    = lrparsing.Token('?')
  # special symbols
  LPAREN     = lrparsing.Token('(')
  RPAREN     = lrparsing.Token(')')
  LBRACKET   = lrparsing.Token('[')
  RBRACKET   = lrparsing.Token(']')
  # punctuation
  COMMA      = lrparsing.Token(',')
  EQ         = lrparsing.Token('=')
  PLUS       = lrparsing.Token('+')
  MINUS      = lrparsing.Token('-')


class Require(lrparsing.Grammar):
  condition = CT.NOT*(0,1) + CT.all_id + CT.IMPLIES  # condition
  choice = CT.OR | CT.ONEMAX | CT.XOR
  require_element = (CT.NOT*(0,1) +  CT.all_id) | ((condition | choice)*(0,1) + CT.LPAREN + lrparsing.THIS*() + CT.RPAREN)
  require = require_element*()
  START = require


class Depend(lrparsing.Grammar):
  condition = CT.NOT*(0,1) + CT.all_id + CT.IMPLIES  # condition
  choice = CT.OR | CT.ONEMAX | CT.XOR | CT.BINDING_OR                 # choice
  selection = (
    (CT.MINUS*(0,1) + CT.all_id + (CT.LPAREN + (CT.PLUS | CT.MINUS) + CT.RPAREN)*(0,1))
    | (CT.NOT*(0,1) + CT.all_id + (CT.LPAREN + (CT.PLUS | CT.MINUS) + CT.RPAREN)*(0,1) + (CT.EQ | CT.IMPLIES)*(0,1))
  )
  depend_element = (
    (CT.NOT*(0,2) + CT.all_id + (CT.LBRACKET + lrparsing.List(selection, CT.COMMA) + CT.RBRACKET)*(0,1))
    | ((condition | choice)*(0,1) + CT.LPAREN + lrparsing.THIS*() + CT.RPAREN)
  )
  depend = depend_element*()                                              # depend
  START = depend


lrparsing.compile_grammar(Require)
lrparsing.compile_grammar(Depend)


def get_tree_require(require_string): return Require.parse(require_string)[1]
def get_tree_depend(depend_string): return Depend.parse(depend_string)[1]