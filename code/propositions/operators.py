""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/propositions/operators.py """

from propositions.semantics import *
import copy



binary_only_not_or={'->':Formula.parse_prefix('(~p|(p&q))')[0],
                    '+':Formula.parse_prefix('((p&~q)|(~p&q))')[0],
                    '<->':Formula.parse_prefix('((p&q)|(~p&~q))')[0],
                    '-&':Formula.parse_prefix('~(p&q)')[0],
                    '-|':Formula.parse_prefix('~(p|q)')[0],
                    'F':Formula.parse_prefix('(p&~p)')[0],
                    'T':Formula.parse_prefix('(p|~p)')[0]}

binary_nand={'|':Formula.parse_prefix('((p-&p)-&(q-&q))')[0],
             '~':Formula.parse_prefix('(p-&p)')[0],
             '+':Formula.parse_prefix('(((p-&p)-&q)-&((q-&q)-&p)))')[0],
             '<->':Formula('-&',Formula.parse_prefix('(((p-&p)-&q)-&((q-&q)-&p)))')[0]
                           ,Formula.parse_prefix('(((p-&p)-&q)-&((q-&q)-&p)))')[0]),
             '->':Formula.parse_prefix('((p-&q)-&((p-&q)-&(p-&p)))')[0],
             '&':Formula.parse_prefix('((p-&q)-&(p-&q))')[0],
             '-|':Formula.parse_prefix('(((p-&p)-&(q-&q))-&((p-&p)-&(q-&q)))')[0],
             'T':Formula.parse_prefix('(p-&(p-&p))')[0],
             'F':Formula.parse_prefix('((p-&(p-&p))-&(p-&(p-&p)))')[0]
             }

binary_not_and={'|':Formula.parse_prefix('~(~p&~q)')[0],
                '-|':Formula.parse_prefix('~~(~p&~q)')[0],
                '-&':Formula.parse_prefix('~(p&q)')[0],
                '<->':Formula.parse_prefix('~~(~(p&~q)&~(~p&q))')[0],
                '->':Formula.parse_prefix('~(~(p&q)&p)')[0],
                '+':Formula.parse_prefix('~(~(p&~q)&~(~p&q))')[0],
                'T':Formula.parse_prefix('~(p&~p)')[0],
                'F':Formula.parse_prefix('~~(p&~p)')[0]
                }

binary_logical_and_not={'&':Formula.parse_prefix('~(p->~(p->q))')[0]}
replace_not_with_f={'~':Formula.parse_prefix('(p->F)')[0]}

def to_not_and_or(formula):
    """ Return an equivalent formula that uses only the operators '~', '&',
        and '|'."""
    #deep copied since F / T changes in the dict when i translate them for some reason i couldn't find.
    binary_only_not_or_dp=copy.deepcopy(binary_only_not_or)
    return formula.substitute_operators(binary_only_not_or_dp)
    # Task 3.5

def to_not_and(formula):
    """ Return an equivalent formula that uses only the operators '~' and '&'.

    """
    #deep copied since F / T changes in the dict when i translate them for some reason i couldn't find.
    deep_copy_binary_not=copy.deepcopy(binary_not_and)
    return formula.substitute_operators(deep_copy_binary_not)
    # Task 3.6a

def to_nand(formula):
    """ Return an equivalent formula that uses only the operator '-&'. """
    # Task 3.6b
    #deep copied since F / T changes in the dict when i translate them for some reason i couldn't find.
    deep_copy_binary_nand=copy.deepcopy(binary_nand)
    return formula.substitute_operators(deep_copy_binary_nand)



def to_implies_not(formula):
    """ Return an equivalent formula that uses only the operators '->' and '~'.
    """
    # Task 3.6c
    #deep copied since F / T changes in the dict when i translate them for some reason i couldn't find.
    first_formula=to_not_and(formula)
    deep_copy_binary_logical_and_not=copy.deepcopy(binary_logical_and_not)
    return first_formula.substitute_operators(deep_copy_binary_logical_and_not)


def to_implies_false(formula):
    """ Return an equivalent formula that uses only the operators '->' and 'F'.
    """
    #deep copied since F / T changes in the dict when i translate them for some reason i couldn't find.
    deep_copy_replace_not_with_f=copy.deepcopy(replace_not_with_f)
    implies_not_rep=to_implies_not(formula)
    return  implies_not_rep.substitute_operators(deep_copy_replace_not_with_f)
    # Task 3.6d
