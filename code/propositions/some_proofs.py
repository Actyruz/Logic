""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/propositions/some_proofs.py """


from propositions.axiomatic_systems import *

# from propositions.deduction import *

# Some Inferece Rules that only use conjunction
AA1 = InferenceRule([Formula.parse('(x&y)')],Formula.parse('x'))
AA2 = InferenceRule([Formula.parse('(x&y)')],Formula.parse('y'))
AA3 = InferenceRule([Formula.parse('x'), Formula.parse('y')],
                    Formula.parse('(x&y)'))

def prove_and_commutativity():
    """ Return a Proof object that gives a valid proof for the conclusion
     '(q&p)' from the single assumption '(p&q)' using the inference rules
     AA1, AA2, AA3 """
    # Task 4.7
    l1=Proof.Line(Formula.parse_prefix("(p&q)")[0])
    l3=Proof.Line(Formula.parse_prefix("p")[0],AA1,[0])
    l2=Proof.Line(Formula.parse_prefix("q")[0],AA2,[0])
    l4=Proof.Line(Formula.parse_prefix("(q&p)")[0],AA3,[1,2])
    lines=[l1,l2,l3,l4]
    conclusion=InferenceRule([Formula.parse_prefix("(p&q)")[0]],Formula.parse_prefix("(q&p)")[0])
    newProfe=Proof(conclusion,set([AA1,AA2,AA3]),lines)
    return newProfe



def prove_implies_self():
    """ Return a valid deductive proof of IO (i.e., '(p->p)') via MP, I1, I2 """
    # Task 4.8
    l1 = Proof.Line(Formula.parse('((p->((p->p)->p))->((p->(p->p))->(p->p)))'), I2, [])
    l2 = Proof.Line(Formula.parse('(p->((p->p)->p))'), I1, [])
    l3 = Proof.Line(Formula.parse('((p->(p->p))->(p->p))'), MP, [1,0])
    l4 = Proof.Line(Formula.parse('(p->(p->p))'), I1, [])
    l5 = Proof.Line(Formula.parse('(p->p)'), MP, [3,2])
    lines=[l1,l2,l3,l4,l5]
    conclusion=I0
    newProof = Proof(conclusion, set([MP, I1, I2]), lines)
    return newProof

# Hypothetical syllogism
HS = InferenceRule([Formula.parse('(p->q)'), Formula.parse('(q->r)')],
                   Formula.parse('(p->r)'))

def prove_hypothetical_syllogism():
    """ Return a valid deductive proof of HS via MP, I0, I1, I2 """
    # Task 5.5

def prove_I3():
    """ Return a proof for I3 via a subset of {MP,I0,I1,I2,N} """
    # Optional Task 6.7a

# Double negation elimination
DNE = InferenceRule([], Formula.parse('(~~p->p)'))

def prove_DNE():
    """ Return a proof for DNE via a subset of {MP,I0,I1,I2,N} """
    # Optional Task 6.7b

def prove_NN():
    """ Return a proof for NN via a subset of {MP,I0,I1,I2,N} """
    # Optional Task 6.7c

# Encoded Modus Tollens
EMT = InferenceRule([], Formula.parse('((p->q)->(~q->~p))'))

def prove_EMT():
    """ Return a proof for EMT via a subset of {MP,I0,I1,I2,N} """
    # Optional Task 6.7d

def prove_NI():
    """ Return a proof for NI via a subset of {MP,I0,I1,I2,N} """
    # Optional Task 6.7e

NPPP = InferenceRule([Formula.parse('(~p->p)')], Formula.parse('p'))

def prove_NPPP():
    """ Return a proof for NPPP via a subset of {MP,I0,I1,I2,N} """
    # Optional Task 6.7f

def prove_R():
    """ Return a proof for R via a subset of {MP,I0,I1,I2,N} """
    # Optional Task 6.7g

def prove_N():
    """ Return a proof for N via a subset of {MP,I0,I1,I2,N_ALTERNATIVE} """
    # Optional Task 6.8

def prove_NA1():
    """ Return a proof for NA1 via a subset of {MP,I0,I1,I2,N,A2} """
    # Optional Task 6.9a

def prove_NA2():
    """ Return a proof for NA2 via a subset of {MP,I0,I1,I2,N,A3} """
    # Optional Task 6.9b

def prove_NO():
    """ Return a proof for NO via a subset of {MP,I0,I1,I2,N,O3} """
    # Optional Task 6.9c
