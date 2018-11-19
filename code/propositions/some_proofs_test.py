""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/propositions/some_proofs_test.py """

from propositions.syntax import *
from propositions.proofs import *
from propositions.axiomatic_systems import *
from propositions.some_proofs import *
from propositions.semantics import*

# Tests for InferenceRule:

def test_prove_and_commutativity(debug=True):
    __test_prove_inference(prove_and_commutativity,
                           InferenceRule([Formula.parse('(p&q)')],
                                         Formula.parse('(q&p)')),
                           {AA1, AA2, AA3}, debug)

def test_prove_implies_self(debug=False):
    __test_prove_inference(prove_implies_self, I0, {MP, I1, I2}, debug)

def test_prove_hypothetical_syllogism(debug=False):
    __test_prove_inference(prove_hypothetical_syllogism, HS, {MP, I0, I1, I2},
                           debug)

def test_prove_I3(debug=False):
    __test_prove_inference(prove_I3, I3, {MP,I0,I1,I2,N}, debug)

def test_prove_DNE(debug=False):
    __test_prove_inference(prove_DNE, DNE, {MP,I0,I1,I2,N}, debug)

def test_prove_NN(debug=False):
    __test_prove_inference(prove_NN, NN, {MP,I0,I1,I2,N}, debug)

def test_prove_EMT(debug=False):
    __test_prove_inference(prove_EMT, EMT, {MP,I0,I1,I2,N}, debug)

def test_prove_NI(debug=False):
    __test_prove_inference(prove_NI, NI, {MP,I0,I1,I2,N}, debug)

def test_prove_NPPP(debug=False):
    __test_prove_inference(prove_NPPP, NPPP, {MP,I0,I1,I2,N}, debug)

def test_prove_R(debug=False):
    __test_prove_inference(prove_R, R, {MP,I0,I1,I2,N}, debug)

def test_prove_N(debug=False):
    __test_prove_inference(prove_N, N, {MP,I0,I1,I2,N_ALTERNATIVE}, debug)

def test_prove_NA1(debug=False):
    __test_prove_inference(prove_NA1, NA1, {MP,I0,I1,I2,N,A2}, debug)

def test_prove_NA2(debug=False):
    __test_prove_inference(prove_NA2, NA2, {MP,I0,I1,I2,N,A3}, debug)

def test_prove_NO(debug=False):
    __test_prove_inference(prove_NO, NO, {MP,I0,I1,I2,N,O3}, debug)

def __test_prove_inference(prover, rule, rules, debug):
    if debug:
        print('Testing', prover.__qualname__)
    proof = prover()
    assert proof.statement == rule
    assert proof.rules.issubset(rules), \
        "got " + str(proof.rules) + ", expected " + str(rules)
    assert proof.is_valid(), proof.offending_line()

def test_ex4(debug=False):
    test_prove_and_commutativity(debug)
    test_prove_implies_self(debug)

def test_ex5(debug=False):
    test_prove_hypothetical_syllogism(debug)

def test_opt_ex6(debug=False):
    test_prove_I3(debug)
    test_prove_DNE(debug)
    test_prove_NN(debug)
    test_prove_EMT(debug)
    test_prove_NI(debug)
    test_prove_NPPP(debug)
    test_prove_R(debug)
    test_prove_N(debug)
    test_prove_NA1(debug)
    test_prove_NA2(debug)
    test_prove_NO(debug)

def test_all(debug=False):
    test_ex4(debug)
    test_ex5(debug)
    test_opt_ex6(debug)
