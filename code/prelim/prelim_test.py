""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/prelim/prelim_test.py """

from prelim.prelim import half

def test_half(debug=False):
    if debug:
        print("Testing half of 42")
    z = half(42)
    assert z+z == 42
    if debug:
        print("Testing half of 8")
    z = half(8)
    assert z+z == 8


def test_all(debug=False):
    test_half(debug)
