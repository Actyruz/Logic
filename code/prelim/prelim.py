""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/prelim/prelim.py """

def half(x):
    """ Given an even integer x, return a number z so that z+z=x """
    assert type(x) is int and x%2 == 0
    # Task 0.1
