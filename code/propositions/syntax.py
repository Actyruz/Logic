""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/propositions/syntax.py """


from copy import*


def reset_visited(formula):
    """
    Reset the visited for the opeartion sub function

    """
    if (is_variable(formula.root) or is_constant(formula.root)):
        formula.visited = False
    if (is_binary(formula.root)):
        formula.visited = False
        reset_visited(formula.first)
        reset_visited(formula.second)
    if (is_unary(formula.root)):
        formula.visited = False
        reset_visited(formula.first)



def sub_operator(formula, op):
    """
    replace the given parametrs with the agreed upon place holders.
    :param formula:  the formula
    :param op: place holders meaning , from the given formula
    :return:
    """
    bb = {}
    if (is_binary(formula.root)):
        bb = {'p': formula.first, 'q': formula.second}
    if (is_unary(formula.root) | is_constant(formula.root)):
        bb = {'p': formula.first}
    return substitute_variables(op, bb)


def sub_operators(formula, d):
    """
    I used post order width tree travesing , so i could start from the bottom up and repalce each opeartors ,
    and used a visited boolean for each formula , so it wont replace the operators twice.
    :param formula: the formula
    :param d: the opeartors we want to replace.
    :return: the corrected formula
    """
    if (formula.visited == True):
        return formula
    if ((is_binary(formula.root)) or is_unary(formula.root)):
        formula.first = sub_operators(formula.first, d)
        if (is_binary(formula.root)):
            formula.second = sub_operators(formula.second, d)
    if (is_variable(formula.root)):
        return formula
    if (is_binary(formula.root)):
        if (formula.root in d.keys()):
            formula = sub_operator(formula, d[formula.root])
            formula.visited = True
        return formula
    if (is_unary(formula.root)):
        if (formula.root in d.keys()):
            formula = sub_operator(formula, d[formula.root])
            formula.visited = True
        formula.first = sub_operators(formula.first, d)
        return formula
    if (is_constant(formula.root)):
        if (formula.root in d.keys()):
            return d[formula.root]
        return formula


def substitute_variables(formula, d):
    """ Return a formula that is derived from self by substituting
        for each variable v that is a key in d, the Formula d[v].
        E.g., if self is the formula "((p->p)|z)" and
        d={"p":Formula.parse("(q&r)") then the returned formula should
        be (a Formula object of) "(((q&r)->(q&r))|z)" """

    if (is_variable(formula.root) or is_constant(formula.root)):
        if (formula.root in d.keys()):
            if (type(d[formula.root]) == Formula):
                return d[formula.root]
            else:
                k = Formula.parse_prefix(d[formula.root])[0]
                return k
        else:
            return formula
    if (is_binary(formula.root)):
        first = substitute_variables(formula.first, d)
        second = substitute_variables(formula.second, d)
        return Formula(formula.root, first, second)
    if (is_unary(formula.root)):
        first = substitute_variables(formula.first, d)
        return Formula(formula.root, first)
    return formula


def is_variable(s):
    """ Is s an atomic proposition?  """
    return s[0] >= 'p' and s[0] <= 'z' and (len(s) == 1 or s[1:].isdigit())


def is_unary(s):
    """ Is s a unary operator? """
    return s[0] == '~'


def is_binary(s):
    """ Is s a binary operator? """
    return s in {'&', '|', '->', '+', '<->', '-&', '-|'}


def is_constant(s):
    """ Is s a constant? """
    return s == 'T' or s == 'F'


def is_expression_binary(s):
    """Checks if the expression given is a binary opeartion."""
    endBracket = count_parathnesses(s)  # recieve the closing parathesses
    if (endBracket == 0 and s[0] == '('):  # if we have an start, but we have a problem , let parse handle it in there.
        return True
    if (endBracket == 0):  # if even have a start , defeintly not binary.
        return False
    if (s[0] == "(" and s[endBracket] == ")"):  # if no problem , and the end and start are parathnesses , return true
        return True
    return False


def update_depth(s):
    """Update depth , bracket recieved."""
    if (s == "("):
        return 1
    if (s == ")"):
        return -1
    else:
        return 0


def handle_variable(s, length):
    "hanlde the variable prefix"
    i = 0
    while (i < length - 1):  # if we reachend something that isn't a digit , return the rest as postfix
        if (not (s[i + 1].isdigit())):
            return (Formula(s[:i + 1]), s[i + 1:])
        i = i + 1
    return (Formula(s), '')


def handle_unary(s, length):
    """hanlde the unary prefix"""
    if (length == 1):
        return (None, 'Unary opeartion with out expression')
    correctFormula, postfix = Formula.parse_prefix(s[1:])  # parse everything after the op and return it
    if (postfix != ''):
        return (Formula(s[0], correctFormula), postfix)  # if isn't vali return the postfix.
    else:
        return (Formula(s[0], correctFormula), '')


def handle_binary(s, length):
    """Handle the binary prefix"""
    indexParth = count_parathnesses(s)
    if (indexParth == 0):  # if 0 return , then we have an error.
        return (None, "Unmatched parathness")
    opeartor = ''
    indent = 0
    firstExpression, postOpeartor = Formula.parse_prefix(s[1:])  # parse the rest of the formula , with out "("
    if (len(postOpeartor) > 0):

        if (len(postOpeartor) > 1 and postOpeartor[0] in ['&', '|', '+']):
            opeartor = postOpeartor[0]
            indent = 1
        if (len(postOpeartor) > 2 and postOpeartor[0] + postOpeartor[1] in ['->', '-&', '-|']):
            opeartor = postOpeartor[0] + postOpeartor[1]
            indent = 2
        if (len(postOpeartor) > 3 and postOpeartor[0] + postOpeartor[1] + postOpeartor[2] in ['<->']):
            opeartor = postOpeartor[0] + postOpeartor[1] + postOpeartor[2]
            indent = 3

    if not is_binary(opeartor):
        return None, 'Unvalid formula'

    secondExpression = postOpeartor[indent:]
    firstFormula, ignore = Formula.parse_prefix(str(firstExpression))
    secondFormula, reminder = Formula.parse_prefix(secondExpression)

    if (firstFormula == None or secondFormula == None):
        return None, 'Unvalid Expression in binary'

    return (Formula(opeartor, firstFormula, secondFormula), reminder[1:])


def count_parathnesses(s):
    """Currenct function will count the number of parathesses , first of all to check if the scopes are correct.
        she'll also determine if we're facing more then a binary opeartion , example : (x|y|z) , by keeping for each
        parathnesses depth a counter , that determine how many binary opeartions he encounterd."""
    string_length = len(s)
    if ((string_length) == 0) | (s[0] != "("):  # if empty or doesn't start with parathesses , return 0
        return 0

    depth_tracker = dict()  # we're using a dict in order to maintain depth binary operation counters.
    # our needs from maintaining depths are changing values , and reciving values that we know
    # their name , so a hash table is the most efficent way.

    parathnessesDepth = 1  # always start with 1 , since if we're in this functions , a parathensees was encounterd.
    index = 1  # we arleady know the first char (parathnesses)

    max_curr_dept = 1  # maintain max depth to create values in hash tables before we use them
    while (
            parathnessesDepth != 0 and index < string_length):  # if we didn't exceed the max length , or the parathnesses
        # ended early , keep going.
        if (max_curr_dept < parathnessesDepth + 1):  # if new depth reached , update the dict and the max depth.
            depth_tracker[parathnessesDepth] = 0
            max_curr_dept += 1

        previous_depth = parathnessesDepth  # keep previous depth in order to know if we need to zero the last depth value

        parathnessesDepth += update_depth(s[index])

        if (
                previous_depth > parathnessesDepth):  # if we return to the same depth in different brackets , zero binary counter
            depth_tracker[previous_depth] = 0

        if_opeartor_1 = False
        if_opeartor_2 = False
        if_opeartor_3 = False
        if (s[index] in ['&', '|', '+']):
            op = s[index]
            index += 1
            if_opeartor_1 = True
        if (string_length - index > 2 and (s[index] + s[index + 1] in ['->', '-&', '-|'])):
            if_opeartor_2 = True
            index += 2
        if (string_length - index > 3 and s[index] + s[index + 1] + s[index + 2] in ['<->']):
            if_opeartor_3 = True
            index += 3

        if (if_opeartor_1 or if_opeartor_2 or if_opeartor_3):
            depth_tracker[parathnessesDepth] += 1
            if (depth_tracker[parathnessesDepth] > 1):  # more then 1 binary in the same? its trinay , error.
                return 0
        if (not (if_opeartor_3 or if_opeartor_2 or if_opeartor_1)):
            index += 1
    if (parathnessesDepth != 0):  # if we reached the end , and the parathenssesDepth isn't 0 , the nubmer isn't equal.
        return 0

    return index - 1




class Formula:
    """ A Propositional Formula """

    visited = False
    binaryPath=""

    def __init__(self, root, first=None, second=None):
        if is_constant(root) or is_variable(root):
            assert first is None and second is None
            self.root = root
        elif is_unary(root):
            assert type(first) is Formula and second is None
            self.root, self.first = root, first
        else:
            assert is_binary(root) and type(first) is Formula and \
                   type(second) is Formula
            self.root, self.first, self.second = root, first, second

    def __eq__(self, other):
        return str(self) == str(other)

    def __ne__(self, other):
        return str(self) != str(other)

    def __hash__(self):
        return hash(str(self))

    def getFirst(self):
        """I use the getter , when one of the childs is none , it mess up the recursion"""
        try:
            self.first
        except AttributeError:
            return None
        return self.first

    def getSecond(self):
        """I use the getter , when one of the childs is none , it mess up the recursion"""
        try:
            self.second
        except AttributeError:
            return None
        return self.second

    def __repr__(self):
        """ Return a string representation of self """
        finalString = ""

        if (is_unary(self.root)):  # If unary , then will be at the start.
            finalString = self.root + str(self.first)
        if (is_binary(self.root)):  # if binary , then between the values.
            finalString = "(" + str(self.first) + self.root + str(self.second) + ")"
        if (is_variable(self.root)):  # if we reached the atoms of the language  , just return them.
            return self.root
        if (is_constant(self.root)):
            return self.root
        return finalString

    def variables(self):
        """ Return the set of atomic propositions (variables) used in self
            I chose set a the data structure since we need to avoid repetition"""
        if (is_variable(self.root)):  # if variable , the atom we neeed , produce a set from the atom
            return {self.root}
        if (is_unary(self.root)):  # if unary , we only care about the first
            return self.first.variables()
        if (self.root == None or is_constant(self.root)):  # if empty or constant , return empty set
            return set()
        else:  # else it is binary , then union both of them.
            return self.first.variables().union(self.second.variables())



    def operators(self):
        """ Return the set of operators (including T and F) used in self """

        if (self == None):  # if one of the child is None , return empty set
            return set()
        if (is_binary(self.root) | is_unary(self.root) | is_constant(self.root)):
            # checkers to avoid None values
            if (self.getFirst() == None):
                first_set = set()
            else:
                first_set = self.getFirst().operators()
            if (self.getSecond() == None):
                second_set = set()
            else:
                second_set = self.getSecond().operators()

            operator = {self.root}
            return operator.union(first_set.union(second_set))
        if (is_variable(self.root)):
            return set()

        # Task 1.4

    # compress and divide this functions into sub function to make it more readble
    @staticmethod
    def parse_prefix(s):
        """ Parse a prefix of the string s into a formula.  Return a
           pair: the parsed formula and the unparsed suffix of the string.
           If no prefix of s is a valid formula then returned pair should
           be None and an error message, where the error message must
           be a string (with some human-readable content) """

        string_length = len(s)

        if (string_length == 0):  # if empty string
            return (None, '')
        if (s == ")"):  # if end of prefix , or start with a bad ) value , return ) as the prefix , and indicate that
            # it is None with the first value.
            return (None, ")")
        if (s[0] == ")"):
            return (None, s)

        if string_length > 1:
            if (s[0] == "-" and s[1] == ">") or s[0] == "|" or s[0] == "&" or (s[0] == "-" and s[1] == '&') or \
                    (s[0] == '-' and s[1] == '|') or (s[0] == '<' and s[1] == '-' and s[2] == '>'):
                if (not (s[-1] == ')')):
                    return None, 'Unvalid'
                return (s, s)

        if (is_variable(s[0])):
            return handle_variable(s, string_length)

        if (is_unary(s)):
            return handle_unary(s, string_length)

        if (is_constant(s[0])):
            rest, postfix = Formula.parse_prefix(s[1:])
            return (Formula(s[0]), postfix)

        if (is_expression_binary(s)):
            return handle_binary(s, string_length)

        return (None, "Unexcpeted Symbol")  # if all failed , reutrn unexpected symbol.

    @staticmethod
    def is_formula(s):
        """ Is s a valid formula? """
        assert type(s) is str
        formula, correctness = Formula.parse_prefix(s)
        if (formula != None):
            if (correctness == '' and formula.root != None):
                return True
        return False

        # Task 1.5

    @staticmethod
    def parse(s):
        """ Return a propositional formula whose infix representation is s """
        assert Formula.is_formula(s), "Expected formula; got " + s
        return Formula.parse_prefix(s)[0]
        # Task 1.6

    # Optional tasks for Chapter 1

    def prefix(self):
        """ Return a prefix representation of self """
        # Optional Task 1.7

    @staticmethod
    def from_prefix(s):
        """ Return a propositional formula whose prefix representation is s """
        assert type(s) is str
        # Optional Task 1.8

    # Tasks for Chapter 3

    def substitute_variables(self, d):
        """ Return a formula that is derived from self by substituting
            for each variable v that is a key in d, the Formula d[v].
            E.g., if self is the formula "((p->p)|z)" and
            d={"p":Formula.parse("(q&r)") then the returned formula should
            be (a Formula object of) "(((q&r)->(q&r))|z)" """
        for v in d:
            assert is_variable(v)
            assert type(d[v]) is Formula
        # didn't know how to use recursion when it is a method , and no idea how to fix it
        return substitute_variables(self, d)

        # Task 3.3

    def substitute_operators(self, d):
        """ Return a formula that is derived from self by replacing
            every operator op that is a key in d by the formula d[op] applied
            to its (zero or one or two) operands, where the first operand
            is used for every occurence of "p" in the formula and the second
            for every occurence of "q".  (In the case of the nullary operators
            F and T, d[op] itself is used.)  E.g. if self is the formula
            "((x&y)&~z)" and d={"&":Formula.parse("~(~p|~q)")} then the returned
            formula should be (a Formula object of): "~(~~(~x|~y)|~~z)" """
        for op in d:
            assert is_binary(op) or is_unary(op) or is_constant(op)
            assert d[op].variables().issubset({"p", "q"})
        # didn't know how to use recursion when it is a method , and no idea how to fix it
        reset_visited(self)
        final_opeartors = sub_operators(self, d)

        return final_opeartors

        # Task 3.4
