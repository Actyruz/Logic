""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/propositions/proofs.py """

"""
EXPLANATION FOR ADDING SEMNATICS AGAIN

i needed to use functions from semantic in order judge if the lines in proofs are working.
im well aware that im code duplicating , but i  used google ALOT , and tried for hours with out finding any way
to terminate the circual calling which created importError names , the only way i could think of is creating another
file , in order to break the  circual loop or add it in the start of the proofs file.
i tried using another file but i recieved an error since its not a moudle recongizble by your tests , so the only way 
i had was to  add it in the top. 
my loop problem was that semantics used InferenceRule ,so i had to import it
while i used in  my own version of implenetaions for proofs i used
is_tautology in order to judge if some lines are working.
In this version , some proofs will call the this file , this file
i couldn't terminate the circual importing with out changing the whole structure of my code , which will take so much
time  , and will teach me nothing to rebuild it , since i arleady learned the needed material from this execrise.
Also , this course isn't about coding , its about understanding the course material so i hope it won't be  much as
critical."""

from propositions.syntax import *


def is_model(model):
    """ Is m a model over some set of variables? """
    for key in model:
        if not (is_variable(key) and type(model[key]) is bool):
            return False
    return True


def variables(model):
    """ Return the set of variables over which model is a model """
    return model.keys()



def evaluate_or(formula1, formula2, model):
    """evalute or"""
    return evaluate(formula1, model) or evaluate(formula2, model)


def evalute_and(formula1, formula2, model):
    """evalute and"""
    return evaluate(formula1, model) and evaluate(formula2, model)


def evalute_logical_conditional(formula1, formula2, model):
    """evalute Logical conditional"""
    f1_value = evaluate(formula1, model)
    f2_value = evaluate(formula2, model)
    return (not (f1_value) or f2_value)


def evalute_neg(formula, model):
    """evalute neg"""
    return not (evaluate(formula.first, model))


def evalute_nand(formula1,formula2,model):
    return not(evalute_and(formula1,formula2,model))

def evalute_eqvualince(formula1,formula2,model):
    return evaluate(formula1,model) == evaluate(formula2,model)

def evalute_xor(formula1,formula2,model):
    return evaluate(formula1,model) != evaluate(formula2,model)

def evalute_nor(formula1,formula2,model):
    return not(evaluate_or(formula1,formula2,model))



def evalute_binary(f1, f2, model, root):
    """evalute binary"""
    operator = root
    if (operator == "->"):
        return evalute_logical_conditional(f1, f2, model)
    if (operator == "&"):
        return evalute_and(f1, f2, model)
    if operator =="-&":
        return evalute_nand(f1, f2, model)
    if operator == '|':
        return evaluate_or(f1,f2,model)
    if operator=='-|':
        return evalute_nor(f1,f2,model)
    if operator=='<->':
        return evalute_eqvualince(f1,f2,model)
    if operator=='+':
        return evalute_xor(f1,f2,model)

def evalute_constant(constant):
    """evalute constant"""
    if (constant == 'T'):
        return True
    else:
        return False


def evaluate(formula, model):
    """ Return the truth value of the given formula in the given model """
    assert is_model(model) and type(formula) is Formula
    assert formula.variables().issubset(variables(model)), \
        'Missing value for variable(s): ' + str(formula.variables().difference(variables(model)))

    root = formula.root

    if (is_variable(root)):
        variable_value = model[root]
        return variable_value

    if (is_constant(root)):
        constant_value = evalute_constant(root)
        return constant_value

    if (is_unary(root)):
        neg_exp_value = evalute_neg(formula, model)
        return neg_exp_value
    if (is_binary(root)):
        first_formula = formula.first
        second_forumla = formula.second
        binary_exp_value = evalute_binary(first_formula, second_forumla, model, root)
        return binary_exp_value


def create_models_list(all_binary_values_N, variables):
    """Creates a model list from the given power of binary values in the right order."""
    models_list = []

    var_list = variables

    if type(variables) == set:
        var_list = sorted(list(variables))  # we get a dict , we need to sort it.

    if type(variables) == list:
        var_list = variables

    for values in all_binary_values_N:
        curr_model = {}
        curr_var_index = 0
        for var in variables:
            curr_model[var_list[curr_var_index]] = bool(int(values[curr_var_index]))
            curr_var_index += 1
        models_list.append(curr_model)
    return models_list


def all_models(variables):
    """ Return a list (or preferably, a more memory-efficient iterable) of all
        possible models over the variables in the given list of variables. The
        order of the models should be lexicographic according to the order of
        the variables in the given list, where False precedes True """
    for v in variables:
        assert is_variable(v)
    len_var_list = len(variables)
    all_binary_values_N = [str(bin(i)[2:]).zfill(len_var_list) for i in
                           range(pow(2, len_var_list))]  # '00','01,'10,'11'
    return create_models_list(all_binary_values_N, variables)  # all those
    # varations
    # Task 2.2


def truth_values(formula, models):
    """ Return a list (or preferably, a more memory-efficient iterable) of the
        respective truth values of the given formula in each model in the given
        list (or preferably, support models to be an arbitrary iterable) """
    assert type(formula) is Formula
    list_truth_values = []
    for model in models:
        list_truth_values.append(evaluate(formula, model))
    return list_truth_values

    # Task 2.3


# helpers functions for 2.4

def output_T_F(bool):
    if bool == True:
        return "T"
    else:
        return "F"


def hypen_for_form(form):
    """Create the hypen string needed for the formula"""
    differnce_hypen_expression = 2
    return num_of_hyphen(len(str(form)) + differnce_hypen_expression)


def num_of_hyphen(number):
    """create hypen string with the given number"""
    hypen_string = ""
    hypen = "-"
    for i in range(number):
        hypen_string += hypen
    return hypen_string


def spaces_string(amount):
    """Create spaces string , as much as needed"""
    spaces = ""
    blank_space = " "
    for i in range(amount):
        spaces += blank_space
    return spaces


def spaces_needed_per_expression(form):
    """calculate the number of needed spaces per line , decided by the expression"""
    spaces_difference_from_exp_length = -1
    return spaces_string(len(str(form)) + spaces_difference_from_exp_length)


def print_first_line(formula, formula_vars):
    """print the first line expression and variables."""
    print("| ", end="")
    for var in formula_vars:
        print(var + " | ", end="")
    print(str(formula) + " |")
    print("|", end="")


def print_hypens_correctly(formula, formula_vars, formula_str):
    """prints the middle line with the correnct number."""
    for var in formula_vars:
        print(hypen_for_form(var) + "|", end="")
    print(hypen_for_form(formula_str) + "|")


def print_values(all_poss_models, formula_vars, truth_value_list, formula_str):
    """prints all the table vars values and |"""
    i = 0
    for num in range(len(all_poss_models)):
        print("| ", end="")
        for var in formula_vars:
            print(output_T_F(all_poss_models[i][var]) + spaces_needed_per_expression(var) + " | ", end="")
        print(output_T_F(truth_value_list[i]) + spaces_needed_per_expression(formula_str) + " |")
        i += 1


def print_table_final(formula, formula_vars, formula_str, all_poss_models, truth_values_list, vars_len):
    """Combine all the needed ingerdients"""
    print_first_line(formula, formula_vars)
    print_hypens_correctly(formula, formula_vars, formula_str)
    print_values(all_poss_models, formula_vars, truth_values_list, formula_str)


def print_truth_table(formula):
    """ Print the truth table of the given formula """
    assert type(formula) is Formula

    # needed variables
    formula_vars = sorted(list(formula.variables()))
    formula_str = Formula.parse_prefix(str(formula))[0]
    all_poss_models = all_models(formula.variables())
    truth_values_list = truth_values(formula, all_poss_models)
    vars_len = len(formula_vars)

    print_table_final(formula, formula_vars, formula_str, all_poss_models, truth_values_list, vars_len)


def is_tautology(formula):
    """ Return whether the given formula is a tautology """
    assert type(formula) is Formula
    models = all_models(formula.variables())
    formula_truth_values_models = truth_values(formula, models)
    if False in formula_truth_values_models:
        return False
    else:
        return True

    # Task 2.5a




def is_contradiction(formula):
    """ Return whether the given formula is a contradiction """
    assert type(formula) is Formula
    models = all_models(formula.variables())
    formula_truth_values_models = truth_values(formula, models)
    if True in formula_truth_values_models:
        return False
    else:
        return True
    # Task 2.5b


def is_satisfiable(formula):
    """ Return whether the given formula is satisfiable """
    assert type(formula) is Formula
    models = all_models(formula.variables())
    formula_truth_values_models = truth_values(formula, models)
    if True in formula_truth_values_models:
        return True
    else:
        return False
    # Task 2.5c


def create_value_neg_true_list(model):
    """Create values list based on the model , example : recieve model {p:true p:false} out : [p , ~p]"""
    vars_negation_or_normal = []
    for var in model:
        if model[var] == True:
            vars_negation_or_normal.append(Formula(var))
        else:
            vars_negation_or_normal.append(Formula('~', Formula(var)))
    return vars_negation_or_normal


def handle_len_one_two(model_size, vars_negation_or_normal, opeartor):
    """Handle the special cases to avoid out of bound expection when vars number is 0 or 1"""
    if (model_size == 1):
        return vars_negation_or_normal[0]
    if (model_size == 2):
        return Formula(opeartor, vars_negation_or_normal[0], vars_negation_or_normal[1])


def emit_conjuction_expression(vars_negation_or_normal, model_size, operator):
    """Recieve model size , vars negation or normal based on the model and which opeartor we want the
    conjuction to be based on , and emit the currect conjuction of variables."""
    if_arleady_handeld_by_curr_formula=bool(model_size<=2)
    handle_out_of_bound=2
    starting_index=2

    curr_formula = Formula(operator, vars_negation_or_normal[0], vars_negation_or_normal[1])

    if (if_arleady_handeld_by_curr_formula):
        return curr_formula

    for i in range(model_size - handle_out_of_bound):
        next_formula = Formula(operator, curr_formula, vars_negation_or_normal[i + starting_index])#since curr formola
        curr_formula = next_formula                                                                #arleady cover 0,1


    return next_formula


def synthesize_for_model(model):
    """ Return a propositional formula in the form of a single clause that
        evaluates to True in the given model, and to False in any other model
        over the same variables """

    assert is_model(model)
    vars_negation_or_normal = create_value_neg_true_list(model)
    model_size = len(model)

    if (model_size == 1 or model_size == 2):
        return handle_len_one_two(model_size, vars_negation_or_normal, "&")

    return emit_conjuction_expression(vars_negation_or_normal, model_size, "&")

    # Task 2.6


def handle_no_true(models, num_of_vars):
    """Handle the case when no true values exists , and we need to return all false"""
    synthesis_list = []
    for model in models:
        synthesis_list.append(synthesize_for_model(model))
    return emit_conjuction_expression(synthesis_list, num_of_vars, '&')


def create_conjuction_list(models, values):
    """Create a conjuction list from the synthesize model"""
    conjuction_list = []
    for i in range(len(models)):
        if (values[i] == True):
            conjuction_list.append(synthesize_for_model(models[i]))
    return conjuction_list


def synthesize(models, values):
    """ Return a propositional formula in DNF that has the given list of
        respective truth values in the given list of models (or preferably,
        support models and values to be arbitrary iterables), which are all
        over the same nonempty set of variables """

    num_of_vars = len(models[0])

    conjuction_list = create_conjuction_list(models, values)
    num_of_truths_in_table = len(conjuction_list)

    if (num_of_truths_in_table == 0):
        return handle_no_true(models, num_of_vars)
    #safety check to not go out of bounds
    if (num_of_truths_in_table == 1 or num_of_truths_in_table == 2):
        return handle_len_one_two(num_of_truths_in_table, conjuction_list, "|")
    #if number of truths is bigger then 2 , emit conjuction expression as needed from conjuction list.
    return emit_conjuction_expression(conjuction_list, num_of_truths_in_table, '|')

    # Task 2.7


# Tasks for Chapter 4


def evaluate_inference(rule, model):
    """ Return whether the given inference rule holds in the given model """
    assert type(rule) is InferenceRule
    assert is_model(model)
    assumpitonValues=[]
    for assumpiton in rule.assumptions:
        assumpitonValues.append(evaluate(assumpiton,model))

    for assumptionValue in assumpitonValues:
        if(assumptionValue==False):
            return True

    if(evaluate(rule.conclusion,model)==False):
        return False
    return True


    # Task 4.2


def is_sound_inference(rule):
    """ Return whether the given inference rule is sound, i.e., whether its
        conclusion is a semantically correct implication of its assumptions """
    assert type(rule) is InferenceRule
    for model in all_models(rule.variables()):
        if not evaluate_inference(rule,model) : return False
    return True
    # Task 4.3



def checkConstnatExpression(variableRepDict,specialization,general):
    """
    Check if a constant , if it is a constant there is a need to handle it differently.
    :param variableRepDict:
    :param specialization:
    :param general:
    :return: None if invalid constant  use , true if everything is valid
    """
    # if the dict is empty , then we perhaps have constant only expression.
    if variableRepDict == {}:
        # if there are 0 variables in the dict ,and the specalztion got more then 0 , that means the general is only
        # constants , while the specailztion got variables that we cant map.
        if len(specialization.variables()) > 0: return None
        # if the length is 0 , and the dict is 0 , we got only constants on our hands.
        # but we learned in class that the only time it'll be is if the formula drags herself , so she have to
        # be exactly the same.
        if len(specialization.variables()) == 0:
            if (general != specialization): return None
    return True

def createPathForEachVarDict(generalPaths, specialization, general, variableRepDict):
    """
    For each Var , create a path using '0' and '1' only , it'll result in mapping all the vars ,
    therefor being able to return false if the specalize isn't mapped like the var as well.
    :param generalPaths:
    :param specialization:
    :param general:
    :param variableRepDict:
    :return: None if the mapping wasn't succes , working var dict if it was.
    """
    # go over each path , which equal to all the tree.
    for path in generalPaths:
        # Checks if the path even exist in the speciazltion tree , if the build is the same.
        if (not (checkIfPathExist(path, specialization))): return None
        # checks if the path got the same opeartors.
        if (not (checkIfPathGotSameOpeartors(general, specialization, path))): return None
        currPath = findFormulaInBinaryPath(general, path)
        # we dont want to add constants to the final values dict.
        if (is_constant(currPath.root)): continue
        # if we arleady have the curr path in dict , check if it got colliding values
        if str(currPath) in variableRepDict:
            if variableRepDict[str(currPath)] != findFormulaInBinaryPath(specialization, path): return None
        # create a spot to input the placeholder into.
        variableRepDict[str(currPath)] = 0
        variableRepDict[str(currPath)] = findFormulaInBinaryPath(specialization, path)
    return variableRepDict


def isLineInAssumptions(currLine,assumptions):
    """
    Check if curr line in assunptions
    :param currLine:
    :param assumptions:
    :return:
    """
    if currLine in assumptions:
        return True
    else:
        return False



def checkLineAssupmtionsCorrectionsAndCalledLinesCorrection(currLine,lineNumber):
    """
    Check line assupmtions number , if called before delcared.
    :param currLine:
    :param lineNumber:
    :return:
    """
    for i in currLine.assumptions:
        if i >= lineNumber: return False
    if (currLine.rule.assumptions != None):
        if (len(currLine.assumptions) != len(currLine.rule.assumptions)): return False


def proofVariableVersion(rule, withOrWithOutConclusion):
    """ Return the set of atomic propositions (variables) used in the
        assumptions and in the conclusion of self """
    varsSet = set()
    for formula in rule.assumptions:
        varsSet = varsSet.union(formula.variables())
    if (withOrWithOutConclusion == True):
        return varsSet.union(rule.conclusion.variables())
    else:
        return varsSet


def binaryAssingToWays(formula):
    """
    Will return us all the paths to varaibles , which will map us a binary tree.
    but it'll map it by all the ways possible to his variables.
    :param formula:
    :return:
    """
    if (is_variable(formula.root) or is_constant(formula.root)):
        return set([formula.binaryPath])
    if (is_binary(formula.root)):
        formula.first.binaryPath = formula.binaryPath + "0"
        formula.second.binaryPath = formula.binaryPath + "1"

        return binaryAssingToWays(formula.first).union(binaryAssingToWays(formula.second))

    if (is_unary(formula.root)):
        formula.first.binaryPath = formula.binaryPath + "0"
        return set(binaryAssingToWays(formula.first))


def checkIfPathGotSameOpeartors(generalFormula, specalizeFormula, path):
    """
    Traverse the tree and check if at every step in the path we got the same opeartors.
    :param generalFormula:
    :param specalizeFormula:
    :param path: binary rep of the path , when 0 is first and 1 is second.
    :return:
    """
    if is_variable(generalFormula.root): return True
    if is_constant(generalFormula.root):
        if generalFormula.root == specalizeFormula.root:
            return True
        else:
            return False
    if generalFormula.root == specalizeFormula.root:
        if (is_binary(generalFormula.root)):
            return checkIfPathGotSameOpeartors(generalFormula.first, specalizeFormula.first, path[1:]) \
                   and checkIfPathGotSameOpeartors(generalFormula.second, specalizeFormula.second, path[1:])
        if (is_unary(generalFormula.root)):
            return checkIfPathGotSameOpeartors(generalFormula.first, specalizeFormula.first, path[1:])


def findFormulaInBinaryPath(formula, path):
    """
    Just traverse the tree by the binary path to give us the path.
    :param formula:
    :param path: binary rep of the path , when 0 is first and 1 is second.
    :return: the formula placed at the path in the curr tree
    """
    for binary in path:
        if binary == '1': formula = formula.second
        if binary == '0': formula = formula.first
    return formula


def checkIfPathExist(path, formula):
    """
    Goes over the path and checks if it exist in the given tree , which size is always at least equal or bigger.
    if it reached till the end and there are still values there , it is legit.
    :param path: binary rep of the path , when 0 is first and 1 is second.
    :param formula:
    :return:
    """
    i = 0
    currFormula = formula
    while (i < len(path)):
        if (is_constant(currFormula.root) or is_variable(currFormula.root)): break
        if (is_binary(currFormula.root) or is_unary(currFormula.root)):
            if (path[i] == "0"):
                currFormula = currFormula.first
                i += 1
                continue
            if (path[i] == "1"):
                i += 1
                currFormula = currFormula.second
                continue
            i += 1
    if (i == len(path)): return True
    return False


def checkIfConclusionMatch(dict, generalConclusion, specConclusion):
    """
    Takes 2 conclusions , and check if the values they specalize are currect from the dict.
    :param dict: with values that say how is each var speaclize
    :param generalConclusion: the general conclsuoin
    :param specConclusion: spec conclsuion
    :return:
    """
    if (is_variable(generalConclusion.root)):
        if generalConclusion.root in dict.keys():
            if not dict[generalConclusion.root] == specConclusion: return False
            if is_constant(specConclusion.root): return False
            return True
    if (is_binary(generalConclusion.root)):
        return checkIfConclusionMatch(dict, generalConclusion.first, specConclusion.first) and checkIfConclusionMatch(
            dict, generalConclusion.second, specConclusion.second)

    if (is_unary(generalConclusion.root)):
        return checkIfConclusionMatch(dict, generalConclusion.first, specConclusion.first)
    return True


class InferenceRule:
    """ An inference rule, i.e., a list of zero or more assumed formulae, and a
        conclusion formula """

    def __init__(self, assumptions, conclusion):
        assert type(conclusion) is Formula
        assert type(assumptions) is list
        for assumption in assumptions:
            assert type(assumption) is Formula
        self.assumptions = assumptions
        self.conclusion = conclusion

    def __eq__(self, other):
        return (type(other) is InferenceRule and
                self.assumptions == other.assumptions and
                self.conclusion == other.conclusion)

    def __ne__(self, other):
        return not self == other

    def __hash__(self):
        return hash(str(self))

    def __repr__(self):
        return str([str(assumption) for assumption in self.assumptions]) + \
               ' ==> ' + "'" + str(self.conclusion) + "'"

    def variables(self):
        """ Return the set of atomic propositions (variables) used in the
            assumptions and in the conclusion of self """
        withConclusion = True
        return proofVariableVersion(self, withConclusion)

        # Task 4.1

    def specalizeEachAssupmtionsLoop(self,specialization_map,mapIndex,assumptionIndex,specializeRule):
        """
        Specalize Each assupmtions.
        :param specialization_map:
        :param mapIndex:
        :param assumptionIndex:
        :param specializeRule:
        :return:
        """
        if (len(specialization_map) > 0):
            while (mapIndex < len(specialization_map)):
                for formula in specializeRule.assumptions:
                    if (assumptionIndex < len(specializeRule.assumptions)):
                        specializeRule.assumptions[assumptionIndex] = formula.substitute_variables(specialization_map)
                        assumptionIndex += 1
                mapIndex += 1
        return specializeRule


    def specialize(self, specialization_map):
        """ Return the specialization of the self inference rule obtained by
            simultaneously substituting each variable that is a key in
            specialization_map with the formula to which this value is mapped
            by specialization_map """
        for variable in specialization_map:
            assert is_variable(variable)
            assert type(specialization_map[variable]) is Formula
        specializeRule = deepcopy(self)
        assumptionIndex = 0
        mapIndex = 0
        specializeRule=self.specalizeEachAssupmtionsLoop(specialization_map,mapIndex,assumptionIndex,specializeRule)
        specializeRule.conclusion = specializeRule.conclusion.substitute_variables(specialization_map)
        return specializeRule

        # Task 4.4

    @staticmethod
    def merge_specialization_maps(specialization_map1, specialization_map2):
        """ Given two dictionaries specialization_map1 and specialization_map2,
            each of which may be None (instead of being a dictionary), return a
            single dictionary containing all (key, value) pairs that appear in
            either dictionary. If one of specialization_map1 or
            specialization_map2 is None, or if some key appears in both
            specialization_map1 and specialization_map2 but with different
            values, also return None """
        assert specialization_map1 is None or type(specialization_map1) is dict
        assert specialization_map2 is None or type(specialization_map2) is dict

        if (specialization_map1 == None or specialization_map2 == None): return None
        for key1 in specialization_map1.keys():
            for key2 in specialization_map2.keys():
                if key1 == key2 and specialization_map1[key1] != specialization_map2[key2]: return None
        finalDict = deepcopy(specialization_map1)
        finalDict.update(specialization_map2)
        return finalDict

        # Task 4.5a





    @staticmethod
    def formula_specialization_map(general, specialization):
        """
        The idea i did is , it'll create a path bettwen every point from the root to a leaf in the general.
        It'll map all the tree of the forula , then i'll go over each path and check if she's legit.
        if the path exist in the specializition , if the operations are the same , if the constnat are the same.
        if there are different values for different variables..
        and i'll return none and according dict based on it.
        :param general:
        :param specialization:
        :return:
        """
        assert type(general) is Formula and type(specialization) is Formula
        generalPaths = list(binaryAssingToWays(general))  # recieve all the paths possible , which maps all the tree
        if (is_variable(general.root)): return {general.root: specialization}
        variableRepDict = {}
        variableRepDict=createPathForEachVarDict(generalPaths, specialization, general, variableRepDict)
        if(variableRepDict is None):return None
        if(checkConstnatExpression(variableRepDict,specialization,general) is None):return None
        return variableRepDict

        # Task 4.5b



    def createMapAndCheckCollidesAndMergs(self,specialization):
        """
        Create map that checks the valid of the maps , if there are any collides.

        :param specialization:
        :return: if everything is valid will reutrn a working specialztion map otherwise None
        """
        finalDict = {}
        if (len(self.assumptions) != len(specialization.assumptions)): return None
        # Take each var and spec formula and build a dict from them.
        for general, specializ in zip(self.assumptions, specialization.assumptions):
            currSpeicallzMap = InferenceRule.formula_specialization_map(general, specializ)
            # if the specaliztion map got coliding values , return none
            if (InferenceRule.formula_specialization_map(general, specializ) == None):
                return None
            else:
                finalDict = self.merge_specialization_maps(finalDict, currSpeicallzMap)
                # if the merge didn't work , return none
            if (finalDict == None): return None
        finalDict=self.checkConclusionSpecAndMerge(finalDict,specialization)
        return finalDict

    def checkConclusionSpecAndMerge(self,finalDict,specialization):
        """
        Checks if the conclusion spec match , if it is will merge.
        :param finalDict:
        :param specialization:
        :return: None if doesn't merge , final dict if does.
        """
        # if the conclusion isn't a speclaiztion , return none.
        ConclusionSpec = InferenceRule.formula_specialization_map(self.conclusion, specialization.conclusion)
        if (InferenceRule.formula_specialization_map(self.conclusion, specialization.conclusion) == None):
            return None
        else:
            finalDict = self.merge_specialization_maps(ConclusionSpec, finalDict)
            if (finalDict == None): return None
        return finalDict


    def checkVarsNotMatchin(self,specialization):
        """
        Check if the vars are matching.
        :param specialization:
        :return: None if they dont match , true if they do.
        """
        # if the conclusion got extra varaibles  that aren't in the assumptions, return None
        if (proofVariableVersion(self, True) != proofVariableVersion(self, False) and len(proofVariableVersion(self, False)) > 0 or
            proofVariableVersion(specialization, True) != proofVariableVersion(specialization, False)) and \
                len(proofVariableVersion(specialization, False)) > 0:
            return None
        return True

    def checkConclsuionMatch(self,finalDict,specialization):
        """
        Check if the conclusions match.
        :param finalDict:
        :param specialization:
        :return: true if they does match , None otherwise.
        """
        # Checks if the specalize conclusion got the correct value set in her , by the spec map.
        doesConclusionMatch = checkIfConclusionMatch(finalDict, self.conclusion, specialization.conclusion)
        if (finalDict != {}) and not doesConclusionMatch: return None
        return True


    def specialization_map(self, specialization):
        """ Return a dictionary specifying the (minimal) map by which the self
            rule specializes to the given specialization. Return None if
            specialization is fact not a specialization of self """

        assert type(specialization) is InferenceRule

        finalDict=self.createMapAndCheckCollidesAndMergs(specialization)

        if(finalDict is None): return None
        if(self.checkVarsNotMatchin(specialization) is None):return None
        if(self.checkConclsuionMatch(finalDict,specialization) is None): return None

        return finalDict

        # Task 4.5c

    def is_specialization_of(self, general):
        """ Is the self rule as specialization of the given general rule? """
        return general.specialization_map(self) is not None


class Proof:
    """ A deductive proof comprised of a statement of a "lemma" in the form of
        an inference rule, a set of inference rules that may be used in the
        proof, and a proof in the form of a list of lines that prove the lemma
        using these inference rules """

    def __init__(self, statement, rules, lines):
        assert type(statement) is InferenceRule
        assert type(rules) is set
        for rule in rules:
            assert type(rule) is InferenceRule
        assert type(lines) is list
        for line in lines:
            assert type(line) is Proof.Line
        self.statement = statement
        self.rules = rules
        self.lines = lines

    class Line:
        """ A line in a proof.  A line is comprised of a formula and a
            justification for it via an inference rule. The rule may be None,
            meaning that the line is simply one of the assumptions of the
            lemma being proven (rather than an actual conclusion of an
            inference rule), or it may be one of the inferenece rules of the
            proof, in which case a list of indices of previous lines in the
            proof that constitute the assumptions of a specialization of this
            rule should be supplied (if this rule is assuptionless, then an
            an empty list, and not None, should be specified), and the line
            formula itself should be the conclusion of this specialization """

        def __init__(self, formula, rule=None, assumptions=None):
            assert type(formula) is Formula
            if rule is not None:
                assert type(rule) is InferenceRule
                assert type(assumptions) is list
                for assumption in assumptions:
                    assert type(assumption) is int
            self.formula = formula
            self.rule = rule
            self.assumptions = assumptions

        def __repr__(self):
            if (self.rule is None):
                return str(self.formula)
            return str(self.formula) + ' Inference Rule ' + str(self.rule) + \
                   ((" on " + str(self.assumptions))
                    if len(self.assumptions) > 0 else '')

        def is_assumption(self):
            return self.rule is None

    def __repr__(self):
        r = 'Proof for ' + str(self.statement) + ' using inference rules:\n'
        for rule in self.rules:
            r += '  ' + str(rule) + '\n'
        r += "Lines:\n"
        for i in range(len(self.lines)):
            r += ("%3d) " % i) + str(self.lines[i]) + '\n'
        return r

    def rule_for_line(self, line_number):
        """ Returns the InferenceRule whose conclusion is the formula in the
            line whose number is given, and whose assumptions are the formulae
            in the lines specified as the assumptions of that line, in the
            order of the specificaions of the line numbers. Return None if that
            line is justified as an assumption """
        currLine = self.lines[line_number]
        current_line_assumptions = []
        if currLine.assumptions == None:
            if currLine in self.statement.assumptions: return None
            return InferenceRule([currLine.formula], currLine.formula)
        for i in currLine.assumptions:
            current_line_assumptions.append(self.lines[i].formula)
        return InferenceRule(current_line_assumptions, currLine.formula)

        # Task 4.6a



    def doesVarsMatch(self,currLine,currLineInterface):
        #Checks if their variables match
        varsSet = set()
        for lineNumber in currLine.assumptions:
            #Creates a set for vars
            currNormalLine = self.lines[lineNumber]
            varsSet = varsSet.union(currNormalLine.formula.variables())
        for lineNumber in currLine.assumptions:
            #check if vars match
            currLineLoopIR = self.rule_for_line(lineNumber)
            if (currLineLoopIR != None):
                if (varsSet != currLineInterface.variables()): return False

    def ifNotTautologyLineVarsMatch(self, curr_line):
        """
        Checks if the line and line conlusion aren't both a tautology , and the are not assumptiosn for the line
        the vars has to match
        :param curr_line:
        :return:
        """
        if (len(curr_line.assumptions) == 0 and not (is_tautology(curr_line.formula)
                                                     and is_tautology(curr_line.rule.conclusion))):
            cur_line_formula_vars = curr_line.formula.variables()
            if (cur_line_formula_vars != set()): return False


    def isLineAssupmtionsCheck(self, curr_line, line_number):
        if (curr_line.assumptions != None):
            for i in curr_line.assumptions:
                if i >= line_number: return False
            if (curr_line.rule.assumptions != None):
                if (len(curr_line.assumptions) != len(curr_line.rule.assumptions)): return False



    def createAssumptionsDictAndCheckIfValid(self, curr_line, curr_line_interface):
        """
        Check if assumptions are valid and create a dict if they are.
        :param curr_line:
        :param curr_line_interface:
        :return:
        """
        #Check if their spec match by creating a dict and comparing him , returing false if one of them is invalid.
        assumptions_rule_list = {}
        for currLineAssupmtion, currLineInterfaceAssupmtions \
                in zip(curr_line.rule.assumptions, curr_line_interface.assumptions):
            currLineMap = curr_line_interface.formula_specialization_map(currLineAssupmtion, currLineInterfaceAssupmtions)
            if currLineMap == None:
                return None
            else:
                assumptions_rule_list = InferenceRule.merge_specialization_maps(assumptions_rule_list, currLineMap)
                if (assumptions_rule_list == None): return None
        return assumptions_rule_list

    def doesConclusionMatchSpeczilation(self, curr_line, assumptions_rule_list):
        #also checking the last line , if the conclusion match the specaliztion of the rule in the last line
        shouldBeFinalLine = curr_line.rule.conclusion.substitute_variables(assumptions_rule_list)
        if (len(curr_line.assumptions) > 0):
            if shouldBeFinalLine != curr_line.formula: return False


    def lineValditionCasesCheck(self, currLine, line_number, currLineInterface, assumptions_rule_dict):
        """
        Checks edge cases for valdition.
        :param currLine:
        :param line_number:
        :param currLineInterface:
        :param assumptions_rule_dict:
        :return:
        """
        if(self.isLineAssupmtionsCheck(currLine,line_number) is False):return False
        if(self.ifNotTautologyLineVarsMatch(currLine) is False):return False
        if(self.doesVarsMatch(currLine,currLineInterface) is False): return False
        if(self.createAssumptionsDictAndCheckIfValid(currLine,currLineInterface) is None):return False
        if (currLine.rule not in self.rules):return False
        if(self.doesConclusionMatchSpeczilation(currLine, assumptions_rule_dict) is False):return False
        return True


    def is_line_valid(self, line_number):
        """ Does the line with the given number indeed validly follow from its
            justification? If the line rule is None, then return whether the
            line formula is an assumption of the proof. Otherwise, return
            whether the line formula is the conclusion of a specialization of
            one of the inference rules of this proof that is specified as the
            line rule, whose assumptions are the formulae of the lines by which
            the line is justified, in the order of the specification of the line
            numbers """
        # Task 4.6b
        currLine = self.lines[line_number]
        if currLine.rule == None: return isLineInAssumptions(currLine,self.statement.assumptions)
        curr_line_interface = self.rule_for_line(line_number)
        assumptions_rule_list=self.createAssumptionsDictAndCheckIfValid(currLine,curr_line_interface)
        return self.lineValditionCasesCheck(currLine,line_number,curr_line_interface,assumptions_rule_list)



    def is_valid(self):
        """ Return whether self indeed contains a valid proof of its claimed
            statement using its inference rules """

        for i in range(len(self.lines)):
            if (self.is_line_valid(i) == False):
                return False

        if (self.lines[len(self.lines) - 1].formula != self.statement.conclusion): return False

        return True

        # Task 4.6c

    def offending_line(self):
        """ For debugging: return an error message containing the line number
            and string representation of the first invalid line in self. Return
            None if all lines are valid """
        for i in range(len(self.lines)):
            if not self.is_line_valid(i):
                return "Invalid Line " + str(i) + ": " + str(self.lines[i])


# Chapter 5 tasks


def createSpecMap(deep_copy_proof,deep_copy_spec):
    currProofAssumptions=[]
    currProofConclusion=deep_copy_proof.lines[-1]
    for line in deep_copy_proof.lines:
        if line.rule==None:currProofAssumptions.append(line.formula)
    specalizeProof=InferenceRule(currProofAssumptions,currProofConclusion.formula)
    specMap=specalizeProof.createMapAndCheckCollidesAndMergs(deep_copy_spec)
    return specMap,specalizeProof,currProofAssumptions


def prove_specialization(proof, specialization):
    """ Given a proof of an inference rule and given a specialization of that
        rule, return a proof of the specialization using the same set of
        inference rules that is used in the given proof """
    assert type(proof) is Proof
    assert type(specialization) is InferenceRule
    assert specialization.is_specialization_of(proof.statement)


    deep_copy_proof=deepcopy(proof)
    deep_copy_spec=deepcopy(specialization)
    specializeFormula=[]
    speicalizeLine=[]
    specMap,specalizeProof,currProofAssumptions=createSpecMap(deep_copy_proof,deep_copy_spec)

    for line in deep_copy_proof.lines:
        specializeFormula.append(line.formula.substitute_variables(specMap))
    for spec_formula,curr_line in zip(specializeFormula,deep_copy_proof.lines):
        curr_line.formula=spec_formula
        speicalizeLine.append(curr_line)
    finalProof=Proof(deep_copy_spec,deep_copy_proof.rules,speicalizeLine)
    return finalProof




    # Task 5.1


def inline_proof_once(proof, line_number, lemma_proof):
    """ Given a proof and another proof that proves the inference rule that
        justifies the line in the first proof whose number is given, return a
        new proof where that line is replaced by the full (specialized) list of
        lines proving it from the lines by which it is justified. The resulting
        proof is a valid proof of the original statement using the set of rules
        that is the union of the rules used in the two given proofs, but where
        the rule that was originally used in the line with the given number is
        no longer used in the corresponding lines in the returned proof (and
        thus, this rule is used one less time in the returned proof than in the
        original proof) """
    assert type(proof) is Proof
    assert type(lemma_proof) is Proof
    assert proof.lines[line_number].rule == lemma_proof.statement

    c_proof=deepcopy(proof)
    c_lemma_proof=deepcopy(lemma_proof)



    assumptions=[]
    for i in proof.lines[line_number].assumptions:
        assumptions.append(proof.lines[i].formula)
    conclcusion=proof.lines[line_number].formula
    newRule=InferenceRule(assumptions,conclcusion)
    lemma_prove_spec=prove_specialization(lemma_proof,newRule)
    currLines=c_proof.lines
    newLineNumber=line_number-1
    del currLines[line_number]
    amount_of_lines_added=0
    for line in lemma_prove_spec.lines:
        if line.assumptions is not None:
            for index in range(len(line.assumptions)):
                line.assumptions[index]+=line_number-1
        if(line.formula not in assumptions):
            currLines.insert(newLineNumber,line)
            amount_of_lines_added+=1
        newLineNumber+=1
    for line in c_proof.lines[newLineNumber:]:
        if(line.assumptions is not None):
            for i in range(len(line.assumptions)):
                line.assumptions[i]+=amount_of_lines_added-1
    k=3
    c_proof.rules=c_proof.rules.union(lemma_proof.rules)
    print(c_proof)
    return c_proof



def inline_proof(main_proof, lemma_proof):
    """ Given a proof and a proof of an inference rule that is used (any number
        of times) in the main proof, return a new proof where all uses of the
        "lemma" inference rule are replaced by an inlined proof of (the
        appropriate specialization of) that rule from the lines by which it is
        justified. The resulting proof is a valid proof of the original
        statement using the set of rules that is the union of the rules used in
        both proofs but without the "lemma" inference rule """
    assert type(main_proof) is Proof
    assert type(lemma_proof) is Proof
    line_number=0
    newProof=Proof
    for line in main_proof.lines:
        if line.rule==lemma_proof.statement:
            newProof=inline_proof_once(main_proof,line_number,lemma_proof)
        line_number+=1
    main_proof.rules.discard(lemma_proof.statement)
    return newProof

    # Task 5.2b
