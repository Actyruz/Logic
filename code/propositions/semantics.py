""" (c) This file is part of the course
    Mathematical Logic through Programming
    by Gonczarowski and Nisan.
    File name: code/propositions/semantics.py """

from propositions.proofs import *


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
