#[1] import libraries
import re
from sympy.logic.boolalg import to_cnf

#[2] Eliminate implication
def Eliminate_implication(s):
    chars = list(s)
    for i in range(len(chars)):
        if chars[i] == "→":
            chars[i] = "∨"
            chars[i - 4] = "¬" + chars[i - 4]
    return ''.join(chars)

#[3] Demorgan Law

def Demorgan(s):
    #replace ¬(a(b)∧c(d))
    pattern = r'\¬\(([a-zA-Z])\(([a-zA-Z])\)\∧([a-zA-Z])\(([a-zA-Z])\)\)'
    replacement = r'(¬\1(\2)∨¬\3(\4))'
    modified_string1 = re.sub(pattern, replacement, s)
    #replace ¬(a(b)∨c(d))
    pattern = r'\¬\(([a-zA-Z])\(([a-zA-Z])\)\∨([a-zA-Z])\(([a-zA-Z])\)\)'
    replacement = r'(¬\1(\2)∧¬\3(\4))'
    modified_string2 = re.sub(pattern, replacement, modified_string1)
    return modified_string2

#[4] Remove double-not
def Remove_double_not(s):
    return s.replace("¬¬" , "")

#[5] Standardize variable scope
def Standardize_variable_scope(s):
    vars = ['none','w', 'x', 'y', 'z']
    new_string = ""
    i = 0
    for ch in s:
        if ch == '∃' or ch == '∀':
            i += 1
        if ch in vars:
            ch = vars[i]
        new_string += ch
    return new_string

#[6] prenex form
def prenex_form(s):
    quantifiers = ""
    new_string = ""
    skip_next = False
    for i, ch in enumerate(s):
        if skip_next:
            skip_next = False
            continue
        if ch in ['∃', '∀']:
            quantifiers += ch + s[i + 1]
            skip_next = True
        else:
            new_string += ch
    return quantifiers + new_string

def Skolemization(s):
    result_string = ""
    prefix_vars = []  # To store variables introduced by universal quantifiers (∀)
    existential_vars = []  # To store variables that need to be replaced because they're introduced by existential quantifiers (∃)
    
    # First pass: Identify and process quantifiers and variables
    i = 0
    while i < len(s):
        if s[i] == '∀':
            prefix_vars.append(s[i+1])  # Add variable after ∀ to the prefix list
            result_string += s[i] + s[i+1]  # Keep ∀ and its variable in the result string
            i += 2  # Skip next symbol (variable)
        elif s[i] == '∃':
            existential_vars.append(s[i+1])  # Add variable after ∃ to be replaced later
            i += 2  # Skip ∃ and its variable, not adding them to result_string
        else:
            result_string += s[i]
            i += 1
    
    # Second pass: Replace existential variables with Skolem functions
    final_result = ""
    for ch in result_string:
        if ch in existential_vars:
            if prefix_vars:
                skolem_function = f'F({",".join(prefix_vars)})'
            else:
                skolem_function = 'F()'
            final_result += skolem_function
        else:
            final_result += ch

    return final_result

#[8] Eliminate universal quantifiers
def Eliminate_universal_quantifiers(s):
    pattern = r'∀[a-zA-Z]'
    new_string = re.sub(pattern, '', s)
    return new_string
        

#[9] Convert to conjunctive normal form
def Convert_to_conjunctive_normal_form(s):
    new_string = Eliminate_implication(s)
    new_string = Demorgan(new_string)
    new_string = Remove_double_not(new_string)
    return new_string

#[10]Turn conjunctions into clauses in a set, and rename variables so that no clause shares the same variable name
def Turn_conjunctions(s):
    return s.split("^")

#[11] Rename variables in clauses so that each clause has a unique variable name
def Rename_variables(lst):
    vars = ["w", "x", "y", "z"]
    i =0
    for clause in range(len(lst)):
        # lst[clause].replace(var in vars, vars[i])
        cls =lst[clause]
        for ch in cls:
            if ch in vars:
                cls = cls.replace(ch,vars[i])
        lst[clause] = cls
        i+=1
    return lst


#[12] Example
logical_clause = "∀x(P(x)→∃xQ(x))"
print(logical_clause)
step1 = Eliminate_implication(logical_clause)
print("After Eliminate_implication : ", step1)

step2 = Demorgan(step1)
print("After Demorgan : ", Demorgan(step1))

step3 = Remove_double_not(step2)
print("After Remove_double_not : ", step3)

step4 = Standardize_variable_scope(logical_clause)
print("After Standardize_variable_scope : ", step4)

step5 = prenex_form(step4)
print("before Skolemization : ", step5)

step6 = Skolemization(step5)
print("After Skolemization : ",step6)

step7 = Eliminate_universal_quantifiers(step6)
print("After Eliminate_universal_quantifiers : ", step7)

step8 = Convert_to_conjunctive_normal_form(step7)
print("After Convert_to_conjunctive_normal_form : ",step8)

step9 = Turn_conjunctions(step8)
print("After Turn_conjunctions : ",step9)

step10 = Rename_variables(step9)
print("After renaming : ",step10)
