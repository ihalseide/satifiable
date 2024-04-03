import re
from typing import Any
import random
import argparse
from sys import stderr, argv, exit
from copy import deepcopy


# Two defined values for literals (the polarity)
POS_LIT = 1 # positive literal, like x1
NEG_LIT = 0 # negative literal, like ~x1

# Clause/function result values
SAT = 'SAT'
UNSAT = 'UNSAT'
UNDECIDED = 'UNDECIDED'


parser = argparse.ArgumentParser(description='Provide path to file with boolean function to check for SAT or UNSAT.\nFile must contain at least one function and no more than two.\nFunctions MUST be in SoP form.\nIf two functions are in file, pass in [-x, --xor] flag to find SAT on two functions.')
mutual1 = parser.add_mutually_exclusive_group(required=False)
mutual2 = parser.add_mutually_exclusive_group(required=False)
group1 = parser.add_argument_group()
group2 = parser.add_argument_group()
group1.add_argument('-f', '--file', required=False, type=str, help='SoP file to parse function in SoP form')
group1.add_argument('-x', '--xor', required=False, help='XOR two SoP functions and return SAT or UNSAT', action='store_true')
mutual1.add_argument('-a', '--all-sop', required=False, help="Find all solutions for function in SoP form", action='store_true')
mutual1.add_argument('-o', '--one-sop', required=False, help="Find one solution for function in SoP form", action='store_true')
group1.add_argument('-p', '--print', required=False, help="Print the DIMACS form of a SoP function from a file. Only use with [-f, --file] option", action='store_true')
group2.add_argument('-d', '--dimacs', required=False, type=str, help="DIMACS file to parse instead of a function in SoP form")
mutual2.add_argument('-m', '--all-dimacs', required=False, help="Find all solutions for function in DIMACS form", action='store_true')
mutual2.add_argument('-s', '--one-dimacs', required=False, help="Find one solution for function in DIMACS form", action='store_true')

class Clause:
    '''
    Clause class, which represents a clause in (CNF) Conjunctive Normal Form.

    When this class is used in the SAT-search algorithms, a CNF clause goes to the inverted/negated boolean function ~F,
    which means that SAT will actually be looking for assignments that set all clauses to have a value of 0, which makes
    the value of ~F UNSAT, which makes F be SAT.
    '''

    def __init__(self, positives:set[int]|list[int], negatives:set[int]|list[int], literals:set[int]|list[int]=set()):
        '''
        Creating a new Clause, arguments:
        - `positives` = set of variables which are positive (like x1, x2, x99)
        - `negatives` = set of variables which are negative (like ~x1, ~x2, ~x99)
        - `literals` = set of literal 1's or 0's values already in the clause

        Examples:
        - Clause([1,2,4], [3,5]) represents the CNF clause: "(x1 + x2 + ~x3 + x4 + ~x5)"
        - Clause([3,2], []) represents the CNF clause: "(x3 + x2)"
        - Clause([], [6]) represents the CNF clause: "(~x6)"
        - Clause([], []) represents an (empty) CNF clause: "()"
        '''
        self.positives: set[int] = set(positives)
        self.negatives: set[int] = set(negatives)
        self.literals: set[int] = set(literals)
        self.isUnit = False

    def __str__(self) -> str:
        '''
        Get a readable string version of this clause.
        This method gets called automatically by str().
        '''
        return f"Clause(positives={self.positives}, negatives={self.negatives}, literals={self.literals})"

    def __repr__(self) -> str:
        '''
        String representation for a clause, just use the same readable version.
        This method is called automatically by repr() and str().
        '''
        return self.__str__()

    def remove(self, xi: int):
        try: self.positives.remove(xi)
        except KeyError: pass

        try: self.negatives.remove(xi)
        except KeyError: pass

    def contains(self, xi: int) -> bool:
        '''
        Returns true if this Clause contains the given variable (index).
        '''
        return (xi in self.positives) or (xi in self.negatives)
    
    def variables(self) -> set[int]:
        '''
        Get the set of all variables in this clause.
        '''
        return set.union(self.positives, self.negatives)
    
    def var_polarities(self) -> dict[int, int|str|None]:
        '''
        Get the list of pairs where each pair is (variable, polarity).
        '''
        return { i: self.var_polarity(i) for i in self.variables() }

    def var_polarity(self, xi:int) -> int|str|None:
        '''
        Get the polarity of a given variable number `xi` within this clause.
        '''
        pos = xi in self.positives
        neg = xi in self.negatives
        if pos and not neg:
            return POS_LIT
        elif neg and not pos:
            return NEG_LIT
        elif neg and pos:
            return 'BOTH'
        else:
            return None

    def negation(self) -> 'Clause':
        '''
        Return the (new instance) negation of this clause.
        '''
        return Clause(self.negatives.copy(), self.positives.copy(), self.literals.copy())
    
    def str_CNF(self, is_CNF=True):
        all = sorted(self.variables())
        string_literals = []
        for lit in self.literals:
            string_literals.append(str(lit))
        for i in all:
            if i in self.positives:
                string_literals.append(f"x{i}")
            if i in self.negatives:
                string_literals.append(f"~x{i}")

        if is_CNF:
            return "(" + (" + ".join(string_literals)) + ")"
        else:
            return " . ".join(string_literals)
        
    def value_cnf(self, assignments: dict[int,int]) -> str:
        '''Return the value this CNF clause has given the assignments.'''
        # SAT if clause is empty
        if not self.positives and not self.negatives and not self.literals:
            return SAT
        # SAT if clause has a literal 1
        if 1 in self.literals:
            return SAT
        # SAT if any positive literal is 1
        for pos_xi in self.positives:
            if assignments.get(pos_xi) == 1:
                return SAT
        # SAT if any negative literal is 0
        for neg_xi in self.negatives:
            if assignments.get(neg_xi) == 0:
                return SAT
        return UNSAT

    def neg_value_cnf(self, assignments: dict[int,int]) -> int|str:
        '''Return the negated/inverted value this CNF clause has given the assignments.'''
        return value_negation(self.value_cnf(assignments))


class ClauseList:
    '''
    Class to track:
    - The list of clauses in a given function.
    - The last variable index from SOP form.
    - The maximum variable index from CNF.
    '''
    def __init__(self, sop_input: str):
        # Store SOP clauses in this member
        self.sop_clauses = parse_SOP_string(sop_input)
        # Store CNF clauses in this member
        self.cnf_clauses = convert_SOP_to_CNF_neg(self.sop_clauses)
        # Store the max variable from the SOP function input in this member
        self.input_max = find_maximum_literal(self.sop_clauses)

        # Keep a count of the index where the max input variable 
        # in SoP form is and store in this member
        self.max_index_sop = 0
        for i in self.sop_clauses:
            # Get the max variable index in the list of keys from the clause
            if max(list(i.variables())) == self.input_max:
                break
            else:
                self.max_index_sop += 1

        # Store the CNF output variable index in this member
        self.max_cnf_index = len(self.cnf_clauses) - 1
        
    def printClauseList(self):
        print(self.sop_clauses)

def value_negation(x):
    '''
    Negate POS_LIT and NEG_LIT, otherwise keep the value.
    '''
    if x == POS_LIT: return NEG_LIT
    elif x == NEG_LIT: return POS_LIT
    else: return x

def parse_SOP_string(text: str) -> list[Clause]: # not CNF clauses!
    '''
    Parses a Sum-of-Products boolean function string.

    The expected string format is:
    - "x"<integer> denotes a variable
    - "~" for logical negation
    - "+" for logical or
    - "." optional for logical and, otherwise logical and is implicit

    Return value: a list of `Clause`s, BUT they are NOT CNF clauses!!!
        They are product terms (DNF clauses).

    NOTE: this function parses pretty greedily and optimistically and may accept and
        parse strings that are not exactly in the right syntax, such as with double
        negatives, multiple dots, extra letters, etc.
    '''
    # Make sure only this subset of characters is in the input string
    if not re.match(r"^([ \r\n.~+x0-9])+$", text, flags=re.IGNORECASE):
        raise ValueError("text string has forbidden characters for SOP form")
    clauses: list[Clause] = [] 
    # split apart all of the product terms which are OR'ed together
    terms = text.split('+')
    # pattern to match one postive or negative literal
    # - group #1 captures the optional inversion prefix '~'
    # - group #2 captures the variable subscript number (the i value in "x_i")
    literal_pat = re.compile(r"^(~?)\s*x(\d+)$", re.IGNORECASE)
    for term in terms:
        # get all of the literals in this term
        literals = term.split(".")
        # group the literals into positive and negative
        positives: set[int] = set()
        negatives: set[int] = set()
        term_lits: set[int] = set()
        for lit in literals:
            lit = lit.strip()
            if lit == "0":
                # Literal zero
                term_lits.add(0)
            elif lit == "1":
                # Literal one
                term_lits.add(1)
                pass
            elif match := literal_pat.match(lit):
                # Literal variable term
                inv = match.group(1)
                num = int(match.group(2))
                if inv:
                    negatives.add(num)
                else:
                    positives.add(num)
            else:
                raise ValueError(f"Invalid single literal in SOP term: \"{lit}\"")
        clauses.append( Clause(positives, negatives, term_lits) )
    return clauses


def convert_SOP_to_CNF_neg(productTerms: list[Clause]) -> list[Clause]:
    '''
    Convert a list of SOP clauses representing a boolean function, F,
    (like from the result of parse_SOP_string) to a list of CNF clauses that represent ~F.
    '''
    # These are the CNF clauses which represent ~F.
    return [ clause.negation() for clause in productTerms ]


def add_GCF_for_and(toList: list[Clause], term: dict[int, int|None], term_out_var_i: int):
    '''
    Helper function for convert_SOP_to_CNF().
    (GCF stands for Gate Consistency Function.)

    Given a product term (from SOP form), and it's output variable,
    add all of it's required CNF clauses to the `toList` as determined by the AND gate consistency function (GCF).

    [Izak is responsible for this function.]
    '''
    # Each term is a product (AND gate)
    # and the consistency function for this creates multiple CNF clauses:
    # For a single gate z = AND(x1, x2, ... xn):
    #     [PRODUCT(over i=1 to n, of (xi + ~z))] * [SUM(over i=1 to n, of ~xi) + z]

    # Add the multiple CNF clauses for the PRODUCT part:
    #    [PRODUCT(over i=1 to n, of xi + ~z)]
    for x_i, val in term.items():
        pos = []
        neg = [term_out_var_i] # add ~z
        if val == POS_LIT:
            # `var_i` is a positive literal in the product term
            pos.append(x_i) # add xi
        elif val == NEG_LIT:
            # `var_i` is a negative literal in the product term
            neg.append(x_i) # add xi
        else:
            raise ValueError(f"term variable #{x_i} has invalid value: {val}")
        toList.append(Clause(pos, neg))

    # Add a single CNF clause for the SUMATION part:
    #    [SUM(over i=1 to n, of ~xi) + z]
    pos = [x_i for x_i, val in term.items() if val == NEG_LIT] # add ~xi (invert the var's polarity)
    neg = [x_i for x_i, val in term.items() if val == POS_LIT] # add ~xi (invert the var's polarity)
    pos.append(term_out_var_i) # add z
    toList.append(Clause(pos, neg))


def add_GCF_for_or(toList: list[Clause], or_input_vars, output_var: int):
    '''
    Helper function for convert_SOP_to_CNF().
    (GCF stands for Gate Consistency Function.)

    Create the consistency function for the OR gate that occurs in SOP form.
    All the input variables are positive, which is why this function is simpler than `add_and_GCF()`.

    [Izak is responsible for this function.]
    '''
    # For and OR gate z = OR(x1, x2, ... xn):
    #    [PRODUCT(over i=1 to n, of (~xi + z))] * [SUM(over i=1 to n, of xi) + ~z]

    # Add the multiple CNF clauses for the PRODUCT part:
    #    PRODUCT(over i=1 to n, of (~xi + z))
    for x_i in or_input_vars:
        toList.append(Clause([output_var], [x_i]))

    # Add a single CNF clause for the SUMATION part:
    #    [SUM(over i=1 to n, of xi) + ~z]
    # In this part, we invert each literals' polarity between positive/negative
    toList.append(Clause(list(or_input_vars), [output_var]))


def clause_value(clause: Clause, assignments: dict) -> str:
    '''
    Function to determine if clause is UNSAT or UNDECIDED.
    A clause is SAT if at least ONE literal evaluates to True
    A clause is UNSAT if all literals evaluate to False
    A clause is UNDECIDED if at least ONE literal is unassigned (This includes Unit Clauses)
    
    - Return `SAT` if clause is SAT
    - Return `UNSAT` if clause is UNSAT
    - Return `UNDECIDED` if clause is UNDECIDED
    '''
    # Get the list of literals from the given clause
    list_of_literals = list(clause.variables())

    # Keep track of number of literals that evaluate to False
    countFalse = 0

    # Loop through the lists and compare the literal in the clause
    # with it's corresponding dictionary value
    # Returns a dictionary of the literal and it's value within the clause
    literals_and_assignments: dict = values_of_literals(clause, assignments)

    # Count number of 0's assigned in the clause
    # A clause is UNSAT if all literals are false.
    for val in literals_and_assignments.values():

        # Count the amount of 0's in a given clause
        if val == NEG_LIT:
            countFalse += 1
        
        # Return 'SAT' if any literal is 1. This means the clause is SAT
        elif val == POS_LIT:
            return SAT
    
    # Specific case for unit clauses:
        # If the amount of 0's in a given clause 
        # is equal to the number of literal in a clause minus 1,
        # then one literal is unassigned, which makes it a unit clause
        # If the clause has one literal that is unassigned, then it is a unit clause
    if countFalse == len(list_of_literals) - 1:
        clause.isUnit = True

    # If the amount of 0's counted in the given clause is equal to the number of
    # literals in the given clause then we know that all literals are 0.
    # This means the clause evaluates to False and is UNSAT.
    if countFalse == len(list_of_literals):
        return UNSAT
    
    # If were here then clause must be UNDECIDED since no other condition is met
    return UNDECIDED


def find_maximum_literal(clauses: list[Clause]) -> int:
    '''
    Find the maximum variable index in a list of CNF clauses.
    This is useful for knowing the upper limit of how many variables there are in a boolean function.
    Also useful for finding the output variable index.
    '''
    return max([max(clause.variables()) for clause in clauses])


def decide_literal(clauses: list[Clause], decisions: dict) -> int|None:
    '''
    Choose an unassigned literal to try next.
    Returns the index of the literal to try next, or None if there are no undecided literals.
    '''
    # NOTE: this doesn't use the clauses at all (yet), but it could be modified to use them.
    undecided = [xi for xi, value in decisions.items() if value is None]
    if not undecided:
        return None
    # For now, just choose a random undecided variable.
    return random.choice(undecided)

def unit_propagate(clauses: list[Clause], assignments: dict[int, int|None]) -> dict[int, int|None]:
    '''
    Function for the unit propagation algorithm
    - Unit propogation works by assigning a unit literal to make the clause SAT
        - We then remove the clause from the search and then remove the unit literal's complement from the clauses.
    - Function takes `list[Clause]` and `assignments dict()`
    - Return the `assignments` of the clause after satisfying the unit clause
    '''
    
    # Loop over entire list of clauses
    i = 0
    polarity = 0
    while i < len(clauses):
        # If there is a unit clause in the list, assign 0 or 1 to the literal depending on the polarity
        if clauses[i].isUnit == True:
            for lit, val in assignments.items():
                if (val == None) and (lit in clauses[i].variables()):
                    if clauses[i].var_polarity(lit) == POS_LIT and assignments[lit] == None: 
                        assignments[lit] = 1 # Only assigning the unassigned literal
                        polarity = POS_LIT # Save the polarity of the literal to determine which complement to remove from the other clauses
                    elif clauses[i].var_polarity(lit) == NEG_LIT and assignments[lit] == None:
                        assignments[lit] = 0 # Only assigning the unassigned literal
                        polarity =  NEG_LIT # Save the polarity of the literal to determine which complement to remove from the other clauses
                    del clauses[i] # Remove the clause from the list now that it is SAT
                    i -= 1
                    # Loop over list again to remove the complement of the literal from all clauses
                    for j in range(len(clauses)):
                        # if the literal that just made the unit clause SAT is in this current clause and is ~xi
                        if  (clauses[j].contains(lit)) and (polarity == NEG_LIT):
                            for k, _ in clauses[j].var_polarities().items():
                                # If literal is the complement of the literal that just made the unit clause SAT...
                                if (k == lit) and (clauses[j].var_polarity(k) == POS_LIT):
                                    clauses[j].remove(k) # Remove the complement literal
                                    break # Removed complement. No need to iterate further in the clause
                        # if the literal that just made the unit clause SAT is in this current clause and is xi
                        elif (clauses[j].contains(lit)) and (polarity == POS_LIT):
                            for k, _ in clauses[j].var_polarities().items():
                                # If literal is the complement of the literal that just made the unit clause SAT...
                                if (k == lit) and (clauses[j].var_polarity(k) == NEG_LIT):
                                    clauses[j].remove(k) # Remove the complement literal
                                    break # Removed complement. No need to iterate further in the clause
                    # Removed clause. No need to further iterate
                    break
        i += 1
    # Return the assignments
    return assignments

def values_of_literals(clause: Clause, assignments: dict) -> dict[int, int|None]:
    '''
    Helper function to assign and get literal values of the current clause

    Return a dictionary of literal and value pairs
    '''
    # Dictionary to hold the mapping of the literal to it's value
    literal_and_assignment = dict()

    # Loop through the literals to assign the values of the literal appropriately
    # Set the current_literal to the current index of the literal
    for current_literal, polarity in clause.var_polarities().items():

        # If the literal is negative AND it's assigned as a 1,
        # Assign the complement 0
        if polarity == NEG_LIT and assignments[current_literal] == POS_LIT:
            literal_and_assignment[current_literal] = NEG_LIT

        # If the literal is negative AND it's assigned as a 0,
        # Assign the complement 1
        elif polarity == NEG_LIT and assignments[current_literal] == NEG_LIT:
            literal_and_assignment[current_literal] = POS_LIT
    
        # If the literal is positive, keep the current assignment
        else:
            literal_and_assignment[current_literal] = assignments[current_literal]

    # Return literal assignments
    return literal_and_assignment


def all_undecided(clauses:list[Clause]) -> dict[int, int|None]:
    '''
    Helper function for dpll() to create initial assignments where each variable is undecided.
    (So each xi is set to None.)
    '''
    assignments: dict[int, int|None] = dict()
    if not clauses:
        # Special case for no clauses
        return assignments
    # Initialize the assignments dictionary to have all variables undecided.
    max_var_i = find_maximum_literal(clauses)
    for i in range(1, max_var_i + 1):
        assignments[i] = None
    return assignments


def dpll_rec(clauses: list[Clause], assignments: dict[int,Any]|None=None) -> dict[int,int|None]:
    '''
    The recursive function implementation for dpll().
    Takes in a list of CNF clauses and a dictionary of decisions.
    Returns: the assignments for literals that make the SAT problem true,
    which is an empty dictionary if the function is UNSAT.

    NOTE: DON'T remove this function because it is useful for validating the iterative version !!!
    '''
    # global for saving the original list of clauses derived
    global original_clauses
    # Make a copy of the clauses to use to evaluate the clauses
    original_clauses = deepcopy(clauses)
    if not assignments:
        assignments = all_undecided(clauses)
    # Base cases:
    # - if all clauses are SAT, then then the function is SAT.
    # - if any clause is UNSAT, then the function is UNSAT.
    # - if there are no clauses, then the function is SAT.
    if not clauses:
        return assignments # SAT
    # Call unit_propagate() to SAT any unit clauses
    anyUndecidedClause: bool = False
    for clause in original_clauses:
        value = clause_value(clause, assignments)
        if value == UNSAT:
            # If any clause is UNSAT, then the whole function is UNSAT.
            return {} # UNSAT
        elif value == UNDECIDED:
            # We only need to see that one clause is undecided to know if any are undecided.
            anyUndecidedClause = True
            if clause.isUnit == True:
                assignments = unit_propagate(clauses, assignments)
    if not anyUndecidedClause:
        # If no clauses are UNSAT and no clauses are undecided,
        # then all clauses are SAT and the whole function is SAT!
        return assignments # SAT

    # At this point, at least one of the clauses is undecided.
    # Choose a literal to try to assign to 1 or to 0...
    # And try those options out by branching recursively.
    xi: int|None = decide_literal(clauses, assignments)
    if not xi:
        # There are no undecided literals, so we can't make any more decisions.
        # This means that the function is UNSAT.
        return {}
    assert(assignments[xi] is None)
    # Try xi=1
    assignments[xi] = 1
    if (result := dpll_rec(clauses, assignments)):
        # SAT
        return result
    # Try xi=0
    assignments[xi] = 0
    if (result := dpll_rec(clauses, assignments)):
        # SAT
        return result
    # If both xi=1 and xi=0 failed, then this whole recursive branch is UNSAT.
    # So return UNSAT to the callee (probably the previous recursive call).
    assignments[xi] = None # undo the decision
    return {} # UNSAT


def dpll_iterative(clauses: list[Clause]) -> dict[int,Any]:
    '''
    Implementation of DPLL using a loop instead of recursion.
    '''
    # global for saving the original list of clauses derived
    global original_clauses
    # Make a copy of the clauses to use to evaluate the clauses
    original_clauses = deepcopy(clauses)
    if not clauses:
        # Edge case where clauses is empty.
        # It's not possible to make any decisions/assignments, so return empty dictionary,
        # which is considered UNSAT.
        return {}
    assignments1 = all_undecided(clauses)
    assignments2 = assignments1.copy()
    starting_xi = decide_literal(clauses, assignments1)
    assert(starting_xi)
    assignments1[starting_xi] = 1
    assignments2[starting_xi] = 0
    stack = []
    stack.append(assignments1)
    stack.append(assignments2)
    while stack:
        current_assignments = stack.pop()
        anyUndecidedClause: bool = False
        anUNSATClause: Clause|None = None
        for clause in original_clauses:
            value = clause_value(clause, current_assignments)
            if value == UNSAT:
                # If any clause is UNSAT, then the whole function is UNSAT.
                anUNSATClause = clause
                break
            elif (not anyUndecidedClause) and (value == UNDECIDED):
                # We only need to see that one clause is undecided to know if any are undecided.
                anyUndecidedClause = True
                current_assignments = unit_propagate(clauses, current_assignments)

        # This should be checked before anyUndecidedClause, because UNSAT takes precedence over UNDECIDED.
        if anUNSATClause is not None:
            # If any clause is UNSAT, then the whole function is UNSAT for this branch.
            # So, continue to next loop iteration to try the next branch(es).
            continue

        if not anyUndecidedClause:
            # If no clauses are UNSAT and no clauses are undecided,
            # then all clauses are SAT and the whole function is SAT!
            return current_assignments # SAT
        else:
            # At this point, at least one of the clauses is undecided,
            # So lets add two decisions to the stack to try next...
            xi = decide_literal(clauses, current_assignments)
            if not xi:
                # There are no undecided literals, so we can't make any more decisions.
                # This means that the function is UNSAT.
                return {} # UNSAT
            assert(current_assignments[xi] is None)
            # Try xi=1
            # (We don't need to make a copy of the current_assignments dictionary,
            #   because it is not used again after this loop iteration.)
            current_assignments[xi] = 1
            stack.append(current_assignments)
            # Try xi=0
            # (Make a copy of the dictionary this time, because we need to make a different decision.)
            assignments2 = current_assignments.copy()
            assignments2[xi] = 0
            stack.append(assignments2)
    # UNSAT due to no more possible assignments on the stack
    return {} # UNSAT


def make_blocking_clause(assignments: dict[int,Any]) -> Clause:
    '''
    Create a clause that blocks the solution given by the assignments.
    Just have to negate the current decided assignments.
    '''
    pos = [xi for xi, v in assignments.items() if v == NEG_LIT] # negated
    neg = [xi for xi, v in assignments.items() if v == POS_LIT] # negated
    return Clause(pos, neg)


def find_all_SAT(clauses: list[Clause]) -> list[dict[int,None]]:
    '''
    Find all satisfying assignments for a boolean function in CNF.
    '''
    solutions: list[dict[int,None]] = []
    # Use the DPLL algorithm to find all solutions
    while (solution := dpll_iterative(clauses)):
        # Add the current solution to the list of solutions
        solutions.append(solution)
        # Add a new clause to the CNF that blocks the current solution
        # (i.e. add a clause that makes the current solution UNSAT).
        # This is called "blocking" the solution.
        clauses.append(make_blocking_clause(solution))
    return solutions


def xor_CNF_functions(clauses_a: ClauseList, clauses_b: ClauseList) -> list[Clause]:
    '''
    Given two boolean functions, combine them with XOR and return a new clause list
    that represents this combination.

    After this function is called, the maximum variable index in the resulting list of clauses
    is guaranteed to be the XOR output.

    Uses gate consistency functions for AND and OR to implement (a^b) as (~a.b + a.~b).
    '''
    clauses_result: list[Clause] = []

    # Get the output literals from the functions, so we can use them as
    # inputs for the GCFs
    a_out = find_maximum_literal(clauses_a.cnf_clauses)
    b_out = find_maximum_literal(clauses_b.cnf_clauses)

    # Get the next variable index that would come after those, so we can
    # introduce new variables to implement GCFs.
    next_literal_i = 1 + max((a_out, b_out,))

    # These are the new variables for the gate outputs
    not_a_yes_b_out = next_literal_i + 1 # for the first AND gate output
    yes_a_not_b_out = next_literal_i + 2 # for the second AND gate output
    or_out = next_literal_i + 3 # for the final OR gate output

    # Implement AND gate for: ~a.b -> not_a_yes_b_out
    not_a_yes_b_clause = Clause([b_out], [a_out])
    add_GCF_for_and(clauses_result, not_a_yes_b_clause.data, not_a_yes_b_out)

    # Implement AND gate for: a.~b -> yes_a_not_b_out
    yes_a_not_b_clause = Clause([a_out], [b_out])
    add_GCF_for_and(clauses_result, yes_a_not_b_clause.data, yes_a_not_b_out)

    # Implement OR gate for combining the above two AND gates
    or_input_vars = [not_a_yes_b_out, yes_a_not_b_out]
    add_GCF_for_or(clauses_result, or_input_vars, or_out)

    return clauses_result


def boolean_functions_are_equivalent(clauses1: ClauseList, clauses2: ClauseList, find_all: bool) -> (list[dict[int, None]] | dict[int, Any]):
    '''
    Function to determine if two sets of CNF clauses represent the same boolean function by using SAT solving.
    Does this by XOR'ing the two sets of clauses and checking if the result is UNSAT.
    '''
    # XOR the two sets of clauses together,
    # Using gate consistency functions for AND and OR to implement (a^b) as (~a.b + a.~b).
    clauses: list[Clause] = xor_CNF_functions(clauses1, clauses2)

    # Print the list of clauses from XOR operation
    print(f"CNF clause from XOR functions: {clauses}")
    result = None
    # Find all or one solution(s) for SAT
    if find_all:
        result = find_all_SAT(clauses)
    else:
        result = dpll_iterative(clauses)
    return result


def printAssignments(assignments: dict[int,Any]):
    print(", ".join([f"x{i}={v}" for i, v in assignments.items()]))


def test_str_CNF():
    print("Testing Clause.str_CNF()")

    c = Clause([],[])
    assert(c.str_CNF() == '()')
    assert(c.str_CNF(False) == '')

    c = Clause([], [], {0})
    assert(c.str_CNF() == '(0)')
    assert(c.str_CNF(False) == '0')

    c = Clause([], [], {1})
    assert(c.str_CNF() == '(1)')
    assert(c.str_CNF(False) == '1')

    c = Clause([], [], {0, 1})
    assert(c.str_CNF() == '(0 + 1)')
    assert(c.str_CNF(False) == '0 . 1')

    c = Clause({1}, [])
    assert(c.str_CNF() == '(x1)')
    assert(c.str_CNF(False) == 'x1')

    c = Clause([], {1})
    assert(c.str_CNF() == '(~x1)')
    assert(c.str_CNF(False) == '~x1')

    c = Clause({1}, {1})
    assert(c.str_CNF() == '(x1 + ~x1)')
    assert(c.str_CNF(False) == 'x1 . ~x1')

    c = Clause({1, 2}, {2, 3})
    assert(c.str_CNF() == '(x1 + x2 + ~x2 + ~x3)')
    assert(c.str_CNF(False) == 'x1 . x2 . ~x2 . ~x3')

    c = Clause({1, 2}, {2, 3}, {1})
    assert(c.str_CNF() == '(1 + x1 + x2 + ~x2 + ~x3)')
    assert(c.str_CNF(False) == '1 . x1 . x2 . ~x2 . ~x3')

    c = Clause({1, 2}, {2, 3}, {0})
    assert(c.str_CNF() == '(0 + x1 + x2 + ~x2 + ~x3)')
    assert(c.str_CNF(False) == '0 . x1 . x2 . ~x2 . ~x3')

    c = Clause({1, 2}, {2, 3}, {1, 0})
    assert(c.str_CNF() == '(0 + 1 + x1 + x2 + ~x2 + ~x3)')
    assert(c.str_CNF(False) == '0 . 1 . x1 . x2 . ~x2 . ~x3')

def test_clause_value():
    '''
    Test the clause_value() function
    '''
    # test one positive literal (x1)
    c = Clause([1], [])

    # postive literal is set to 1
    v = clause_value(c, {1:1})
    assert(v == SAT)

    # Setting clause with only one literal to 0
    v = clause_value(c, {1:0})
    assert(v == UNSAT)

    # The only literal is undecided
    v = clause_value(c, {1:None})
    assert(v == UNDECIDED)

    # Test one negative literal (~x1)
    c = Clause([], [1])

    # assign the literal to 1, which makes the clause false
    v = clause_value(c, {1:1})
    assert(v == UNSAT)

    # assign the literal to 0, which makes the clause true
    v = clause_value(c, {1:0})
    assert(v == SAT)

    # The only literal is undecided
    v = clause_value(c, {1:None})
    assert(v == UNDECIDED)

    # Test a clause with 2 literals
    c = Clause([1,2], [])
    testPairs2 = [
        ({1:1, 2:1}, SAT),
        ({1:1, 2:0}, SAT),
        ({1:0, 2:1}, SAT),
        ({1:0, 2:0}, UNSAT),
        ({1:None, 2:None}, UNDECIDED),
        ({1:0, 2:None}, UNDECIDED),
        ({1:None, 2:0}, UNDECIDED),
        ({1:1, 2:None}, SAT),
        ({1:None, 2:1}, SAT),
    ]
    for assignment, expected in testPairs2:
        actual = clause_value(c, assignment)
        try:
            assert(actual == expected)
        except AssertionError:
            print(f"Failed test with assignments {assignment} and expected {expected} but got {actual}")
            exit(1)

    # Test a clause with 3 positive literals
    # (not testing all combinations of 0,1, and None)
    c = Clause([1,2,3], [])
    testPairs3 = [
        ({1:1, 2:1, 3:1}, SAT),
        ({1:1, 2:1, 3:0}, SAT),
        ({1:1, 2:0, 3:1}, SAT),
        ({1:1, 2:0, 3:0}, SAT),
        ({1:0, 2:1, 3:1}, SAT),
        ({1:0, 2:1, 3:0}, SAT),
        ({1:0, 2:0, 3:1}, SAT),
        ({1:0, 2:0, 3:0}, UNSAT),
        ({1:0, 2:1, 3:None}, SAT),
        ({1:None, 2:None, 3:1}, SAT),
        ({1:None, 2:0, 3:None}, UNDECIDED),
    ]
    for assignment, expected in testPairs3:
        v = clause_value(c, assignment)
        try:
            assert(v == expected)
        except AssertionError:
            print(f"Failed test with assignments {assignment} and expected {expected} but got {v}")
            exit(1)


def test_dpll(dpll_func):
    print(f"Testing {dpll_func.__name__}()")

    # test no clauses (just make sure it doesn't crash)
    assert(dpll_func([]) == {})

    # Test a single clause with one positive literal (SAT)
    clauses = [ Clause([1], []) ] # (x1)
    result = dpll_func(clauses)
    assert(result)
    assert(result[1] == 1)
    assert(result == {1:1})

    # Test a single clause with one negative literal (SAT)
    clauses = [ Clause([], [1]) ] # (~x1)
    result = dpll_func(clauses)
    assert(result)
    assert(result[1] == 0)
    assert(result == {1:0})

    # Test conflicting clauses (UNSAT)
    clauses = [ Clause([1], []), Clause([], [1]) ] # (x1).(~x1)
    result = dpll_func(clauses)
    assert(result == {})

    # Test 2 clauses
    clauses = [ Clause([1], []), Clause([2], []) ] # (x1).(x2)
    result = dpll_func(clauses)
    assert(result)
    assert(result == {1: 1, 2: 1})

    # Test 2 clauses (one has a positive literal, one is negative literal)
    clauses = [ Clause([1], []), Clause([], [2]) ] # (x1).(~x2)
    result = dpll_func(clauses)
    assert(result)
    assert(result == {1: 1, 2: 0})

    # Test 2 clauses (both negative literals)
    clauses = [ Clause([], [1]), Clause([], [2]) ] # (~x1).(~x2)
    result = dpll_func(clauses)
    assert(result)
    assert(result == {1: 0, 2: 0})


def test_parse_SOP_string():
    print('Testing parse_SOP_string()')
    
    a = parse_SOP_string("1")
    assert(len(a) == 1)
    c = a[0]
    assert(1 in c.literals)
    assert(0 not in c.literals)
    assert(not c.positives)
    assert(not c.negatives)

    a = parse_SOP_string("0")
    assert(len(a) == 1)
    c = a[0]
    assert(1 not in c.literals)
    assert(0 in c.literals)
    assert(not c.positives)
    assert(not c.negatives)

    a = parse_SOP_string("1 . 1")
    assert(len(a) == 1)
    c = a[0]
    assert(1 in c.literals)
    assert(0 not in c.literals)
    assert(not c.positives)
    assert(not c.negatives)

    a = parse_SOP_string("1 . 0")
    assert(len(a) == 1)
    c = a[0]
    assert(1 in c.literals)
    assert(0 in c.literals)
    assert(not c.positives)
    assert(not c.negatives)

    a = parse_SOP_string("1 + 0")
    assert(len(a) == 2)
    c = a[0]
    assert(1 in c.literals)
    assert(0 not in c.literals)
    assert(not c.positives)
    assert(not c.negatives)
    c = a[1]
    assert(1 not in c.literals)
    assert(0 in c.literals)
    assert(not c.positives)
    assert(not c.negatives)

    a = parse_SOP_string("x1")
    assert(len(a) == 1)
    c = a[0]
    assert(1 in c.positives)
    assert(not c.literals)
    assert(not c.negatives)

    a = parse_SOP_string("x1 + x2 + x3")
    assert(len(a) == 3)
    assert(1 in a[0].positives)
    assert(2 in a[1].positives)
    assert(3 in a[2].positives)
    assert(1 not in a[0].negatives)
    assert(2 not in a[1].negatives)
    assert(3 not in a[2].negatives)

    a = parse_SOP_string("x1 . ~x2")
    assert(len(a) == 1)
    assert(1 in a[0].positives)
    assert(2 not in a[0].positives)
    assert(1 not in a[0].negatives)
    assert(2 in a[0].negatives)

    a = parse_SOP_string("~x1 . x2")
    assert(len(a) == 1)
    assert(1 not in a[0].positives)
    assert(2 in a[0].positives)
    assert(1 in a[0].negatives)
    assert(2 not in a[0].negatives)

    a = parse_SOP_string("~x1 . ~x2")
    assert(len(a) == 1)
    assert(1 not in a[0].positives)
    assert(2 not in a[0].positives)
    assert(1 in a[0].negatives)
    assert(2 in a[0].negatives)

    a = parse_SOP_string("~x1 . x1 . x1")
    assert(len(a) == 1)
    assert(1 in a[0].negatives)
    assert(1 in a[0].positives)


def test_convert_SOP_to_CNF_neg():
    print('Testing convert_SOP_to_CNF_neg()')
    
    # try single-variable SOP clauses of "x1" up to "x100"
    for xi in range(1, 100):
        # positive clauses
        sop = [ Clause([xi], []) ] # "xi"
        cnf = convert_SOP_to_CNF_neg(sop)
        assert(cnf[0].variables() == {xi})
        assert(cnf[0].var_polarity(xi) == NEG_LIT)

        # negative clauses
        sop = [ Clause([], [xi]) ] # "xi"
        cnf = convert_SOP_to_CNF_neg(sop)
        assert(cnf[0].variables() == {xi})
        assert(cnf[0].var_polarity(xi) == POS_LIT)

    # try a single SOP clause with 2 variables
    sop = [ Clause([1, 2], []) ] # "x1 . x2"
    cnf = convert_SOP_to_CNF_neg(sop) # should be "(x1)(x2)"
    assert(len(cnf) == 1)
    assert(cnf[0].variables() == {1, 2})
    assert(cnf[0].var_polarity(1) == NEG_LIT)
    assert(cnf[0].var_polarity(2) == NEG_LIT)

    # try a single SOP clause with 2 variables
    sop = [ Clause([1], [2]) ] # "x1 . ~x2"
    cnf = convert_SOP_to_CNF_neg(sop) # should be "(x1)(~x2)"
    assert(len(cnf) == 1)
    assert(cnf[0].variables() == {1, 2})
    assert(cnf[0].var_polarity(1) == NEG_LIT)
    assert(cnf[0].var_polarity(2) == POS_LIT)

    # try a single SOP clause with conflicting variables
    sop = [ Clause([99], [99]) ] # "xi . ~xi"
    cnf = convert_SOP_to_CNF_neg(sop) # should be "(xi . ~x1)""
    assert(cnf[0].variables() == {99})
    assert(cnf[0].var_polarity(99) == 'BOTH')

    # convert 2 clauses each with 2 vars
    sop = [ Clause({1}, {2}), Clause({2}, {1})] # "x1 . ~x2 + ~x1 . x2"
    cnf = convert_SOP_to_CNF_neg(sop) # should be "(~x1 + x2).(x1 + ~x2)"
    assert(cnf[0].var_polarities() == {1: NEG_LIT, 2: POS_LIT})
    assert(cnf[1].var_polarities() == {1: POS_LIT, 2: NEG_LIT})


def test_SAT_cnf():
    '''Test all functions in this file (SAT_cnf.py).'''
    print("Testing SAT_cnf.py")
    test_str_CNF()
    test_parse_SOP_string()
    test_convert_SOP_to_CNF_neg()
    test_clause_value()
    test_dpll(dpll_rec)
    test_dpll(dpll_iterative)
    print('All tests passed!')


def print_clauses_as_DIMACS(clauses: list[Clause]):
    '''
    Print the given clauses in DIMACS format.
    '''
    # Get the maximum variable index
    max_var_i = find_maximum_literal(clauses)
    # Print the header
    print(f"p cnf {max_var_i} {len(clauses)}")
    # Print each clause
    for clause in clauses:
        # Get the list of literals in the clause
        literals = sorted(clause.var_polarities().items())
        # Print the literals in the clause
        for var_i, value in literals:
            if value == POS_LIT:
                print(var_i, end=" ")
            elif value == NEG_LIT:
                print(f"-{var_i}", end=" ")
            else:
                raise ValueError(f"invalid value {value} for variable {var_i}")
        print("0")


def parse_DIMACS_clause(line: str) -> Clause:
    '''
    Helper function for read_DIMACS_file().
    '''
    assert(line)
    indices = line.split()
    neg = set()
    pos = set()
    for index in indices:
        xi = int(index)
        if xi == 0:
            break
        elif xi < 0:
            neg.add(-xi)
        elif xi > 0:
            pos.add(xi)
    return Clause(pos, neg)
    

def read_DIMACS_file(file_path: str) -> list[Clause]:
    '''
    Read a file in DIMACS format and return all of the clauses (CNF).
    '''
    clauses = []
    num_vars = 0
    num_clauses = 0
    with open(file_path, "r") as file:
        # Read the file into a list of lines
        for line in file:
            if not line:
                # Skip blank lines
                continue
            elif line.startswith("c"):
                # Skip any comments
                continue
            elif line.startswith("p"):
                # p cnf <vars> <clauses>
                _, _, num_vars_s, num_clauses_s = line.split()
                num_vars = int(num_vars_s)
                num_clauses = int(num_clauses_s)
            else:
                # Parse the clause
                clause = parse_DIMACS_clause(line)
                clauses.append(clause)
    assert(num_vars > 0)
    assert(num_clauses == len(clauses))
    # Print the clauses.
    print('Converting to CNF, clauses are:')
    print(".".join([str(clauses[i]) for i in range(len(clauses))]))
    return clauses


def read_sop_file(file_path: str) -> list[Clause]:
    '''
    Function to read the plain text SoP function.
    Will read the first function on line 1.
    - `~` represents NOT
    - `.` represents AND
    - `+` represents OR
    - `xi` represents literal where `i` is the 'subscript'

    Returns a list of Clause objects for the given function
    '''
    with open(file_path, "r") as file:
        # Read first line of the file. This should be the function in SoP form
        function = file.readline()
        print('Parsing SOP input:', function)
        # Parse the string input
        sop = parse_SOP_string(function)
        print('Parsed result:', '+'.join([x.str_CNF(is_CNF=False) for x in sop]))
        # Convert the string to CNF form
        cnf = convert_SOP_to_CNF_neg(sop)
        # Print the CNF clause list
        print('Converting to CNF, clauses are:')
        print(".".join([str(c) for c in cnf])) # print clause list
    return cnf


def read_sop_xor(file_path: str) -> tuple[ClauseList, ClauseList]:
    '''
    Function to read the plain text SoP functions. Should only be used for XOR operation
    Requires two functions in the plain text file. They will be XOR'd together
    Will read the first function on line 1.
    - `~` represents NOT
    - `.` represents AND
    - `+` represents OR
    - `xi` represents literal where `i` is the 'subscript'

    Returns a tuple ClauseList objects for the given function
    '''
    with open(file_path, "r") as file:
        # Read first line of the file. This should be the function in SoP form
        function1 = file.readline()
        # Read second line of the file. This should be the function in SoP form
        function2 = file.readlines()[0]
        print('Parsing SOP input:', function1)
        # Parse the string input
        sop1 = parse_SOP_string(function1)
        print('Parsed result:', '+'.join([x.str_CNF(is_CNF=False) for x in sop1]))
        print('Parsing SOP input:', function2)
        # Parse the string input
        sop2 = parse_SOP_string(function2)
        print('Parsed result:', '+'.join([x.str_CNF(is_CNF=False) for x in sop2]))
        # Create a ClauseList object to convert the SoP function to CNF.
        # Object members contain CNF form function and other attributes
        cnf1 = ClauseList(function1)
        cnf2 = ClauseList(function2)
        # Print the CNF clause list
        print('Converting to CNF for function 1, clauses are:')
        print(".".join([str(c) for c in cnf1.cnf_clauses]))
        print('Converting to CNF for function 2, clauses are:')
        print(".".join([str(c) for c in cnf2.cnf_clauses]))
    return cnf1, cnf2


def print_result(result: list[dict[int,None]], all_sat: bool):
    '''
    Function to print the result SAT or UNSAT.
    '''
    # If bool for finding all SAT solutions is false, then only print one solution
    if not all_sat:
        if result:
            print("Function is SAT with this assignment:")
            printAssignments(result)
        else:
            print("Function is UNSAT")
    # Print all given solutions
    else:
        if result:
            print("Function is SAT with these assignments:")
            for i, r in enumerate(result):
                print(end=f'- solution #{i+1}: ')
                printAssignments(r)
        else:
            print("Function is UNSAT")


def main():
    args = parser.parse_args()

    if len(argv) == 1:
        parser.print_help(stderr)
        exit(1)
        
    if not args.file and not args.dimacs:
        # Run tests if no files were provided
        print('No file provided, Running tests...')
        test_SAT_cnf()
        return

        # If DIMACS formatted file was provided...
    if args.dimacs:
        # Find one solution for the given clauses
        if args.one_dimacs:# Find one SAT solution from DIMACS format
            # Parse DIMACS and call DPLL algorithm to find SAT or UNSAT
            print('Parsing DIMACS file at:', args.dimacs)
            clauses = read_DIMACS_file(args.dimacs)
            result = dpll_iterative(clauses)
        # Find all solutions for the given clauses
        elif args.all_dimacs:
            # Parse DIMACS and call DPLL algorithm to find SAT or UNSAT
            print('Parsing DIMACS file at:', args.dimacs)
            clauses = read_DIMACS_file(args.dimacs)
            result = find_all_SAT(clauses)
        else:
            parser.print_help(stderr)
            exit(1)
        # Print all or one solution(s) from the result
        print_result(result, args.all_dimacs)
        return
    
    # If SoP formatted file was provided...
    if args.file and not args.xor and not args.print:
        # Find one SAT solution from given file for one function
        if args.one_sop:
            # Parse SoP and call DPLL algorithm to find SAT or UNSAT
            cnf = read_sop_file(args.file)
            result = dpll_iterative(cnf)
        # Find all SAT solutions from given file for one function
        elif args.all_sop:
            # Parse SoP and call DPLL algorithm to find SAT or UNSAT
            cnf = read_sop_file(args.file)
            result = find_all_SAT(cnf)
        else:
            parser.print_help(stderr)
            exit(1)
    # Print all or one solution(s) from the result
        print_result(result, args.all_sop)
        return

    # Find if two solutions are SAT by XOR
    if args.file and args.xor and not args.print:
        # Read both lines of file and return the CNF Clauses
        cnf1, cnf2 = read_sop_xor(args.file)
        # args.all_sop holds boolean if we want all or one result. 
        # Depending on that, we call either find_and_print_all_SAT() or dpll_iterative()
        result = boolean_functions_are_equivalent(cnf1, cnf2, args.all_sop)
        # Print all or one solution(s) from the result
        print_result(result, args.all_sop)
        return

    # Print the DIMACS format of a given SoP function
    if args.file and args.print:
        cnf = read_sop_file(args.file)
        print('--- BEGIN DIMACS FORMAT')
        print_clauses_as_DIMACS(cnf)
        print('--- END DIMACS FORMAT')
        return

if __name__ == "__main__":
    test_SAT_cnf()
    #main()