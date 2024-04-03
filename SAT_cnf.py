import re
from typing import Any
import random
import argparse
from sys import stderr, argv, exit


'''
Terminology notes:
- SOP stands for "Sum of Products", is equivalent to DNF
- POS stands for "Product of Sums", is equivalent to CNF
- DNF stands for "Disjunctive Normal Form", is equivalent to SOP
- CNF stands for "Conjunctive Normal Form", is equivalent to POS
'''


# Two defined values for literals (the polarity)
POS_LIT = 1 # positive literal, like x1
NEG_LIT = 0 # negative literal, like ~x1

# Clause/function result values
SAT = 'SAT'
UNSAT = 'UNSAT'
UNDECIDED = 'UNDECIDED'


class Clause:
    '''
    Clause class, which represents a clause in (CNF) Conjunctive Normal Form
    (although it is sometimes used as a convenient container for SOP terms).

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
        - `Clause([1,2,4], [3,5])` represents the CNF clause: "(x1 + x2 + ~x3 + x4 + ~x5)"
        - `Clause([3,2], [])` represents the CNF clause: "(x3 + x2)"
        - `Clause([], [6])` represents the CNF clause: "(~x6)"
        - `Clause([], [])` represents an (empty) CNF clause: "()"
        '''
        self.positives: set[int] = set(positives)
        self.negatives: set[int] = set(negatives)
        self.literals: set[int] = set(literals)
        #self.isUnit = False


    def __eq__(self, other: object) -> bool:
        if not isinstance(other, Clause):
            return NotImplemented
        return (self.positives == other.positives) and (self.negatives == other.negatives) and (self.literals == other.literals)


    def __str__(self) -> str:
        return f"Clause(positives={self.positives}, negatives={self.negatives}, literals={self.literals})"


    def __repr__(self) -> str:
        return self.__str__()


    def remove_var(self, xi: int):
        '''Remove a variable from the clause.'''
        try: self.positives.remove(xi)
        except KeyError: pass

        try: self.negatives.remove(xi)
        except KeyError: pass


    def contains(self, xi: int) -> bool:
        '''
        Returns True only if this Clause contains the given variable (index).
        '''
        return (xi in self.positives) or (xi in self.negatives)
    

    def vars(self) -> set[int]:
        '''
        Get the set of all variables in this clause.
        '''
        return set.union(self.positives, self.negatives)
    

    def var_polarities(self) -> dict[int, int|str|None]:
        '''
        Get the list of pairs where each pair is (variable, polarity).
        '''
        return { i: self.var_polarity(i) for i in self.vars() }


    def var_polarity(self, xi:int) -> int|str|None:
        '''
        Get the polarity of a given variable number `xi` within this clause.
        '''
        pos = xi in self.positives
        neg = xi in self.negatives
        if neg and pos:
            return 'BOTH'
        elif neg and not pos:
            return NEG_LIT
        elif pos and not neg:
            return POS_LIT
        else:
            return None


    def negation(self) -> 'Clause':
        '''
        Return the (new instance) negation of this clause.
        '''
        return Clause(self.negatives.copy(), self.positives.copy(), self.literals.copy())
    

    def str_SOP(self) -> str:
        all = sorted(self.vars())
        string_literals = []
        for lit in self.literals:
            string_literals.append(str(lit))
        for i in all:
            if i in self.positives:
                string_literals.append(f"x{i}")
            if i in self.negatives:
                string_literals.append(f"~x{i}")
        return " . ".join(string_literals)


    def str_CNF(self) -> str:
        all = sorted(self.vars())
        string_literals = []
        for lit in self.literals:
            string_literals.append(str(lit))
        for i in all:
            if i in self.positives:
                string_literals.append(f"x{i}")
            if i in self.negatives:
                string_literals.append(f"~x{i}")
        return " + ".join(string_literals)
            
        
    def undecided_vars(self, assignments: dict[int, int]) -> set[int]:
        '''
        Return the set of undecided variables within this clause given the specific assignments so far.
        '''
        assigned = set(assignments.keys())
        return self.vars().difference(assigned)
        

    def value_cnf(self, assignments: dict[int,int]) -> str:
        '''
        Return the value this as a CNF clause if it has given the assignments.
        - A clause is SAT if at least ONE literal evaluates to True
        - A clause is UNSAT if all literals evaluate to False
        - A clause is UNDECIDED if at least ONE literal is unassigned (This includes "unit" Clauses)
        '''
        # SAT if clause is empty
        if not self.positives and not self.negatives and not self.literals:
            return SAT
        # SAT if clause has a literal 1
        if 1 in self.literals:
            return SAT
        has_unassigned_var = False
        # SAT if any positive literal is 1.
        # If the end of this for loop is reached, then all positive literals are either 0 or undecided.
        for pos_xi in self.positives:
            val = assignments.get(pos_xi)
            if val == 1:
                return SAT
            elif val is None:
                has_unassigned_var = True
        # SAT if any negative literal is 0.
        # If the end of this for loop is reached, then all negative literals are either 1 or undecided.
        for neg_xi in self.negatives:
            val = assignments.get(neg_xi)
            if val == 0:
                return SAT
            elif val is None:
                has_unassigned_var = True
        # UNDECIDED if no positive literals are 1 and no negative literals are 0 and there is at least one unassigned variable.
        # UNSAT if no positive literals are 1 and no negative literals are 0 and there are no unassigned variables.
        if has_unassigned_var:
            return UNDECIDED
        else:
            return UNSAT


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
        self.cnf_clauses = convert_SOP_to_CNF(self.sop_clauses)
        # Store the max variable from the SOP function input in this member
        self.input_max = find_max_var(self.sop_clauses)

        # Keep a count of the index where the max input variable 
        # in SoP form is and store in this member
        self.max_index_sop = 0
        for i in self.sop_clauses:
            # Get the max variable index in the list of keys from the clause
            if max(list(i.vars())) == self.input_max:
                break
            else:
                self.max_index_sop += 1

        # Store the CNF output variable index in this member
        self.max_cnf_index = len(self.cnf_clauses) - 1
        
    def printClauseList(self):
        print(self.sop_clauses)


def literal_val_negation(x):
    '''
    Negate POS_LIT and NEG_LIT, otherwise keep the value.
    '''
    if x == POS_LIT: return NEG_LIT
    elif x == NEG_LIT: return POS_LIT
    else: return x


def sat_val_negation(x:str) -> str:
    '''Invert/negate SAT vs UNSAT'''
    if x == SAT: return UNSAT
    elif x == UNSAT: return SAT
    elif x == UNDECIDED: return UNDECIDED
    raise ValueError(f"x must be SAT or UNSAT but is \"{x}\"")


def clauses_all_vars(clauses:list[Clause]) -> set[int]:
    '''Get the set of all variables in a given list of Clauses'''
    result = set()
    for clause in clauses:
        result.update(clause.vars())
    return result


def parse_SOP_string(text: str) -> list[Clause]: # list of product terms, not CNF clauses!
    '''
    Parses a Sum-of-Products boolean function string.

    The expected string format is:
    - "x"<integer> denotes a variable
    - "~" for logical negation
    - "+" for logical or
    - "." optional for logical and, otherwise logical and is implicit

    Return value: a list of `Clause`s, BUT they are NOT CNF clauses!!!
        They are product terms (SOP/DNF clauses).

    NOTE: this function parses pretty greedily and optimistically and may accept and
        parse strings that are not exactly in the right syntax, such as with double
        negatives, multiple dots, extra letters, etc.
    '''
    if not text:
        raise ValueError("empty SOP string")
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
                raise ValueError(f"Invalid single literal in SOP term (dots are required): \"{lit}\"")
        clauses.append( Clause(positives, negatives, term_lits) )
    return clauses


def convert_SOP_to_CNF(product_terms: list[Clause]) -> list[Clause]:
    '''
    Convert a list of SOP clauses representing a boolean function, F,
    (like from the result of parse_SOP_string) to a list of CNF clauses that represent F.
    '''
    result: list[Clause] = []
    if len(product_terms) == 1:
        # Only one term, so expand it out into 1-variable CNF clauses
        term = product_terms[0]
        for x_i, polarity in term.var_polarities().items():
            if polarity == POS_LIT:
                result.append(Clause({x_i}, []))
            elif polarity == NEG_LIT:
                result.append(Clause([], {x_i}))
            else:
                raise ValueError(f"'and' input variable #{x_i} has invalid polarity: {polarity}")
        return result
    else:
        # See if all terms only have 1 variable.
        is_all_1_var_terms = True
        for term in product_terms:
            if len(term.vars()) != 1:
                is_all_1_var_terms = False
                break

        if is_all_1_var_terms:
            # Multiple terms, where each only has one variable.
            # Can create just a single CNF clause.
            one_clause = Clause([], [])
            for term in product_terms:
                one_clause.positives.update(term.positives)
                one_clause.negatives.update(term.negatives)
            result.append(one_clause)
            return result
        else:
            # Multiple terms with multiple variables
            xi = find_max_var(product_terms) + 1
            or_first_in_i = xi
            # Keep track of the inputs to the OR gate, and their polarities.
            or_inputs: dict[int, int] = {}
            # Create AND gates for each product term
            for term in product_terms:
                num_vars = len(term.vars())
                if num_vars > 1:
                    # Create AND gate for this product term
                    add_GCF_for_and(result, term.var_polarities(), xi)
                    or_inputs[xi] = POS_LIT
                    xi += 1
                elif num_vars == 1:
                    # (Shortcut) Wire directly to the big OR GCF later
                    var, polarity = tuple(term.var_polarities().items())[0]
                    assert(polarity == POS_LIT or polarity == NEG_LIT)
                    or_inputs[var] = int(polarity)
            # Combine into one big OR gate
            add_GCF_for_or(result, or_inputs, xi)
            # Now that we have the gate consistency, make sure the output should be 1
            result.append(Clause({xi}, []))
            return result


def add_GCF_for_and(to_list: list[Clause], input_vars: dict[int, int], term_output_var: int):
    '''
    Helper function for convert_SOP_to_CNF().
    (GCF stands for Gate Consistency Function.)

    Given a product term (from SOP form), and it's output variable,
    add all of it's required CNF clauses to the `toList` as determined by the AND gate consistency function (GCF).
    '''
    # Each term is a product (AND gate)
    # and the consistency function for this creates multiple CNF clauses:
    # For a single gate z = AND(x1, x2, ... xn):
    #     [PRODUCT(over i=1 to n, of (xi + ~z))] * [SUM(over i=1 to n, of ~xi) + z]

    # Add the multiple CNF clauses for the PRODUCT part:
    #    [PRODUCT(over i=1 to n, of xi + ~z)]
    for x_i, polarity in input_vars.items():
        # Keep polarity of x_i and always add ~z
        if polarity == POS_LIT:
            # `x_i` is a positive literal in the product term
            to_list.append(Clause([x_i], [term_output_var])) # add xi and ~z
        elif polarity == NEG_LIT:
            # `x_i` is a negative literal in the product term
            to_list.append(Clause([], [x_i, term_output_var])) # add ~xi and ~z
        else:
            raise ValueError(f"'and' input variable #{x_i} has invalid polarity: {polarity}")

    # Add a single CNF clause for the SUMATION part (invert original vars and introduce the output variable `z`):
    #    [SUM(over i=1 to n, of ~xi) + z]
    summation_clause = Clause({term_output_var}, []) # add z
    for x_i, polarity in input_vars.items():
        # Invert polarity of x_i
        if polarity == POS_LIT:
            summation_clause.negatives.add(x_i)
        elif polarity == NEG_LIT:
            summation_clause.positives.add(x_i)
        else:
            raise ValueError(f"'and' input variable #{x_i} has invalid polarity: {polarity}")
    to_list.append(summation_clause)


def add_GCF_for_or(to_list: list[Clause], input_vars: dict[int, int], output_var: int):
    '''
    Helper function for convert_SOP_to_CNF().
    (GCF stands for Gate Consistency Function.)

    Create the consistency function for the OR gate that occurs in SOP form.
    '''
    # For and OR gate z = OR(x1, x2, ... xn):
    #    [PRODUCT(over i=1 to n, of (~xi + z))] * [SUM(over i=1 to n, of xi) + ~z]

    # Add the multiple CNF clauses for the PRODUCT part:
    #    PRODUCT(over i=1 to n, of (~xi + z))
    for x_i, polarity in input_vars.items():
        if polarity == POS_LIT:
            # invert positive `x_i` to negative
            to_list.append(Clause({output_var}, {x_i})) # add ~xi and z
        elif polarity == NEG_LIT:
            # invert negative `x_i` to positive
            to_list.append(Clause({x_i, output_var}, [])) # add ~xi and z
        else:
            raise ValueError(f"'or' input variable #{x_i} has invalid polarity: {polarity}")

    # Add a single CNF clause for the SUMATION part:
    #    [SUM(over i=1 to n, of xi) + ~z]
    summation_clause = Clause([], {output_var}) # add ~z
    for x_i, polarity in input_vars.items():
        # Keep polarity of x_i
        if polarity == POS_LIT:
            summation_clause.positives.add(x_i)
        elif polarity == NEG_LIT:
            summation_clause.negatives.add(x_i)
        else:
            raise ValueError(f"'or' input variable #{x_i} has invalid polarity: {polarity}")
    to_list.append(summation_clause)


def find_max_var(clauses: list[Clause]) -> int:
    '''
    Find the maximum variable index in a list of CNF clauses.
    This is useful for knowing the upper limit of how many variables there are in a boolean function.
    Also useful for finding the output variable index.
    '''
    return max([max(clause.vars()) for clause in clauses])


def decide_literal(literal_set:set[int], decisions: dict) -> int|None:
    '''
    Choose an unassigned literal to try next.
    The `literal_set` is the set of literals allowed to be chosen from.
    Returns the index of the literal to try next, or `None` if there are no undecided literals.
    '''
    assigned = set(decisions.keys())
    unassigned = literal_set.difference(assigned)
    if unassigned:
        return random.choice(tuple(unassigned))
    else:
        return None


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
                if (val == None) and (lit in clauses[i].vars()):
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
                                    clauses[j].remove_var(k) # Remove the complement literal
                                    break # Removed complement. No need to iterate further in the clause
                        # if the literal that just made the unit clause SAT is in this current clause and is xi
                        elif (clauses[j].contains(lit)) and (polarity == POS_LIT):
                            for k, _ in clauses[j].var_polarities().items():
                                # If literal is the complement of the literal that just made the unit clause SAT...
                                if (k == lit) and (clauses[j].var_polarity(k) == NEG_LIT):
                                    clauses[j].remove_var(k) # Remove the complement literal
                                    break # Removed complement. No need to iterate further in the clause
                    # Removed clause. No need to further iterate
                    break
        i += 1
    # Return the assignments
    return assignments


def dpll_rec(clauses: list[Clause], assignments: dict[int, int] | None = None, var_set: set[int] | None = None) -> dict[int, int]:
    '''
    The recursive function implementation for dpll().
    Arguments:
    - `clauses` = represent the CNF clauses for the boolean function, F.
    - `assignments` = current variable assignments (if any).
    - `var_set` = set of variables which may be included in an assignment to evaluate the boolean function.
    Returns: the assignment (if any) for the set of variables that make F be SAT.
    '''
    # By default, assignments are empty (vars are all unassigned).
    assignments = dict() if assignments is None else assignments
    # By default work with all variables that are present in the clauses.
    var_set = clauses_all_vars(clauses) if var_set is None else var_set
    # Base cases:
    # - if all clauses are SAT, then then the function is SAT.
    # - if any clause is UNSAT, then the function is UNSAT.
    # - if there are no clauses, then the function is SAT.
    if not clauses:
        return assignments # SAT
    # Call unit_propagate() to SAT any unit clauses
    anyUndecidedClause: bool = False
    for clause in clauses:
        value = clause.value_cnf(assignments)
        if value == UNSAT:
            # If any clause is UNSAT, then the whole function is UNSAT.
            return {} # UNSAT
        elif value == UNDECIDED:
            # We only need to see that one clause is undecided to know if any are undecided.
            anyUndecidedClause = True
            #if clause.isUnit == True:
            #    assignments = unit_propagate(clauses, assignments)
    if anyUndecidedClause:
        # At least one of the clauses is undecided.
        # Choose a literal to try to assign to 1 or to 0...
        # And try those options out by branching recursively.
        xi = decide_literal(var_set, assignments)
        if xi is None:
            # There are no undecided literals, so we can't make any more decisions.
            # This means that the function is UNSAT with previous assignments.
            return {}
        else:
            # Try both possibilities of assigning xi (choose the order randomly)
            value1: int = random.choice((0, 1))
            value2: int = 1 - value1 # inverts value1
            assignments[xi] = value1
            if (result := dpll_rec(clauses, assignments)):
                # SAT
                return result
            # Try xi=0
            assignments[xi] = value2
            if (result := dpll_rec(clauses, assignments)):
                # SAT
                return result
            # If both xi=1 and xi=0 failed, then this whole recursive branch is UNSAT.
            # So return UNSAT to the callee (probably the previous recursive call).
            del assignments[xi] # undo the decision
            return {} # UNSAT
    else:
        # If no clauses are UNSAT and no clauses are undecided,
        # then all clauses are SAT and the whole function is SAT!
        return assignments # SAT


def dpll_iterative(clauses: list[Clause], assignments: dict[int, int] | None = None, var_set: set[int]|None=None) -> dict[int, int]:
    '''
    The iterative function implementation for dpll().
    Arguments:
    - `clauses` = represent the CNF clauses for the boolean function, F.
    - `assignments` = current variable assignments (if any).
    - `var_set` = set of variables which may be included in an assignment to evaluate the boolean function.
    Returns: the assignment (if any) for the set of variables that make F be SAT.
    '''
    # global for saving the original list of clauses derived
    #global original_clauses
    # Make a copy of the clauses to use to evaluate the clauses
    #original_clauses = deepcopy(clauses)

    if not clauses:
        # Edge case where clauses is empty.
        # It's not possible to make any decisions/assignments, so return empty dictionary,
        # which is considered UNSAT.
        return {}
    
    # By default work with all variables that are present in the clauses.
    var_set = clauses_all_vars(clauses) if var_set is None else var_set

    # By default, assignments are empty (vars are all unassigned).
    assignments1: dict[int, int] = dict() if assignments is None else assignments
    assignments2: dict[int,int] = assignments1.copy()

    # Start the stack of assigments to try
    starting_xi = decide_literal(var_set, assignments1)
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
        for clause in clauses:
            value = clause.value_cnf(current_assignments)
            if value == UNSAT:
                # If any clause is UNSAT, then the whole function is UNSAT.
                anUNSATClause = clause
                break
            elif (not anyUndecidedClause) and (value == UNDECIDED):
                # We only need to see that one clause is undecided to know if any are undecided.
                anyUndecidedClause = True
                #current_assignments = unit_propagate(clauses, current_assignments)

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
            # At least one of the clauses is undecided,
            # So lets add two decisions to the stack to try next...
            xi = decide_literal(var_set, current_assignments)
            if xi is None:
                # There are no undecided literals, so we can't make any more decisions.
                # This means that the function is UNSAT.
                # NOTE: there are no new assignments to push, so this case is where the stack size will shrink.
                continue # UNSAT
            else:
                # Add the assignment where, first, xi = randomly 0 or 1.
                # (We don't need to make a copy of the `current_assignments` dictionary, because it is not used again after this loop iteration.)
                value1 = random.choice((0, 1))
                value2 = 1 - value1 # inverts value1
                current_assignments[xi] = value1
                stack.append(current_assignments)
                # Then add the assignment where xi = the opposite of the first choice.
                # (Make a copy of the dictionary this time, because we need to make a different decision.)
                assignments2 = current_assignments.copy()
                assignments2[xi] = value2
                stack.append(assignments2)

    # UNSAT due to no more possible assignments on the stack.
    return {} # UNSAT


def make_blocking_clause(assignments: dict[int,Any]) -> Clause:
    '''
    Create a clause that blocks the solution given by the assignments.
    Just have to negate the current decided assignments.
    '''
    pos = [xi for xi, v in assignments.items() if v == NEG_LIT] # negated
    neg = [xi for xi, v in assignments.items() if v == POS_LIT] # negated
    return Clause(pos, neg)


def find_all_SAT(clauses: list[Clause]) -> list[dict[int, int]]:
    '''
    Find all satisfying assignments for a boolean function in CNF.
    '''
    solutions: list[dict[int, int]] = []
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
    a_out = find_max_var(clauses_a.cnf_clauses)
    b_out = find_max_var(clauses_b.cnf_clauses)

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


def test_clause_value():
    '''
    Test the Clause.value_cnf() function
    '''
    # test one positive literal (x1)
    c = Clause([1], [])

    # postive literal is set to 1
    v = c.value_cnf({1:1})
    assert(v == SAT)

    # Setting clause with only one literal to 0
    v = c.value_cnf({1:0})
    assert(v == UNSAT)

    # The only literal is undecided
    v = c.value_cnf({1:None})
    assert(v == UNDECIDED)

    # Test one negative literal (~x1)
    c = Clause([], [1])

    # assign the literal to 1, which makes the clause false
    v = c.value_cnf({1:1})
    assert(v == UNSAT)

    # assign the literal to 0, which makes the clause true
    v = c.value_cnf({1:0})
    assert(v == SAT)

    # The only literal is undecided
    v = c.value_cnf({1:None})
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
        actual = c.value_cnf(assignment)
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
        v = c.value_cnf(assignment)
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

    # Test 1 clause with 2 literals
    clauses = [ Clause([1, 2], []) ] # (x1 + x2)
    result = dpll_func(clauses)
    assert(result)
    assert(result.get(1) == 1 or result.get(2) == 1)

    # Test 2 clause with 2 literals
    clauses = [ Clause([1, 2], []), Clause([], [1, 2]) ] # (x1 + x2).(~x1 + ~x2)
    result = dpll_func(clauses)
    assert(result)
    assert(result.get(1) == 1 or result.get(2) == 1)
    assert(result.get(1) == 0 or result.get(2) == 0)

    # Test 2 clause with 2 literals
    clauses = [ Clause([2], [1]), Clause([1], [2]) ] # (~x1 + x2).(x1 + ~x2)
    result = dpll_func(clauses)
    assert(result)
    assert((result.get(1) == 1 and result.get(2) == 1)
           or (result.get(1) == 0 and result.get(2) == 0))


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


def test_convert_SOP_to_CNF():
    print('Testing convert_SOP_to_CNF()')
    
    # try single-variable SOP clauses of "x1" up to "x100"
    for xi in range(1, 100):
        # positive clauses
        sop = [ Clause([xi], []) ] # "xi"
        cnf = convert_SOP_to_CNF(sop) # "(xi)"
        assert(cnf[0].vars() == {xi})
        assert(cnf[0].var_polarity(xi) == POS_LIT)

        # negative clauses
        sop = [ Clause([], [xi]) ] # "~xi"
        cnf = convert_SOP_to_CNF(sop) # "(~xi)"
        assert(cnf[0].vars() == {xi})
        assert(cnf[0].var_polarity(xi) == NEG_LIT)

    # try a single SOP clause with 2 variables
    sop = [ Clause([1, 2], []) ] # "x1 . x2"
    cnf = convert_SOP_to_CNF(sop) # should be "(x1)(x2)"
    assert(len(cnf) == 2)
    assert(cnf[0].vars() == {1})
    assert(cnf[0].var_polarity(1) == POS_LIT)
    assert(cnf[1].vars() == {2})
    assert(cnf[1].var_polarity(2) == POS_LIT)

    # try a single SOP clause with 2 variables
    sop = [ Clause([1], [2]) ] # "x1 . ~x2"
    cnf = convert_SOP_to_CNF(sop) # should be "(x1)(~x2)"
    assert(len(cnf) == 2)
    assert(cnf[0].vars() == {1})
    assert(cnf[0].var_polarity(1) == POS_LIT)
    assert(cnf[1].var_polarity(2) == NEG_LIT)

    # try a single SOP clause with conflicting variables
    error = False
    try:
        sop = [ Clause([99], [99]) ] # "xi . ~xi"
        cnf = convert_SOP_to_CNF(sop) # should be "(xi . ~x1)""
        assert(cnf[0].vars() == {99})
        assert(cnf[0].var_polarity(99) == 'BOTH')
    except ValueError:
        error = True
    assert(error)


def test_SAT_cnf():
    '''Test all functions in this file (SAT_cnf.py).'''
    print("Testing SAT_cnf.py")
    test_parse_SOP_string()
    test_convert_SOP_to_CNF()
    test_clause_value()
    test_dpll(dpll_rec)
    test_dpll(dpll_iterative)
    print('All tests passed!')


def print_clauses_as_DIMACS(clauses: list[Clause]):
    '''
    Print the given CNF clauses in DIMACS format.
    '''
    # Get the maximum variable index
    max_var_i = find_max_var(clauses)
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
    print(CNF_to_string(clauses))
    return clauses


def read_sop_file(file_path: str) -> tuple[list[Clause], set[int]]:
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
        original_vars = clauses_all_vars(sop)
        print('Parsed result:', SOP_to_string(sop))
        # Convert the string to CNF form
        cnf = convert_SOP_to_CNF(sop)
        # Print the CNF clause list
        print('Converting to CNF, clauses are:')
        print(CNF_to_string(cnf)) # print clause list
        return cnf, original_vars


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
        print('Parsed result:', '+'.join([x.str_SOP() for x in sop1]))
        print('Parsing SOP input:', function2)
        # Parse the string input
        sop2 = parse_SOP_string(function2)
        print('Parsed result:', '+'.join([x.str_SOP() for x in sop2]))
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


def SOP_to_string(sop_clauses: list[Clause]) -> str:
    sorted_clauses = sorted(sop_clauses, key=lambda c: len(c.vars()))
    return " + ".join([f"({c.str_SOP()})" for c in sorted_clauses])


def CNF_to_string(cnf_clauses: list[Clause]) -> str:
    sorted_clauses = sorted(cnf_clauses, key=lambda c: len(c.vars()))
    return ".".join([f"({c.str_CNF()})" for c in sorted_clauses])


def func_assignment_to_string(var_set: set[int], assignments: dict[int, int]) -> str:
    vals = []
    for xi, v in sorted(assignments.items()):
        if xi in var_set:
            vals.append(f"x{xi}={v}")
    return ", ".join(vals)


def main():
    is_sop_input = False
    if is_sop_input:
        # SOP string input
        txt = "x1.~x3.~x4 + x2.~x1.x5 + x1.~x5.~x3.~x4"
        sop = parse_SOP_string(txt)
        print("SOP:", SOP_to_string(sop))
        variables = clauses_all_vars(sop)
        cnf = convert_SOP_to_CNF(sop)
        print("CNF:", CNF_to_string(cnf))
        solutions = find_all_SAT(cnf)
        if solutions:
            print("Function is SAT with these assignments:")
        else:
            print("Function is UNSAT")
        for sol in solutions:
            print(func_assignment_to_string(variables, sol))
    else:
        # DIMACS input
        cnf = read_DIMACS_file("xor.cnf")
        variables = clauses_all_vars(cnf)
        print("CNF:", CNF_to_string(cnf))
        solutions = find_all_SAT(cnf)
        if solutions:
            print("Function is SAT with these assignments:")
        else:
            print("Function is UNSAT")
        for sol in solutions:
            print(func_assignment_to_string(variables, sol))

if __name__ == "__main__":
    #test_SAT_cnf()
    main()
