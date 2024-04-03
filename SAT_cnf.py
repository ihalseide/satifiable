import re
from typing import Any, Iterable
import random
import argparse
import copy
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


class Clause(object):
    '''
    Clause class, which represents a clause in (CNF) Conjunctive Normal Form
    (although it is sometimes used as a convenient container for DNF terms).

    When this class is used in the SAT-search algorithms, a CNF clause goes to the inverted/negated boolean function ~F,
    which means that SAT will actually be looking for assignments that set all clauses to have a value of 0, which makes
    the value of ~F UNSAT, which makes F be SAT.
    '''

    # Prevent the addition of extra attributes to `Clause` instances.
    __slots__ = "positives", "negatives", "literals"


    def __init__(self, positives: Iterable[int] | None = None, negatives: Iterable[int] | None = None, literals: Iterable[int]|None = None):
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
        self.positives: frozenset[int] = frozenset() if positives is None else frozenset(positives) 
        self.negatives: frozenset[int] = frozenset() if negatives is None else frozenset(negatives) 
        self.literals: frozenset[int] = frozenset() if literals is None else frozenset(literals) 


    def __key(self) -> tuple:
        return (self.positives, self.negatives, self.literals)


    def __hash__(self):
        '''
        This method is implemented so we can put `Clause`s inside a `set`.
        Reference: [https://stackoverflow.com/questions/2909106/whats-a-correct-and-good-way-to-implement-hash]
        '''
        return hash(self.__key())


    def __eq__(self, other):
        if isinstance(other, Clause):
            return self.__key() == other.__key()
        return NotImplemented


    def __repr__(self) -> str:
        p = sorted(tuple(self.positives))
        n = sorted(tuple(self.negatives))
        l = sorted(tuple(self.literals))
        return f"Clause(positives={p}, negatives={n}, literals={l})"


    def without_vars(self, xis: Iterable[int]) -> 'Clause':
        '''Create a new `Clause` that has the given variables removed.'''
        positives = self.positives.difference(set(xis))
        negatives = self.negatives.difference(set(xis))
        return Clause(positives, negatives, self.literals)


    def has_var(self, xi: int) -> bool:
        '''
        Returns True only if this Clause contains the given variable.
        '''
        return (xi in self.positives) or (xi in self.negatives)
    

    def vars(self) -> frozenset[int]:
        '''
        Get the set of all variables in this clause.
        '''
        return self.positives.union(self.negatives)
    

    def polarity_of_all(self) -> dict[int, int | str | None]:
        '''
        Get the dictionary of all variables with their polarities within this clause.
        '''
        return { i: self.polarity_of(i) for i in self.vars() }


    def polarity_of(self, xi: int) -> int | str | None:
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
        

    def _string_vars(self) -> list[str]:
        '''Internal helper function for `str_DNF` and `str_CNF`'''
        result = []
        for lit in self.literals:
            result.append(str(lit))

        for i in sorted(self.vars()):
            if i in self.positives:
                result.append(f"x{i}")
            if i in self.negatives:
                result.append(f"~x{i}")
        return result


    def str_DNF(self) -> str:
        '''Get the string version of this clause as if it is in DNF form.'''
        return " . ".join(self._string_vars())


    def str_CNF(self) -> str:
        '''Get the string version of this clause as if it is in CNF form.'''
        return " + ".join(self._string_vars())
            
        
    def undecided_given(self, assignments: dict[int, int]) -> frozenset[int]:
        '''
        Return the set of undecided variables within this clause given the specific assignments so far.
        '''
        return self.vars().difference(assignments.keys())


    def value_given(self, assignments: dict[int,int]) -> str:
        '''
        Return the evaluated value this as a CNF clause if it is given the `assignments`.
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
    

    def status_given(self, assignments: dict[int,int]) -> tuple[str, frozenset[int]]:
        '''
        Returns the "status" of this CNF `Clause` given the `assignments`.
        The status returned is a tuple of: (the clause's value, and the set of the clause's undecided variables).
        '''
        return (self.value_given(assignments), self.undecided_given(assignments)) 


class ClauseList:
    '''
    Class to track:
    - The list of clauses in a given function.
    - The last variable index from SOP form.
    - The maximum variable index from CNF.
    '''
    def __init__(self, sop_input: str):
        # Store SOP clauses in this member
        self.sop_clauses = parse_DNF_string(sop_input)
        # Store CNF clauses in this member
        self.cnf_clauses = convert_DNF_to_CNF(self.sop_clauses)
        # Store the max variable from the SOP function input in this member
        self.input_max = find_clauses_highest_var(self.sop_clauses)

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


def clauses_all_vars(clauses: list[Clause]) -> set[int]:
    '''Get the set of all variables in a given list of Clauses'''
    result: set[int] = set()
    for clause in clauses:
        result.update(clause.vars())
    return result


def parse_DNF_string(text: str) -> list[Clause]: # list of product terms, not CNF clauses!
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
        raise ValueError("empty boolean function string")
    # Make sure only this subset of characters is in the input string
    if not re.match(r"^([ \r\n.~+x0-9])+$", text, flags=re.IGNORECASE):
        raise ValueError("text string has forbidden characters for DNF a.k.a SOP form")
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
                raise ValueError(f"Invalid single literal in DNF/SOP term (dots are required): \"{lit}\"")
        clauses.append( Clause(positives, negatives, term_lits) )
    return clauses


def convert_DNF_to_CNF(product_terms: list[Clause]) -> list[Clause]:
    '''
    Convert a list of DNF clauses that represent a boolean function, F, into a list of CNF clauses that represent F.
    '''
    result: list[Clause] = []
    if len(product_terms) == 1:
        # Only one term, so expand it out into 1-variable CNF clauses
        term = product_terms[0]
        for x_i, polarity in term.polarity_of_all().items():
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
            one_positives: set[int] = set()
            one_negatives: set[int] = set()
            for term in product_terms:
                one_positives.update(term.positives)
                one_negatives.update(term.negatives)
            result.append(Clause(one_positives, one_negatives))
            return result
        else:
            # Multiple terms with multiple variables
            xi = find_clauses_highest_var(product_terms) + 1
            or_first_in_i = xi
            # Keep track of the inputs to the OR gate, and their polarities.
            or_inputs: dict[int, int] = {}
            # Create AND gates for each product term
            for term in product_terms:
                num_vars = len(term.vars())
                if num_vars > 1:
                    # Create AND gate for this product term
                    add_GCF_for_and(result, term.polarity_of_all(), xi)
                    or_inputs[xi] = POS_LIT
                    xi += 1
                elif num_vars == 1:
                    # (Shortcut) Wire directly to the big OR GCF later
                    var, polarity = tuple(term.polarity_of_all().items())[0]
                    assert(polarity == POS_LIT or polarity == NEG_LIT)
                    or_inputs[var] = int(polarity)
            # Combine into one big OR gate
            add_GCF_for_or(result, or_inputs, xi)
            # Now that we have the gate consistency, make sure the output should be 1
            result.append(Clause({xi}, []))
            return result


def add_GCF_for_and(to_list: list[Clause], input_vars: dict[int, int | str | None], term_output_var: int):
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
    summation_positives: set[int] = set()
    summation_negatives: set[int] = set()
    summation_positives.add(term_output_var) # add z
    for x_i, polarity in input_vars.items():
        # Invert polarity of x_i
        if polarity == POS_LIT:
            summation_negatives.add(x_i)
        elif polarity == NEG_LIT:
            summation_positives.add(x_i)
        else:
            raise ValueError(f"'and' input variable #{x_i} has invalid polarity: {polarity}")
    to_list.append(Clause(summation_positives, summation_negatives))


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
    summation_positives: set[int] = set()
    summation_negatives: set[int] = set()
    summation_negatives.add(output_var) # add ~z
    for x_i, polarity in input_vars.items():
        # Keep polarity of x_i
        if polarity == POS_LIT:
            summation_positives.add(x_i)
        elif polarity == NEG_LIT:
            summation_negatives.add(x_i)
        else:
            raise ValueError(f"'or' input variable #{x_i} has invalid polarity: {polarity}")
    to_list.append(Clause(summation_positives, summation_negatives))


def find_clauses_highest_var(clauses: Iterable[Clause]) -> int:
    '''
    Find the maximum variable index in a list of CNF clauses.
    This is useful for knowing the upper limit of how many variables there are in a boolean function.
    Also useful for finding the output variable index.
    '''
    return max([max(clause.vars()) for clause in clauses])


def decide_variable(literal_set: set[int], decisions: dict[int, int]) -> int | None:
    '''
    Choose an unassigned literal to try next.
    The `literal_set` is the set of literals allowed to be chosen from.
    Returns the index of the literal to try next, or `None` if there are no undecided literals.
    '''
    unassigned = literal_set.difference(decisions.keys())
    if unassigned:
        return random.choice(tuple(unassigned))
    else:
        return None
    

def unit_decisions(clauses: frozenset[Clause], var_set: set[int], current_assignments: dict[int, int]) -> dict[int, int]:
    '''
    Return decided variable assignments to make using the unit clause trick.
    '''
    new_decisions: dict[int, int] = {}
    # Look for the variables of unit clauses
    for clause in clauses:
        undecided = var_set.intersection(clause.undecided_given(current_assignments))
        #print(f"clause has undecided vars: {undecided}")
        if len(undecided) == 1:
            # Unit clause
            xi = next(iter(undecided))
            polarity = clause.polarity_of(xi)
            already = new_decisions.get(xi)
            if already is not None and already != polarity:
                # Conflict
                pass
            elif already is None:
                if polarity == POS_LIT:
                    new_decisions[xi] = 1
                elif polarity == NEG_LIT:
                    new_decisions[xi] = 0
                else:
                    raise ValueError(f"variable {xi} has unexpected polarity {polarity}")
    return new_decisions


def dpll_rec(clauses: list[Clause], assignments: dict[int, int] | None = None, var_set: set[int] | None = None) -> dict[int, int]:
    '''
    The recursive function implementation for dumb dpll(), which doesn't apply any optimization.
    Used as a baseline to compare dpll_iter to.
    Arguments:
    - `clauses` = represent the CNF clauses for the boolean function, F.
    - `assignments` = current variable assignments (if any).
    - `var_set` = set of variables which may be included in an assignment to evaluate the boolean function.
    Returns: the assignment (if any) for the set of variables that make F be SAT.
    '''
    #print(f"dpll_rec(..., {assignments})")
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
    
    anyUndecidedClause: bool = False
    for clause in clauses:
        value = clause.value_given(assignments)
        if value == UNSAT:
            # If any clause is UNSAT, then the whole function is UNSAT.
            return {} # UNSAT
        elif value == UNDECIDED:
            # We only need to see that one clause is undecided to know if any are undecided.
            anyUndecidedClause = True

    if anyUndecidedClause:
        # At least one of the clauses is undecided.
        # Choose a literal to try to assign to 1 or to 0...
        # And try those options out by branching recursively.
        xi = decide_variable(var_set, assignments)
        if xi is None:
            # There are no undecided literals, so we can't make any more decisions.
            # This means that the function is UNSAT with previous assignments.
            return {}
        else:
            # Try both possibilities of assigning xi (choose the order randomly)
            value1, value2 = random_literal_pair()
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


# TODO: add unit propagation / other optimizations
def dpll_iterative(original_clauses: list[Clause], assignments: dict[int, int] | None = None, var_set: set[int]|None=None) -> dict[int, int]:
    '''
    The iterative function implementation for dpll().
    Arguments:
    - `clauses` = represent the CNF clauses for the boolean function, F.
    - `assignments` = current variable assignments (if any).
    - `var_set` = set of variables which may be included in an assignment to evaluate the boolean function.
    Returns: the assignment (if any) for the set of variables that make F be SAT.
    '''

    clauses = frozenset(original_clauses)
    #print("given clauses", CNF_to_string(clauses))
    ignored_clauses: set[Clause] = set()

    if not clauses:
        # Edge case where clauses is empty.
        # It's not possible to make any decisions/assignments, so return empty dictionary,
        # which is considered UNSAT.
        return {}
    
    # By default work with all variables that are present in the clauses.
    var_set = clauses_all_vars(original_clauses) if var_set is None else var_set
    #print(f"var_set: {var_set}")

    # By default, assignments are empty (vars are all unassigned).
    # Otherwise, use the given assignments.
    assignments1: dict[int, int] = dict() if assignments is None else assignments

    # Make first unit propagation decisions (can't be undone).
    unit_assign = unit_decisions(clauses, var_set, assignments1)
    assignments1.update(unit_assign)

    #print(f"initial assignments: {assignments1}")

    # Make first decision.
    starting_xi = decide_variable(var_set, assignments1)
    if starting_xi is None:
        # At this point, perhaps the unit assignment may or may not have made the function SAT.
        for clause in clauses:
            value = clause.value_given(assignments1)
            if value == UNSAT:
                return {} # UNSAT
            elif value == UNDECIDED:
                return {} # UNSAT
        return assignments1 # SAT
    
    assignments2: dict[int,int] = assignments1.copy()
    assignments1[starting_xi], assignments2[starting_xi] = random_literal_pair()

    # Initialize the stack
    stack: list[dict[int, int]] = [assignments1, assignments2]

    i = 0
    while stack:
        if (i > 0) and (i % 100_000 == 0):
            print(end='.', flush=True)
            if i % 1_000_000 == 0:
                print(end=str(i//1_000_000)+"M", flush=True)
        i += 1
        current_assignments = stack.pop()
        #print(f"(#{i}) try assignment = {current_assignments}")

        #print("  unit decisions would be:", func_assignment_to_string(var_set, unit_decisions(clauses, var_set, current_assignments)))

        undecided_clauses: set[Clause] = set()
        an_UNSAT_clause: Clause|None = None
        for clause in clauses:
            value = clause.value_given(current_assignments)
            if value == UNSAT:
                # If any clause is UNSAT, then the whole function is UNSAT.
                an_UNSAT_clause = clause
                break
            elif value == UNDECIDED:
                # Accumulate the undecided clauses for later.
                undecided_clauses.add(clause)

        #print("  unSAT clause:", an_UNSAT_clause.str_CNF() if an_UNSAT_clause else "<NONE>")
        #print("  undecided clauses :", CNF_to_string(undecided_clauses))

        if an_UNSAT_clause is not None:
            # This should be checked before anyUndecidedClause, because UNSAT takes precedence over UNDECIDED.
            # If any clause is UNSAT, then the whole function is UNSAT for this branch.
            # So, continue to next loop iteration to try the next branch(es) on the stack.
            continue
        elif not undecided_clauses:
            # If no clauses are UNSAT and no clauses are undecided,
            # then all clauses are SAT and the whole function is SAT!
            return current_assignments # SAT
        else:
            # At least one of the clauses is undecided,
            # So lets add two decisions to the stack to try next...
            xi = decide_variable(var_set, current_assignments)
            if xi is None:
                # There are no undecided literals, so we can't make any more decisions.
                # This means that the function is UNSAT.
                # NOTE: there are no new assignments to push, so this case is where the stack size will shrink.
                continue # UNSAT
            else:
                # Add the assignment where, first, xi = randomly 0 or 1.
                # (We don't need to make a copy of the `current_assignments` dictionary, because it is not used again after this loop iteration.)
                value1, value2 = random_literal_pair()
                current_assignments[xi] = value1
                stack.append(current_assignments)
                # Then add the assignment where xi = the opposite of the first choice.
                # (Make a copy of the dictionary this time, because we need to make a different decision.)
                assignments2 = current_assignments.copy()
                assignments2[xi] = value2
                stack.append(assignments2)

    # Empty stack.
    # UNSAT due to no more possible assignments on the stack.
    return {} # UNSAT


def random_literal_pair() -> tuple[int, int]:
    '''
    Get a randomly ordered pair of 0 and 1.
    Returns either (0, 1) or (1, 0).
    '''
    return random.choice(((0, 1), (1, 0)))


def make_blocking_clause(assignments: dict[int,Any]) -> Clause:
    '''
    Create a clause that blocks the solution given by the assignments.
    Just have to negate the current decided assignments.
    '''
    pos = [xi for xi, v in assignments.items() if v == NEG_LIT] # negated
    neg = [xi for xi, v in assignments.items() if v == POS_LIT] # negated
    return Clause(pos, neg)


def find_all_SAT(clauses: list[Clause], solver_func=dpll_rec) -> list[dict[int, int]]:
    '''
    Find all satisfying assignments for a boolean function in CNF.
    '''
    solutions: list[dict[int, int]] = []
    # Use the DPLL algorithm to find all solutions
    while (solution := solver_func(clauses)):
        # Add the current solution to the list of solutions
        solutions.append(solution)
        # Add a new clause to the CNF that blocks the current solution
        # (i.e. add a clause that makes the current solution UNSAT).
        # This is called "blocking" the solution.
        clauses.append(make_blocking_clause(solution))
    return solutions


def xor_CNF_functions(clauses_a: Iterable[Clause], clauses_b: Iterable[Clause]) -> list[Clause]:
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
    a_out = find_clauses_highest_var(clauses_a)
    b_out = find_clauses_highest_var(clauses_b)

    # Get the next variable index that would come after those, so we can
    # introduce new variables to implement GCFs.
    next_literal_i = 1 + max(a_out, b_out)

    # These are the new variables for the gate outputs
    not_a_yes_b_out = next_literal_i + 1 # for the first AND gate output
    yes_a_not_b_out = next_literal_i + 2 # for the second AND gate output
    or_out = next_literal_i + 3 # for the final OR gate output

    # Implement AND gate for: (~a . b) -> not_a_yes_b_out
    add_GCF_for_and(clauses_result, { a_out: NEG_LIT, b_out: POS_LIT }, not_a_yes_b_out)

    # Implement AND gate for: (a . ~b) -> yes_a_not_b_out
    add_GCF_for_and(clauses_result, { a_out: POS_LIT, b_out: NEG_LIT }, yes_a_not_b_out)

    # Implement OR gate for combining the above two AND gates
    add_GCF_for_or(clauses_result, { not_a_yes_b_out: POS_LIT, yes_a_not_b_out: POS_LIT }, or_out)

    return clauses_result


def test_clause_value():
    '''
    Test the Clause.value_cnf() function
    '''
    # test one positive literal (x1)
    c = Clause([1], [])

    # postive literal is set to 1
    v = c.value_given({1:1})
    assert(v == SAT)

    # Setting clause with only one literal to 0
    v = c.value_given({1:0})
    assert(v == UNSAT)

    # The only literal is undecided
    v = c.value_given({1:None})
    assert(v == UNDECIDED)

    # Test one negative literal (~x1)
    c = Clause([], [1])

    # assign the literal to 1, which makes the clause false
    v = c.value_given({1:1})
    assert(v == UNSAT)

    # assign the literal to 0, which makes the clause true
    v = c.value_given({1:0})
    assert(v == SAT)

    # The only literal is undecided
    v = c.value_given({1:None})
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
        actual = c.value_given(assignment)
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
        v = c.value_given(assignment)
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


def test_parse_DNF_string():
    print('Testing parse_SOP_string()')
    
    a = parse_DNF_string("1")
    assert(len(a) == 1)
    c = a[0]
    assert(1 in c.literals)
    assert(0 not in c.literals)
    assert(not c.positives)
    assert(not c.negatives)

    a = parse_DNF_string("0")
    assert(len(a) == 1)
    c = a[0]
    assert(1 not in c.literals)
    assert(0 in c.literals)
    assert(not c.positives)
    assert(not c.negatives)

    a = parse_DNF_string("1 . 1")
    assert(len(a) == 1)
    c = a[0]
    assert(1 in c.literals)
    assert(0 not in c.literals)
    assert(not c.positives)
    assert(not c.negatives)

    a = parse_DNF_string("1 . 0")
    assert(len(a) == 1)
    c = a[0]
    assert(1 in c.literals)
    assert(0 in c.literals)
    assert(not c.positives)
    assert(not c.negatives)

    a = parse_DNF_string("1 + 0")
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

    a = parse_DNF_string("x1")
    assert(len(a) == 1)
    c = a[0]
    assert(1 in c.positives)
    assert(not c.literals)
    assert(not c.negatives)

    a = parse_DNF_string("x1 + x2 + x3")
    assert(len(a) == 3)
    assert(1 in a[0].positives)
    assert(2 in a[1].positives)
    assert(3 in a[2].positives)
    assert(1 not in a[0].negatives)
    assert(2 not in a[1].negatives)
    assert(3 not in a[2].negatives)

    a = parse_DNF_string("x1 . ~x2")
    assert(len(a) == 1)
    assert(1 in a[0].positives)
    assert(2 not in a[0].positives)
    assert(1 not in a[0].negatives)
    assert(2 in a[0].negatives)

    a = parse_DNF_string("~x1 . x2")
    assert(len(a) == 1)
    assert(1 not in a[0].positives)
    assert(2 in a[0].positives)
    assert(1 in a[0].negatives)
    assert(2 not in a[0].negatives)

    a = parse_DNF_string("~x1 . ~x2")
    assert(len(a) == 1)
    assert(1 not in a[0].positives)
    assert(2 not in a[0].positives)
    assert(1 in a[0].negatives)
    assert(2 in a[0].negatives)

    a = parse_DNF_string("~x1 . x1 . x1")
    assert(len(a) == 1)
    assert(1 in a[0].negatives)
    assert(1 in a[0].positives)


def test_convert_DNF_to_CNF():
    print('Testing convert_DNF_to_CNF()')
    
    # try single-variable SOP clauses of "x1" up to "x100"
    for xi in range(1, 100):
        # positive clauses
        sop = [ Clause([xi], []) ] # "xi"
        cnf = convert_DNF_to_CNF(sop) # "(xi)"
        assert(cnf[0].vars() == {xi})
        assert(cnf[0].polarity_of(xi) == POS_LIT)

        # negative clauses
        sop = [ Clause([], [xi]) ] # "~xi"
        cnf = convert_DNF_to_CNF(sop) # "(~xi)"
        assert(cnf[0].vars() == {xi})
        assert(cnf[0].polarity_of(xi) == NEG_LIT)

    # try a single SOP clause with 2 variables
    sop = [ Clause([1, 2], []) ] # "x1 . x2"
    cnf = convert_DNF_to_CNF(sop) # should be "(x1)(x2)"
    assert(len(cnf) == 2)
    assert(cnf[0].vars() == {1})
    assert(cnf[0].polarity_of(1) == POS_LIT)
    assert(cnf[1].vars() == {2})
    assert(cnf[1].polarity_of(2) == POS_LIT)

    # try a single SOP clause with 2 variables
    sop = [ Clause([1], [2]) ] # "x1 . ~x2"
    cnf = convert_DNF_to_CNF(sop) # should be "(x1)(~x2)"
    assert(len(cnf) == 2)
    assert(cnf[0].vars() == {1})
    assert(cnf[0].polarity_of(1) == POS_LIT)
    assert(cnf[1].polarity_of(2) == NEG_LIT)

    # try a single SOP clause with conflicting variables
    error = False
    try:
        sop = [ Clause([99], [99]) ] # "xi . ~xi"
        cnf = convert_DNF_to_CNF(sop) # should be "(xi . ~x1)""
        assert(cnf[0].vars() == {99})
        assert(cnf[0].polarity_of(99) == 'BOTH')
    except ValueError:
        error = True
    assert(error)


def test_SAT_cnf():
    '''Test all functions in this file (SAT_cnf.py).'''
    print("Testing SAT_cnf.py")
    test_parse_DNF_string()
    test_convert_DNF_to_CNF()
    test_clause_value()
    test_dpll(dpll_rec)
    test_dpll(dpll_iterative)
    print('All tests passed!')


def print_clauses_as_DIMACS(clauses: list[Clause]):
    '''
    Print the given CNF clauses in DIMACS format.
    '''
    # Get the maximum variable index
    max_var_i = find_clauses_highest_var(clauses)
    # Print the header
    print(f"p cnf {max_var_i} {len(clauses)}")
    # Print each clause
    for clause in clauses:
        # Get the list of literals in the clause
        literals = sorted(clause.polarity_of_all().items())
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


def read_DNF_file(file_path: str) -> tuple[list[Clause], set[int]]:
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
        sop = parse_DNF_string(function)
        original_vars = clauses_all_vars(sop)
        print('Parsed result:', DNF_to_string(sop))
        # Convert the string to CNF form
        cnf = convert_DNF_to_CNF(sop)
        # Print the CNF clause list
        print('Converting to CNF, clauses are:')
        print(CNF_to_string(cnf)) # print clause list
        return cnf, original_vars


def read_DNF_file_xor(file_path: str) -> tuple[ClauseList, ClauseList]:
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
        sop1 = parse_DNF_string(function1)
        print('Parsed result:', '+'.join([x.str_DNF() for x in sop1]))
        print('Parsing SOP input:', function2)
        # Parse the string input
        sop2 = parse_DNF_string(function2)
        print('Parsed result:', '+'.join([x.str_DNF() for x in sop2]))
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


def DNF_to_string(dnf_clauses: Iterable[Clause]) -> str:
    '''
    Turn a list of SOP clauses into a nice readable string.
    '''
    sorted_clauses = sorted(dnf_clauses, key=lambda c: len(c.vars()))
    return " + ".join([f"({c.str_DNF()})" for c in sorted_clauses])


def CNF_to_string(cnf_clauses: Iterable[Clause]) -> str:
    '''
    Turn a list of CNF clauses into a nice readable string.
    '''
    sorted_clauses = sorted(cnf_clauses, key=lambda c: len(c.vars()))
    return ".".join([f"({c.str_CNF()})" for c in sorted_clauses])


def func_assignment_to_string(var_set: set[int], assignments: dict[int, int]) -> str:
    '''
    Turn a dictionary of variable assignments into a nice readable string.
    '''
    vals = []
    for xi, v in sorted(assignments.items()):
        if xi in var_set:
            vals.append(f"x{xi}={v}")
    return ", ".join(vals)


def _sat_result(cnf, variables):
    print("Running SAT...")
    sol = dpll_iterative(cnf)
    if sol:
        print("found SAT solution:", func_assignment_to_string(variables, sol))
    else:
        print("UNSAT")
    # for f in (dpll_iterative, dpll_rec):
    #     print(f">>>>>>>>>> solving using {f.__name__} ...")
    #     solutions = find_all_SAT(cnf.copy(), f)
    #     if solutions:
    #         print("Function is SAT with these assignments:")
    #     else:
    #         print("Function is UNSAT")
    #     for s in solutions:
    #         print(func_assignment_to_string(variables, s))
    

def main():
    test_SAT_cnf()

    # SOP string input
    print("============ Running function in SOP file... ============")
    txt = "x1.~x2 + ~x1.x2"
    sop = parse_DNF_string(txt)
    print("SOP:", DNF_to_string(sop))
    variables = clauses_all_vars(sop)
    cnf = convert_DNF_to_CNF(sop)
    print("CNF:", CNF_to_string(cnf))
    _sat_result(cnf, variables)

    # DIMACS input
    print("============ Running function in DIMACS file... ============")
    cnf = read_DIMACS_file("xor.cnf")
    variables = clauses_all_vars(cnf)
    print("CNF:", CNF_to_string(cnf))
    _sat_result(cnf, variables)


if __name__ == "__main__":
    main()
