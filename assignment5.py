#!/usr/bin/python

import copy
import itertools

class CSP:
    def __init__(self):
        # self.variables is a list of the variable names in the CSP
        self.variables = []

        # self.domains[i] is a list of legal values for variable i
        self.domains = {}

        # self.constraints[i][j] is a list of legal value pairs for
        # the variable pair (i, j)
        self.constraints = {}

        #Variables for stats
        self.number_calls = 0
        self.number_failures = 0

    def add_variable(self, name, domain):
        """Add a new variable to the CSP. 'name' is the variable name
        and 'domain' is a list of the legal values for the variable.
        """
        self.variables.append(name)
        self.domains[name] = list(domain)
        self.constraints[name] = {}

    def get_all_possible_pairs(self, a, b):
        """Get a list of all possible pairs (as tuples) of the values in
        the lists 'a' and 'b', where the first component comes from list
        'a' and the second component comes from list 'b'.
        """
        return itertools.product(a, b)

    def get_all_arcs(self):
        """Get a list of all arcs/constraints that have been defined in
        the CSP. The arcs/constraints are represented as tuples (i, j),
        indicating a constraint between variable 'i' and 'j'.
        """
        return [ (i, j) for i in self.constraints for j in self.constraints[i] ]

    def get_all_neighboring_arcs(self, var):
        """Get a list of all arcs/constraints going to/from variable
        'var'. The arcs/constraints are represented as in get_all_arcs().
        """
        return [ (i, var) for i in self.constraints[var] ]

    def add_constraint_one_way(self, i, j, filter_function):
        """Add a new constraint between variables 'i' and 'j'. The legal
        values are specified by supplying a function 'filter_function',
        that returns True for legal value pairs and False for illegal
        value pairs. This function only adds the constraint one way,
        from i -> j. You must ensure that the function also gets called
        to add the constraint the other way, j -> i, as all constraints
        are supposed to be two-way connections!
        """
        if not j in self.constraints[i]:
            # First, get a list of all possible pairs of values between variables i and j
            self.constraints[i][j] = self.get_all_possible_pairs(self.domains[i], self.domains[j])

        # Next, filter this list of value pairs through the function
        # 'filter_function', so that only the legal value pairs remain
        self.constraints[i][j] = filter(lambda value_pair: filter_function(*value_pair), self.constraints[i][j])

    def add_all_different_constraint(self, variables):
        """Add an Alldiff constraint between all of the variables in the
        list 'variables'.
        """
        for (i, j) in self.get_all_possible_pairs(variables, variables):
            if i != j:
                self.add_constraint_one_way(i, j, lambda x, y: x != y)

    def backtracking_search(self):
        """This functions starts the CSP solver and returns the found
        solution.
        """
        # Make a so-called "deep copy" of the dictionary containing the
        # domains of the CSP variables. The deep copy is required to
        # ensure that any changes made to 'assignment' does not have any
        # side effects elsewhere.
        assignment = copy.deepcopy(self.domains)

        # Run AC-3 on all constraints in the CSP, to weed out all of the
        # values that are not arc-consistent to begin with
        self.inference(assignment, self.get_all_arcs())

        # Call backtrack with the partial assignment 'assignment'
        return self.backtrack(assignment)

    def backtrack(self, assignment):
        """The function 'Backtrack' from the pseudocode in the
        textbook.

        The function is called recursively, with a partial assignment of
        values 'assignment'. 'assignment' is a dictionary that contains
        a list of all legal values for the variables that have *not* yet
        been decided, and a list of only a single value for the
        variables that *have* been decided.

        When all of the variables in 'assignment' have lists of length
        one, i.e. when all variables have been assigned a value, the
        function should return 'assignment'. Otherwise, the search
        should continue. When the function 'inference' is called to run
        the AC-3 algorithm, the lists of legal values in 'assignment'
        should get reduced as AC-3 discovers illegal values.

        IMPORTANT: For every iteration of the for-loop in the
        pseudocode, you need to make a deep copy of 'assignment' into a
        new variable before changing it. Every iteration of the for-loop
        should have a clean slate and not see any traces of the old
        assignments and inferences that took place in previous
        iterations of the loop.
        """
        
        #Every time this functio is called, we have ont more backtracking step
        self.number_calls+=1

        #We search a variable for which we can select a value
        Xi = self.select_unassigned_variable(assignment)

        #If all variable have a value, then the problem is solved
        if Xi == None:
            return assignment

        #Either way, we try all the possible value fot this variable 
        for value in assignment[Xi]:

            #We create a deepcopy so that the next steps won't be affected by this one
            current_assignment = copy.deepcopy(assignment)

            #We select a value, i.e. we delete all the other possible values
            current_assignment[Xi] = [value]

            #We check if there is any modification due to an inference in the neighbors
            if self.inference(current_assignment, self.get_all_neighboring_arcs(Xi)):

                #If that's the case, we backtrack
                next_step = self.backtrack(current_assignment)

                #If the next step isn't a failure, it means we achieved to find a solution
                if next_step != False:
                    return next_step

        #If we didn't find a solution after trying all the values, it means that we need to change something in the previous steps
        self.number_failures+=1
        return False

    def select_unassigned_variable(self, assignment):
        """The function 'Select-Unassigned-Variable' from the pseudocode
        in the textbook. Should return the name of one of the variables
        in 'assignment' that have not yet been decided, i.e. whose list
        of legal values has a length greater than one.
        """
        
        #We go through all the variables of the problem
        for X in self.variables:

            #If the current variable has more than one possible value, it is not selected and we return it.
            if len(assignment[X]) > 1:
                return X

        #We didn't find any variable with more than one possible value. The game is solved. 
        return None

    def inference(self, assignment, queue):
        """The function 'AC-3' from the pseudocode in the textbook.
        'assignment' is the current partial assignment, that contains
        the lists of legal values for each undecided variable. 'queue'
        is the initial queue of arcs that should be visited.
        """

        #We loop on the elements of the stack
        while len(queue) > 0:

            #We get the first element
            (Xi, Xj) = queue.pop(0)

            #If we changed something in the neighbors, we propagate these modifications
            if self.revise(assignment, Xi, Xj):

                #If the variable has no possible value, we return a failure
                if len(assignment[Xi]) == 0:
                    return False

                #If it still has possible values, then we add all its neighbors to the queue
                for arc in self.get_all_neighboring_arcs(Xi):
                    queue.append(arc)
        
        #If we didn't encouter an empty variable, the inference was a success
        return True

    def revise(self, assignment, i, j):
        """The function 'Revise' from the pseudocode in the textbook.
        'assignment' is the current partial assignment, that contains
        the lists of legal values for each undecided variable. 'i' and
        'j' specifies the arc that should be visited. If a value is
        found in variable i's domain that doesn't satisfy the constraint
        between i and j, the value should be deleted from i's list of
        legal values in 'assignment'.
        """

        #We check all the possible values of i
        for legal_i in assignment[i]:
            #For the moment, we consider that we have to remove this 
            revised = True

            #We do the same for the possible values of j 
            for legal_j in assignment[j]:

                #If there is a constraint satisfying the tuple of these two values, we don't remove the value of i
                if (legal_i, legal_j) in self.constraints[i][j]:
                    revised = False

            #But if there is no possible value of j for which (i, j) has a constraint, we remove it. And we continue for the next value of i
            if revised:
                assignment[i].remove(legal_i)

        return revised


def create_map_coloring_csp():
    """Instantiate a CSP representing the map coloring problem from the
    textbook. This can be useful for testing your CSP solver as you
    develop your code.
    """
    csp = CSP()
    states = [ 'WA', 'NT', 'Q', 'NSW', 'V', 'SA', 'T' ]
    edges = { 'SA': [ 'WA', 'NT', 'Q', 'NSW', 'V' ], 'NT': [ 'WA', 'Q' ], 'NSW': [ 'Q', 'V' ] }
    colors = [ 'red', 'green', 'blue' ]
    for state in states:
        csp.add_variable(state, colors)
    for state, other_states in edges.items():
        for other_state in other_states:
            csp.add_constraint_one_way(state, other_state, lambda i, j: i != j)
            csp.add_constraint_one_way(other_state, state, lambda i, j: i != j)
    return csp

def create_sudoku_csp(filename):
    """Instantiate a CSP representing the Sudoku board found in the text
    file named 'filename' in the current directory.
    """
    csp = CSP()
    board = map(lambda x: x.strip(), open(filename, 'r'))

    for row in range(9):
        for col in range(9):
            if board[row][col] == '0':
                csp.add_variable('%d-%d' % (row, col), map(str, range(1, 10)))
            else:
                csp.add_variable('%d-%d' % (row, col), [ board[row][col] ])

    for row in range(9):
        csp.add_all_different_constraint([ '%d-%d' % (row, col) for col in range(9) ])
    for col in range(9):
        csp.add_all_different_constraint([ '%d-%d' % (row, col) for row in range(9) ])
    for box_row in range(3):
        for box_col in range(3):
            cells = []
            for row in range(box_row * 3, (box_row + 1) * 3):
                for col in range(box_col * 3, (box_col + 1) * 3):
                    cells.append('%d-%d' % (row, col))
            csp.add_all_different_constraint(cells)

    return csp

def print_sudoku_solution(solution):
    """Convert the representation of a Sudoku solution as returned from
    the method CSP.backtracking_search(), into a human readable
    representation.
    """
    for row in range(9):
        for col in range(9):
            print solution['%d-%d' % (row, col)][0],
            if col == 2 or col == 5:
                print '|',
        print
        if row == 2 or row == 5:
            print '------+-------+------'


### MAIN ###

#We first try to solve the map coloration problem, to see if everything is OK. 
print 'Solution for the map coloration problem\n'
m = create_map_coloring_csp()
print "%s\n\n" % m.backtracking_search() 
#We now print the stats 
print 'Backtrack function was called %d time(s)' % m.number_calls
print 'Backtrack function returned failure %d time(s)\n\n' % m.number_failures

#All the sudoku problems
sudoku_names = ['easy', 'medium', 'hard', 'veryhard']

#We loop on all problems
for name in sudoku_names:
    print 'Solution for: sudoku %s\n' % name

    #We create the CSP problem
    s = create_sudoku_csp('%s.txt' % name)

    #We search the solution and print it
    print_sudoku_solution(s.backtracking_search())

    #We now print the stats 
    print '\nBacktrack function was called %d time(s)' % s.number_calls
    print 'Backtrack function returned failure %d time(s)\n\n' % s.number_failures