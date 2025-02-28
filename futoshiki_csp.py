# Look for #IMPLEMENT tags in this file.
'''
All models need to return a CSP object, and a list of lists of Variable objects
representing the board. The returned list of lists is used to access the
solution.

For example, after these three lines of code

    csp, var_array = futoshiki_csp_model_1(board)
    solver = BT(csp)
    solver.bt_search(prop_FC, var_ord)

var_array[0][0].get_assigned_value() should be the correct value in the top left
cell of the Futoshiki puzzle.

1. futoshiki_csp_model_1 (worth 20/100 marks)
    - A model of a Futoshiki grid built using only
      binary not-equal constraints for both the row and column constraints.

2. futoshiki_csp_model_2 (worth 20/100 marks)
    - A model of a Futoshiki grid built using only n-ary
      all-different constraints for both the row and column constraints.
    
    The input board is specified as a list of n lists. Each of the n lists
    represents a row of the board. If a 0 is in the list it represents an empty
    cell. Otherwise if a number between 1--n is in the list then this
    represents a pre-set board position.

    Each list is of length 2n-1, with each space on the board being separated
    by the potential inequality constraints. '>' denotes that the previous
    space must be bigger than the next space; '<' denotes that the previous
    space must be smaller than the next; '.' denotes that there is no
    inequality constraint.

    E.g., the board

    -------
    | > |2|
    | | | |
    | | < |
    -------
    would be represented by the list of lists

    [[0,>,0,.,2],
     [0,.,0,.,0],
     [0,.,0,<,0]]

'''
import cspbase
import itertools

from cspbase import *
from propagators import *

def futoshiki_csp_model_1(futo_grid):
    ##IMPLEMENT

    
    dom = []
    for i in range(1,len(futo_grid)+1):
        dom.append(i)

    all_vars = []

    for i in range(len(futo_grid)):
        row_vars = []
        for j in range(len(futo_grid[i])):
            if type(futo_grid[i][j]) == int:
                if futo_grid[i][j] == 0:
                    row_vars.append(Variable(f'X{i}{j}', dom.copy()))
                else:
                    row_vars.append(Variable(f'X{i}{j}', [futo_grid[i][j]]))
        all_vars.append(row_vars)

    cons = []
    for i in range(len(futo_grid)):
        for j in range(len(futo_grid)):
            for k in range(j+1, len(futo_grid)):
                con = Constraint(f'Row-{i}-X{i}{j}-X{i}{k}', [all_vars[i][j], all_vars[i][k]])
                sat_list = [(x, y) for x in dom for y in dom if x != y] 
                con.add_satisfying_tuples(sat_list)
                cons.append(con)

    for i in range(len(futo_grid)):
        for j in range(len(futo_grid)):
            for k in range(j+1, len(futo_grid)):
                con = Constraint(f'Col-{i}-X{j}{i}-X{k}{i}', [all_vars[j][i], all_vars[k][i]])
                sat_list = [(x,y) for x in dom for y in dom if x != y]
                con.add_satisfying_tuples(sat_list)
                cons.append(con)
    
    for i in range(len(futo_grid)):
        for j in range(len(futo_grid[i])):
            if futo_grid[i][j] == '<':
                lp = all_vars[i][j // 2] 
                rp = all_vars[i][(j // 2) + 1]  
                con = Constraint(f'Ineq{i}{j}',[lp,rp])
                sat_list = [(x,y) for x in dom for y in dom if x < y]
                con.add_satisfying_tuples(sat_list)
                cons.append(con)

            elif futo_grid[i][j] == '>':
                lp = all_vars[i][j // 2]  
                rp = all_vars[i][(j // 2) + 1]  
                con = Constraint(f'Ineq{i}{j}',[lp,rp])
                sat_list = [(x,y) for x in dom for y in dom if x > y]
                con.add_satisfying_tuples(sat_list)
                cons.append(con)
    csp = CSP("Futoshiki_CSP_Model_1", [j for i in all_vars for j in i])
    for i in cons:
        csp.add_constraint(i)

    return csp, all_vars





def futoshiki_csp_model_2(futo_grid):
    ##IMPLEMENT
    pass