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

    #Create a list of feasible values in the domain of all unassigned cells
    dom = []
    for i in range(1,len(futo_grid)+1):
        dom.append(i)

    all_vars = []

    #Create a variable type for all indices that are numeric
    for i in range(len(futo_grid)):
        row_vars = []
        for j in range(len(futo_grid[i])):
            #Check if a cell is numeric
            if type(futo_grid[i][j]) == int:
                #Check to see if the cell is 0, if it is assign its domain to the dom list made above
                if futo_grid[i][j] == 0:
                    row_vars.append(Variable(f'X{i}{j}', dom.copy()))
                #Otherwise, assign its domain to the singular value specified at its index
                else:
                    row_vars.append(Variable(f'X{i}{j}', [futo_grid[i][j]]))
        #Add all the row variables to the all_vars list
        all_vars.append(row_vars)

    #Create a list of constriants
    cons = []
    #Iterate through n cells (nxn grid)
    for i in range(len(futo_grid)):
        for j in range(len(futo_grid)):
            #go to the cell right of j
            for k in range(j+1, len(futo_grid)):
                #all_vars is the list of variables (excluding the inequalities), so we can index on this 
                con = Constraint(f'Row-{i}-X{i}{j}-X{i}{k}', [all_vars[i][j], all_vars[i][k]])  
                #satisfiable variabels are any variable not equal to itself
                sat_list = []
                for x in dom: 
                    for y in dom:  
                        if x != y:  
                            sat_list.append((x, y))
                con.add_satisfying_tuples(sat_list)
                cons.append(con)
    
    #Iterate through n cells (nxn grid)
    for i in range(len(futo_grid)):
        for j in range(len(futo_grid)):
            #go to the cell below j
            for k in range(j+1, len(futo_grid)):
                #all_vars is the list of variables (excluding the inequalities), so we can index on this 
                con = Constraint(f'Col-{i}-X{j}{i}-X{k}{i}', [all_vars[j][i], all_vars[k][i]])
                #satisfiable variabels are any value not equal to itself
                sat_list = []
                for x in dom: 
                    for y in dom:  
                        if x != y:  
                            sat_list.append((x, y))  
                con.add_satisfying_tuples(sat_list)
                cons.append(con)
    
    #Iterate through n cells (nxn grid)
    for i in range(len(futo_grid)):
        for j in range(len(futo_grid[i])):
            #see if there is a greater than constraint
            if futo_grid[i][j] == '<':
                #Get the left pointer by dividing the index of j by 2 and taking the floor
                lp = all_vars[i][j // 2] 
                #Get the right pointer by dividing the index of j by 2 and adding 1 (get the ceiling)
                rp = all_vars[i][(j // 2) + 1]  
                con = Constraint(f'Ineq{i}{j}',[lp,rp])
                #Satisfiable variables are any value y greater than x
                sat_list = []
                for x in dom: 
                    for y in dom:  
                        if x < y:  
                            sat_list.append((x, y))
                con.add_satisfying_tuples(sat_list)
                cons.append(con)

            #see if there is a less than constraint
            elif futo_grid[i][j] == '>':
                #Get the left pointer by dividing the index of j by 2 and taking the floor
                lp = all_vars[i][j // 2]  
                #Get the right pointer by dividing the index of j by 2 and adding 1 (get the ceiling)
                rp = all_vars[i][(j // 2) + 1]  
                con = Constraint(f'Ineq{i}{j}',[lp,rp])
                #Satisfiable variables are any value y less than x
                sat_list = []
                for x in dom: 
                    for y in dom:  
                        if x > y:  
                            sat_list.append((x, y))
                con.add_satisfying_tuples(sat_list)
                cons.append(con)

    
    final_list = [] 
    for i in all_vars:
        for j in i:
           final_list.append(j) 
    #Intialize the CSP by adding the variables and the constraints             
    csp = CSP("Futoshiki_CSP_Model_1", final_list)
    for i in cons:
        csp.add_constraint(i)
    return csp, all_vars #Return the CSP and all the variables

def futoshiki_csp_model_2(futo_grid):
    ##IMPLEMENT

    #Create a list of feasible values in the domain of all unassigned cells
    dom = []
    for i in range(1,len(futo_grid)+1):
        dom.append(i)

    all_vars = []

    #Create a variable type for all indices that are numeric
    for i in range(len(futo_grid)):
        row_vars = []
        for j in range(len(futo_grid[i])):
            #Check if a cell is numeric
            if type(futo_grid[i][j]) == int:
                #Check to see if the cell is 0, if it is assign its domain to the dom list made above
                if futo_grid[i][j] == 0:
                    row_vars.append(Variable(f'X{i}{j}', dom.copy()))
                #Otherwise, assign its domain to the singular value specified at its index
                else:
                    row_vars.append(Variable(f'X{i}{j}', [futo_grid[i][j]]))
        #Add all the row variables to the all_vars list
        all_vars.append(row_vars)

    #Create a list of constriants
    cons = []
    #Make all-diff constraint
    for i in range(len(futo_grid)):
        con = Constraint(f'Row-{i}-AllDiff', all_vars[i])
        sat_list = []  
        #Add all permutations to sat_list 
        for j in itertools.permutations(dom, len(futo_grid)):  
            perm_list = list(j)  
            sat_list.append(perm_list) 
        con.add_satisfying_tuples(sat_list)
        cons.append(con)

    #Create a list of column variables for column all-diff
    column_group = []  
    for col in range(len(futo_grid)):
        column = []  
        # Iterate over each row index
        for row in range(len(futo_grid)):
            column.append(all_vars[row][col])  
        column_group.append(column)  
        
    #Iterate through the column groups and make all-diff constraint   
    for i in range(len(column_group)):
        con = Constraint(f'Col-{i}-AllDiff', column_group[i])  
        sat_list = []  
        #Add all permutations to sat_list 
        for k in itertools.permutations(dom, len(futo_grid)):
            perm_list = list(k)  
            sat_list.append(perm_list) 

        con.add_satisfying_tuples(sat_list)
        cons.append(con)
            
    #Iterate through n cells (nxn grid)
    for i in range(len(futo_grid)):
        for j in range(len(futo_grid[i])):
            #see if there is a greater than constraint
            if futo_grid[i][j] == '<':
                #Get the left pointer by dividing the index of j by 2 and taking the floor
                lp = all_vars[i][j // 2] 
                #Get the right pointer by dividing the index of j by 2 and adding 1 (get the ceiling)
                rp = all_vars[i][(j // 2) + 1]  
                con = Constraint(f'Ineq{i}{j}',[lp,rp])
                #Satisfiable variables are any value y greater than x
                sat_list = []
                for x in dom: 
                    for y in dom:  
                        if x < y:  
                            sat_list.append((x, y))
                con.add_satisfying_tuples(sat_list)
                cons.append(con)

            #see if there is a less than constraint
            elif futo_grid[i][j] == '>':
                #Get the left pointer by dividing the index of j by 2 and taking the floor
                lp = all_vars[i][j // 2]  
                #Get the right pointer by dividing the index of j by 2 and adding 1 (get the ceiling)
                rp = all_vars[i][(j // 2) + 1]  
                con = Constraint(f'Ineq{i}{j}',[lp,rp])
                #Satisfiable variables are any value y less than x
                sat_list = []
                for x in dom: 
                    for y in dom:  
                        if x > y:  
                            sat_list.append((x, y))
                con.add_satisfying_tuples(sat_list)
                cons.append(con)



    final_list = [] 
    for i in all_vars:
        for j in i:
           final_list.append(j) 
    #Intialize CSP
    csp = CSP("Futoshiki_CSP_Model_2", final_list)
    for i in cons:
        csp.add_constraint(i)

    return csp, all_vars #Return the CSP and all the variables


