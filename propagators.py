# Look for #IMPLEMENT tags in this file. These tags indicate what has
# to be implemented to complete problem solution.

'''This file will contain different constraint propagators to be used within 
   bt_search.

   propagator == a function with the following template
      propagator(csp, newly_instantiated_variable=None)
           ==> returns (True/False, [(Variable, Value), (Variable, Value) ...]

      csp is a CSP object---the propagator can use this to get access
      to the variables and constraints of the problem. The assigned variables
      can be accessed via methods, the values assigned can also be accessed.

      newly_instaniated_variable is an optional argument.
      if newly_instantiated_variable is not None:
          then newly_instantiated_variable is the most
           recently assigned variable of the search.
      else:
          progator is called before any assignments are made
          in which case it must decide what processing to do
           prior to any variables being assigned. SEE BELOW

       The propagator returns True/False and a list of (Variable, Value) pairs.
       Return is False if a deadend has been detected by the propagator.
       in this case bt_search will backtrack
       return is true if we can continue.

      The list of variable values pairs are all of the values
      the propagator pruned (using the variable's prune_value method). 
      bt_search NEEDS to know this in order to correctly restore these 
      values when it undoes a variable assignment.

      NOTE propagator SHOULD NOT prune a value that has already been 
      pruned! Nor should it prune a value twice

      PROPAGATOR called with newly_instantiated_variable = None
      PROCESSING REQUIRED:
        for plain backtracking (where we only check fully instantiated 
        constraints) 
        we do nothing...return true, []

        for forward checking (where we only check constraints with one
        remaining variable)
        we look for unary constraints of the csp (constraints whose scope 
        contains only one variable) and we forward_check these constraints.

        for gac we establish initial GAC by initializing the GAC queue
        with all constaints of the csp


      PROPAGATOR called with newly_instantiated_variable = a variable V
      PROCESSING REQUIRED:
         for plain backtracking we check all constraints with V (see csp method
         get_cons_with_var) that are fully assigned.

         for forward checking we forward check all constraints with V
         that have one unassigned variable left

         for gac we initialize the GAC queue with all constraints containing V.
		 
		 
var_ordering == a function with the following template
    var_ordering(csp)
        ==> returns Variable 

    csp is a CSP object---the heuristic can use this to get access to the
    variables and constraints of the problem. The assigned variables can be
    accessed via methods, the values assigned can also be accessed.

    var_ordering returns the next Variable to be assigned, as per the definition
    of the heuristic it implements.
   '''


def prop_BT(csp, newVar=None):
    '''Do plain backtracking propagation. That is, do no 
    propagation at all. Just check fully instantiated constraints'''

    if not newVar:
        return True, []
    for c in csp.get_cons_with_var(newVar):
        if c.get_n_unasgn() == 0:
            vals = []
            vars = c.get_scope()
            for var in vars:
                vals.append(var.get_assigned_value())
            if not c.check(vals):
                return False, []
    return True, []


def prop_FC(csp, newVar=None):
    '''Do forward checking. That is check constraints with
       only one uninstantiated variable. Remember to keep
       track of all pruned variable,value pairs and return '''
    #IMPLEMENT

    #Create a dictionairy for pruned values 
    pruned_values = {}

    #If there is no newVar, make a list of all the constraints in the CSP, otherwise make a list of all constraints with the variable in scope
    if newVar == None:
        cons = list(csp.get_all_cons())  
    else:
        cons = list(csp.get_cons_with_var(newVar))  

    #Iterate and get constraints with only 1 unassigned variable    
    for c in cons:
        if c.get_n_unasgn() == 1:
            
            unassigned_variable = c.get_unasgn_vars()[0] #Get unassigned variable

            #See if any value in the domain of the unassigned variable has a support
            for i in unassigned_variable.cur_domain():
                if c.has_support(unassigned_variable,i) == False:   
                    #If no support, prune the value
                    unassigned_variable.prune_value(i)
                    #Add the variable to the dictornairy if its not there already
                    if unassigned_variable not in pruned_values:
                        pruned_values[unassigned_variable] = [] #Intialize empty list
                    #Add pruned value to the dictionary 
                    pruned_values[unassigned_variable].append((unassigned_variable, i))
            
            #If the domain becomes empty, return domain wipeout
            if unassigned_variable.cur_domain_size() == 0:
                all_prunes = []
                #Add the pruned values to the list of all pruned values
                for i in pruned_values.values():  
                    for j in i:  
                        all_prunes.append(j)  

                return False, all_prunes #Return no support (False), and all the pruned values
        
    all_prunes = []
    #Add the pruned values to the list of all pruned values
    for i in pruned_values.values():  
        for j in i:  
            all_prunes.append(j)  
    return True, all_prunes #Return True and all the pruned values



def prop_GAC(csp, newVar=None):
    '''Do GAC propagation. If newVar is None we do initial GAC enforce 
       processing all constraints. Otherwise we do GAC enforce with
       constraints containing newVar on GAC Queue'''
    #IMPLEMENT

    #Create a dictionairy for pruned values
    pruned_values = {}

    #If there is no newVar, make a queue all the constraints in the CSP, otherwise make a queue of all constraints with the variable in scope
    if newVar == None:
        queue = list(csp.get_all_cons())  
    else:
        queue = list(csp.get_cons_with_var(newVar))  

    #While the queue is not empty
    while len(queue) > 0:
        #Take the first constraint
        constraint = queue.pop(0)

        #For all variables in the contraints scope
        for i in constraint.get_scope(): 
            #For all values in the variables domain        
            for j in i.cur_domain():  
                #Check if a constraint has a support for value i          
                if constraint.has_support(i,j) == False:    
                    #If no support, prune i
                    i.prune_value(j)
                    #Add i,j to the list of pruned values
                    if i not in pruned_values:
                        pruned_values[i] = []
                    pruned_values[i].append((i,j))
                    
                    #If we get a domain wipeout
                    if i.cur_domain_size() == 0:
                        all_prunes = []
                        #Add the pruned values to the list of all pruned values
                        for i in pruned_values.values():  
                            for j in i:  
                                all_prunes.append(j)  
                        return False, all_prunes    #Return no support (False), and all the pruned values
                    
                    #Add all the constraints with variable i in scope back to the queue if it is not in the queue currently
                    for remaining_constraints in csp.get_cons_with_var(i):
                        if remaining_constraints not in queue:
                            queue.append(remaining_constraints)

    all_prunes = []
    #Add the pruned values to the list of all pruned values
    for i in pruned_values.values():  
        for j in i:  
            all_prunes.append(j)  
    return True, all_prunes     #Return True and all the pruned values



def ord_mrv(csp):
    ''' return variable according to the Minimum Remaining Values heuristic '''
    #IMPLEMENT

    #If there is no unassigned variables, return none
    if len(csp.get_all_unasgn_vars()) == 0:
        return None
    
    #Intial min var domain size very large and variable to None
    min_var = None  
    min_var_domain_size = 100000000 

    #Get all the unassinged variables
    for i in csp.get_all_unasgn_vars():
        #Check domain size of unassigned variables
        if i.cur_domain_size() < min_var_domain_size:   
            #if domain size is smaller than current best, replace
            min_var = i
            min_var_domain_size = i.cur_domain_size()
        else:
            continue

    return min_var  #Return the minimum value