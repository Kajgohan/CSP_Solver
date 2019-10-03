import copy
import sys

def main():
    global counter
    counter = 0
    variableList = {}
    #parsing in the variables
    # Parsing Inputs
    with open(sys.argv[1], 'r') as f:
        content = f.readlines()
    # setting up state machine for file parsing
    # var, domain list
    varDomainList = []
    # parsed constraints list
    biConditional = []
    state = 0
    items = []
    bags = []
    fitlimits = [0, 1000]
    # Fitting Limits
    uninc = []
    unexc = []
    binEQ = []
    binNE = []
    mutin = []

    for line in content:
        # change the state if we hit the next delimiter
        if line.__contains__('#####'):
            state += 1
            continue

        # split the line for storage
        entry = line.split()
        # Items and Weights
        if state == 1:
            items.append([entry[0], int(entry[1])])
        # bags and capacities
        if state == 2:
            bags.append([entry[0], int(entry[1])])
        # Fitting Limits
        if state == 3:
            fitlimits = [int(entry[0]), int(entry[1])]
        # Unary Inclusive
        if state == 4:
            uninc.append(entry)
        # unary exclusive
        if state == 5:
            unexc.append(entry)
        # Binary Equals
        if state == 6:
            binEQ.append(entry)
        # Binary Not Equals
        if state == 7:
            binNE.append(entry)
        # Mutual Inclusive
        if state == 8:
            mutin.append(entry)

    for var in items:

        variable = Variable()
        domain = Domain()
        variable.label = var[0]
        tempDom = []


        #adds all of the possible domains
        for l in bags:
            domain.label = l[0]
            domain.capacity = l[1]
            tempDom.append(l)
        variable.domain = tempDom
        variable.assignment = None
        variable.weight = var[1]

        #This edits the domains of the variables based on the unary conditions
        variable = pruneUnEx(variable, unexc)
        variable = pruneUnIn(variable, uninc)


        variableList[variable.label] = variable

    #fill the constraints
    constraints = []
    for i in binEQ:
        constraints.append((i[0], '=', i[1]))
    for i in binNE:
        constraints.append((i[0], '!', i[1]))
    for i in mutin:
         constraints.append((i[0], '^', i[1], i[2], i[3]))


    # This is to see if we are doing forward checking
    if sys.argv[2] == "none":
        forward_checking = False
    else:
        forward_checking = True


    #ladies and gentelman start your recursion
    solution = recursive_backtracking({}, variableList, constraints, forward_checking, fitlimits, bags)
    if solution is not False:
        print(solution)
        c = 0
        counter += 1
        print(counter, ". ", end="", sep="")
        for u in solution.keys():
            if c is len(solution.keys()) - 1:
                print(u, "=", solution[u], " solution", sep=" ")
            else:
                print(u, "=", solution[u], ", ", end="", sep=" ")
            c += 1


class Variable():
    label = None
    weight = None
    domain = None
    assignment = None

class Domain():
    label = None
    capacity = None
counter = 0

def iff(domain1, domain2, constraints, var1, var2):
    for con in constraints:
        if con[1] == '^':
            if ((con[0] == var1.label) or (con[2] == var1.label)) and ((con[0] == var2.label) or (con[2] == var2.label)):
                if (domain1 == None):
                    return True
                else:
                    if (domain2 == con[3] and domain1 != con[4]):
                        return False
                    elif (domain2 == con[4] and domain1 != con[3]):
                        return False

    return True

#compares the domains of the variables that are specified in the constraints
def operationStation(domain1, domain2, operator, constraints, var1, var2):
    if operator == '=':
        return bool(domain1 == domain2)
    elif operator == '^':
        return iff(domain1, domain2, constraints, var1, var2)
    elif operator == '!':
        return bool(domain1 != domain2)

def recursive_backtracking(assigned, varList, constraints, forward_checking, fitlimits, bags):
    global counter

    #if every variable has an assignment, then you have found a solution
    if all(variable.assignment != None for variable in varList.values()):
        # check to make sure that none of the domains have below the min number of assigned variables
        minLimitCounter = []
        for u in assigned.keys():
            minLimitCounter.append(assigned[u])
        for b in bags:
            check = minLimitCounter.count(b[0])
            if check < fitlimits[0]:
                return False
        return assigned
    #MRV
    var = varPickMRV(varList, constraints)
    #LCV
    domainsToUse = domainSortLCV(varList, constraints, var)

    for vals in domainsToUse:
        val = vals[0]

        #the flag is to see if the movement is legal
        flag = True
        #checks the weight if there are no constraints to trigger the check later on
        overWeight = 0
        for v in varList.keys():
            if varList[v].assignment == val or v == var:
                overWeight += varList[v].weight
        flag = (vals[1] >= overWeight)
        count = 0

        #checks for fitLimit
        for i in assigned.keys():
            if assigned[i] == val:
                count += 1;
        if count >= fitlimits[1]:
            flag = False



        for cons in constraints:
            if cons[0] is varList[var].label:
                if varList[cons[2]].assignment is None:
                    continue
                else:
                    overWeight = 0
                    for v in varList.keys():
                        if varList[v].assignment == val or v == var:
                            overWeight += varList[v].weight
                    # this is where we check for the assignments legality
                    flag = operationStation(val, varList[cons[2]].assignment, cons[1], constraints, varList[var], varList[cons[2]]) and (vals[1] >= overWeight) and (fitlimits[1] >= count)

            elif cons[2] is varList[var].label:
                if varList[cons[0]].assignment is None:
                    continue
                else:
                    overWeight = 0
                    for v in varList.keys():
                        if varList[v].assignment == val or v == var:
                            overWeight += varList[v].weight
                    flag = operationStation(val, varList[cons[0]].assignment, cons[1], constraints, varList[var], varList[cons[0]]) and (vals[1] >= overWeight) and (fitlimits[1] >= count)
            if flag is False:
                c = 0
                counter += 1
                print(counter, ". ", end="", sep="")
                for v in assigned.keys():
                    if c is len(assigned.keys()) - 1:
                        print(v, "=", assigned[v], ", ", end="", sep="")
                        print(varList[var].label, "=", val, " failure", sep="")
                    else:
                        print(v, "=", assigned[v], ", ", end="", sep="")
                    c += 1
                if counter >= 300:
                    SystemExit
                break
        if flag is True:
            varList[var].assignment = val
            assigned[var] = val
            resultVariableList = None
            # forward checking stuff here
            if forward_checking is True:
                # restrict domains based on the new assignment
                resultVariableList = fc(copy.deepcopy(varList), constraints, var)
                for variable in resultVariableList.values():
                    if len(variable.domain) is 0:
                        c = 0
                        counter += 1
                        print(counter, ". ", end="", sep="")
                        for v in assigned.keys():
                            if c is len(assigned.keys()) - 1:
                                # print(v, "=", assigned[v], ", ", end="", sep="")
                                print(varList[var].label, "=", val, " failure", sep="")
                            else:
                                print(v, "=", assigned[v], ", ", end="", sep="")
                            c += 1
                        if counter >= 300:
                            SystemExit
                        continue
            else:
                resultVariableList = varList

            result = recursive_backtracking(assigned, resultVariableList, constraints, forward_checking, fitlimits, bags)
            if result is not False:
                return result
            varList[var].assignment = None
            assigned.pop(var)

    return False


#prunes for the exclusive domains
def pruneUnEx(variable, unex):
    removeList = []
    for e in unex:
        if e[0] == variable.label:
            for i in variable.domain:
                if i[0] in e:
                    removeList.append(i)
    for x in removeList:
        variable.domain.remove(x)
    return variable


#prunes the inclusive domains
def pruneUnIn(variable, uninc):
    removeList = []
    for e in uninc:
        if e[0] == variable.label:
            for i in variable.domain:
                if i[0] not in e:
                    removeList.append(i)
    for x in removeList:
        variable.domain.remove(x)
    return variable

def fc(variableList, constraints, var):
    assignedValue = variableList[var].assignment
    # remove values from other domains that break the rules
    for cons in constraints:
        if cons[0] is variableList[var].label:
            # restrict domain if other var in relationship is not assigned
            if variableList[cons[2]].assignment is None:
                removalList = []
                for value in variableList[cons[2]].domain:
                    if operationStation(assignedValue, value[0], cons[1], constraints, variableList[var], variableList[cons[2]]) is False:
                        removalList.append(value)

                for r in removalList:
                    variableList[cons[2]].domain.remove(r)

        elif cons[2] is variableList[var].label:
            # restrict domain if other var in relationship is not assigned
            if variableList[cons[0]].assignment is None:
                removalList = []
                for value in variableList[cons[0]].domain:
                    if operationStation(assignedValue, value[0], cons[1], constraints, variableList[var], variableList[cons[2]]) is False:
                        removalList.append(value)
                for r in removalList:
                    variableList[cons[0]].domain.remove(r)

    return variableList


def varPickMRV(variables, constraints):
    var = None
    varList = []
    for v in variables.keys():
        # if variable has no assignment
        if variables[v].assignment == None:
            # if no variable currently being checked just take the first one
            if var == None:
                var = v
                varList.append(v)
            # Check to see the one with the biggest domain, and add it to the list first
            elif len(variables[var].domain) > len(variables[v].domain):
                var = v
                varList = [v]
            # otherwise if domains are the same size, tiebreak
            elif len(variables[var].domain) == len(variables[v].domain):
                constraintNum = 0
                variablecount = 0
                constraintNum += sum(1 for i in constraints if i[0] == variables[var].label and variables[i[2]].assignment == None)
                constraintNum += sum(1 for i in constraints if variables[i[0]].assignment == None and i[2] == variables[var].label)
                variablecount += sum(1 for i in constraints if i[0] == variables[v].label and variables[i[2]].assignment == None)
                variablecount += sum(1 for i in constraints if variables[i[0]].assignment == None and i[2] == variables[v].label)
                # rate the variable with the most constraints the highest
                if constraintNum < variablecount:
                    var = v
                    varList = [v]
                elif constraintNum == variablecount:
                    varList.append(v)
    return var


def domainSortLCV(variableList, constraints, var):
    # array for constraints
    conVals = {}
    for vall in variableList[var].domain:
        val = vall[0]
        tempValue = 0
        for cons in constraints:
            if cons[0] is variableList[var].label and variableList[cons[2]].assignment is None:
                for compValue in variableList[cons[2]].domain:
                    if not operationStation(val, compValue[0], cons[1], constraints, variableList[var], variableList[cons[2]]):
                        tempValue += 1
            elif variableList[cons[0]].assignment is None and cons[2] == variableList[var].label:
                for compValue in variableList[cons[0]].domain:
                    if not operationStation(compValue[0], val, cons[1], constraints, variableList[var], variableList[cons[2]]):
                        tempValue += 1
        if tempValue in conVals:
            conVals[tempValue].append(vall)
        else:
            conVals[tempValue] = [vall]
    orderedDomain = []
    for s in sorted(conVals.keys()):
        for i in conVals[s]:
            orderedDomain.append(i)
    return orderedDomain


if __name__ == "__main__":
    main()
