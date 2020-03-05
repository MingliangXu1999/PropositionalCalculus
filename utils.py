import re
import numpy as np


def isFormula(string):
    """
    Determine if a string is a formula.
    """
    string = string.replace(' ', '')
    if string == '':
        return True
    elif re.sub(r"\w|\d|->|_|\(|\)|~", '', string):
        return False
    elif re.findall(r"(?<!\w_)\d+|(?<!\w)\d+|->->", string):
        return False
    else:
        string1 = string.replace('~', '').replace('->', '+')
        info = re.findall(r'\w_\d+|\w\d*', string1)
        for part in info:
            string1 = string1.replace(part, '(-1)')
        try:
            eval(string1)
        except:
            return False
        string2 = string.replace('~', '-').replace('->', '+')
        info = re.findall(r'\w_\d+|\w\d*', string2)
        for part in info:
            string2 = string2.replace(part, '(-1)')
        try:
            eval(string2)
        except:
            return False
        return True


def isLeFormula(formula):
    """
    Determine if a formula is a compound formula.
    """
    return '->' in formula


def decompForm(string, flag):
    """
    Break the formula into the smallest subformulas:
    if flag is true, then add non-symbol into subformulas.
    """
    neededString = []
    substring = re.findall(r'\([^()]*\)', string)
    if flag:
        for subs in substring:
            neededString.append('~' + subs)
        neededString = list(set(neededString))
        for i in range(len(substring)):
            substring[i] = substring[i][1:-1]
        neededString.extend(list(set(substring)))
    else:
        for i in range(len(substring)):
            substring[i] = substring[i][1:-1]
        neededString = list(set(substring))
    return neededString


def decompTwo(string):
    """
    Break the formula into two subformulas.
    """
    index = 0
    while True:
        index = string.find('->', index)
        if index > 0:
            if isFormula(string[:index]) and isFormula(string[index + 2:]):
                return [string[:index], string[index + 2:]]
            else:
                index += 2
        else:
            break
    return ['', string]


def genL1(formulaP, formulaQ):
    """
    Build an L1 expression using formulaP and formulaQ:
    p->(q->p)
    return ["p->(q->p)", "p", "q->p", "L1"]
    """
    lis = []
    if isLeFormula(formulaP):
        if isLeFormula(formulaQ):
            lis.append('(' + formulaP + ')->((' + formulaQ + ')->(' + formulaP + '))')
        else:
            lis.append('(' + formulaP + ')->(' + formulaQ + '->(' + formulaP + '))')
    else:
        if isLeFormula(formulaQ):
            lis.append(formulaP + '->((' + formulaQ + ')->' + formulaP + ')')
        else:
            lis.append(formulaP + '->(' + formulaQ + '->' + formulaP + ')')

    lis.append(formulaP)
    if isLeFormula(formulaP):
        if isLeFormula(formulaQ):
            lis.append('(' + formulaQ + ')->(' + formulaP + ')')
        else:
            lis.append(formulaQ + '->(' + formulaP + ')')
    else:
        if isLeFormula(formulaQ):
            lis.append('(' + formulaQ + ')->' + formulaP)
        else:
            lis.append(formulaQ + '->' + formulaP)
    lis.append("L1")
    return lis


def genL2(formulaP, formulaQ, formulaR):
    """
    Build an L2 expression using formulaP, formulaQ and formulaR:
    (p->(q->r))->((p->q)->(p->r))
    return ["(p->(q->r))->((p->q)->(p->r))", "p->(q->r)", "(p->q)->(p->r)", "L2"]
    """
    lisFormula = [formulaP, formulaQ, formulaR]
    for i in range(len(lisFormula)):
        if isLeFormula(lisFormula[i]):
            lisFormula[i] = '(' + lisFormula[i] + ')'
    formulaP = lisFormula[0]
    formulaQ = lisFormula[1]
    formulaR = lisFormula[2]

    lis = []
    lis.append('(' + formulaP + '->(' + formulaQ + '->' + formulaR + '))->((' + \
               formulaP + '->' + formulaQ + ')->(' + formulaP + '->' + formulaR + '))')
    lis.append(formulaP + '->(' + formulaQ + '->' + formulaR + ')')
    lis.append('(' + formulaP + '->' + formulaQ + ')->(' + formulaP + '->' + formulaR + ')')
    lis.append('L2')
    return lis


def genL3(formulaP, formulaQ):
    """
    Build an L2 expression using formulaP and formulaQ:
    (~p->~q)->(q->p)
    return ["(~p->~q)->(q->p)", "~p->~q", "q->p", "L3"]
    """
    lisFormula = [formulaP, formulaQ]
    for i in range(len(lisFormula)):
        if isLeFormula(lisFormula[i]):
            lisFormula[i] = '(' + lisFormula[i] + ')'
    formulaP = lisFormula[0]
    formulaQ = lisFormula[1]

    lis = []
    lis.append('(~' + formulaP + '->~' + formulaQ + ')->(' + formulaQ + '->' + formulaP + ')')
    lis.append('~' + formulaP + '->~' + formulaQ)
    lis.append(formulaQ + '->' + formulaP)
    lis.append("L3")
    return lis


def save2file(lis, path):
    """
    save answer to a specified path.
    """
    np.save(path, np.array(lis))


def searchOrigin(concForm, preSet, formulSet):
    """
    Search answers in formula sets.
    """
    lis = []
    for i in range(len(preSet)):
        if preSet[i] == concForm:
            lis.append(i + 1)
            liss = preSet[i].split()
            liss.append("Assumed")
            lis.append(liss)
            return [1, lis]
    for subset in formulSet:
        if concForm == subset[1][0]:
            lis.append(subset[0])
            lis.append(subset[1])
            return [0, lis]
    return [-1]


def searchFormuSet(index, concForm, formulSet):
    """
    Search answers in formula sets by using MP rules.
    """
    ans = []
    lis = []
    for subset in formulSet:
        if (concForm == subset[1][2]):
            lis.append(index)
            lis.append(subset[1])
            ans.append(lis)
            lis = []
    return ans


def searchMP(string, formulaSet, preSet):
    """
    Search MP rules.
    """
    for lis in formulaSet:
        if lis[1][1]:
            pass
