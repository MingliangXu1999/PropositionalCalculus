#!/usr/bin/python3

from utils import *


class InputError(IOError):
    pass


class proCal(object):
    """
    Define a propositional calculus class.
    """

    def __init__(self):
        self.initInput = []
        self.preSet = []
        self.preSetLen = 0
        self.concForm = []
        self.elements = []
        self.formulBaseSet = []
        self.formulSet = []
        self.depth = 2
        self.LMPDevidLine = 0
        self.ans = []

    def getInit(self):
        # print("Using LATEX grammar")
        # inputString = input("Such as \"\\vdash p\\rightarrow q\" means \"|-p->q\"")
        inputString = input("Input the T|-p:such as \"|-p->~p\"\n\n").strip(' ')
        try:
            if inputString.count("|-") != 1:
                raise InputError("Please input right T|-p /too many \"|-\"")
            else:
                prereqSet = inputString.split("|-")
                if not prereqSet[1].strip():
                    raise InputError("Please input right T|-p /nothing to proof")
                elif isFormula(prereqSet[1]) is True:
                    if prereqSet[0].startswith('{') and prereqSet[0].endswith('}'):
                        prereqSet[0] = prereqSet[0][1:-1]
                        if prereqSet[0].strip():
                            if all(isFormula(lis) for lis in prereqSet[0].split(',')):
                                self.initInput.append(inputString)
                            else:
                                raise InputError("Please input right T|-p /formula syntax error 001")
                    elif prereqSet[0].strip():
                        if isFormula(prereqSet[0]):
                            self.initInput.append(inputString)
                        else:
                            raise InputError("Please input right T|-p /formula syntax error 002")
                    else:
                        self.initInput.append(inputString)
                else:
                    raise InputError("Please input right T|-p / formula syntax error 003")
        except InputError as exception:
            print(exception)
            self.getInit()

        formuList = self.initInput[0].split('|-')
        if formuList[0].startswith('{') and formuList[0].endswith('}'):
            formuList[0] = formuList[0][1:-1]
            self.preSet = formuList[0].split(',')
        else:
            self.preSet = formuList[0].split(',')
        self.preSet = [x for x in self.preSet if x]
        self.preSetLen = len(self.preSet)
        self.concForm = formuList[1].split()
        self.getElements()
        self.getFormuSet()

    def getElements(self):
        string = []
        for lis in self.preSet + self.concForm:
            string += re.findall(r'~*\w_\d+|~*\w\d*', lis)
        self.elements = list(set(string))
        # for i in range(len(self.elements)):
        #     self.formulBaseSet.append('~'+self.elements[i])
        self.formulBaseSet.extend(self.elements)
        for lis in self.preSet + self.concForm:
            self.formulBaseSet.extend(decompForm(lis, False))

    def getFormuSet(self):
        depth = self.depth
        index = self.preSetLen + 1
        for p in self.formulBaseSet:
            for q in self.formulBaseSet:
                self.formulSet.append([index, genL1(p, q)])
                index += 1
                self.formulSet.append([index, genL3(p, q)])
                index += 1
        for p in self.formulBaseSet:
            for q in self.formulBaseSet:
                for r in self.formulBaseSet:
                    self.formulSet.append([index, genL2(p, q, r)])
                    index += 1
        depth -= 1
        while depth > 0:
            formulaBaseSet = self.formulBaseSet
            for i in range(len(self.formulSet)):
                formulaBaseSet.append(self.formulSet[i][1][0])
            self.formulSet = []
            index = self.preSetLen + 1
            for p in formulaBaseSet:
                for q in formulaBaseSet:
                    self.formulSet.append([index, genL1(p, q)])
                    index += 1
                    self.formulSet.append([index, genL3(p, q)])
                    index += 1
            for p in formulaBaseSet:
                for q in formulaBaseSet:
                    for r in formulaBaseSet:
                        self.formulSet.append([index, genL2(p, q, r)])
                        index += 1
            depth -= 1
        self.LMPDevidLine = index
        formulaSet = self.formulSet
        for lis in formulaSet:
            kind = searchOrigin(lis[1][1], self.preSet, formulaSet)
            if kind[0] != -1:
                liss = []
                liss.append(lis[1][2])
                for li in decompTwo(lis[1][2]):
                    liss.append(li)
                liss.append(kind[1][0])
                liss.append(lis[0])
                liss.append('MP')
                self.formulSet.append([index, liss])
                index += 1
            else:
                pass

    def searchAns(self):
        stack = []
        delstack = []
        for i in range(self.LMPDevidLine - self.preSetLen - 1, len(self.formulSet)):
            if self.formulSet[i][1][0] == self.concForm[0]:
                if self.formulSet[i][1][-2] - 1 - self.preSetLen >= 0:
                    stack.append(self.formulSet[i][1][-2] - 1 - self.preSetLen)
                    self.ans.append(self.formulSet[self.formulSet[i][1][-2] - 1 - self.preSetLen])
                else:
                    pass
                if self.formulSet[i][1][-3] - 1 - self.preSetLen >= 0:
                    stack.append(self.formulSet[i][1][-3] - 1 - self.preSetLen)
                    self.ans.append(self.formulSet[self.formulSet[i][1][-3] - 1 - self.preSetLen])
                else:
                    pass
                self.ans.append(self.formulSet[i])
                break

        while len(stack) > 0:
            lis = stack
            for i in range(len(stack)):
                if self.formulSet[int(stack[i])][1][-1] != 'MP':
                    delstack.append(stack[i])
                    stack[i] = float("inf")
                else:
                    if self.formulSet[int(stack[i])][1][-2] >= 1 + self.preSetLen:
                        stack.append(self.formulSet[int(stack[i])][1][-2] - 1 - self.preSetLen)
                        self.ans.append(self.formulSet[self.formulSet[int(stack[i])][1][-2] - 1 - self.preSetLen])
                    else:
                        pass
                    if self.formulSet[int(stack[i])][1][-3] >= 1 + self.preSetLen:
                        stack.append(self.formulSet[int(stack[i])][1][-3] - 1 - self.preSetLen)
                        self.ans.append(self.formulSet[self.formulSet[int(stack[i])][1][-3] - 1 - self.preSetLen])
                    else:
                        pass
                    self.ans.append(self.formulSet[int(stack[i])])
            while float("inf") in stack:
                stack.remove(float("inf"))
            for i in range(len(stack)):
                if self.formulSet[int(stack[i])][1][-1] != 'MP':
                    delstack.append(stack[i])
                    stack[i] = float("inf")
            while float("inf") in stack:
                stack.remove(float("inf"))
            delstack = list(set(delstack))
            for i in range(len(stack)):
                if stack[i] in delstack:
                    stack.remove(stack[i])
            if lis == stack:
                break
        self.ans
        ans = []
        for id in self.ans:
            if id not in ans:
                ans.append(id)
        for id in ans:
            id[1].pop(1)
            id[1].pop(1)
        self.ans = ans
        print(self.ans)

    def printf(self):
        print("Init_input: " + str(self.initInput))
        print("Elements: " + str(self.elements))
        print("Prerequisite set: " + str(self.preSet))
        print("Conclusion to prove: " + str(self.concForm))
        print("Base formula set: " + str(self.formulBaseSet))
        print("Final formula set: " + str(self.formulSet))
        print("Answer: " + str(self.ans))


if __name__ == "__main__":
    cal = proCal()
    cal.getInit()
    cal.searchAns()
