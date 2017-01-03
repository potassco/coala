% In order to call this, you should use the incremental.lp encoding:
% coala examples/monkey/monkey.bc examples/monkey/monkey_instance.bc | clingo - encodings/incremental.lp -c imin=10 -c imax=15 | outputformatclingocoala
#script (python) 

import clingo

global print_negative
global initially
global translate
global atoms

print_negative = False
initially = True
translate = True
atoms = None

def onmodel(model):
    global atoms
    global currentmodels
    atoms = model.symbols(atoms=True)
    currentmodels += 1
    if atoms is not None:
        occurs, holds = clean(atoms)
        printplan(occurs, holds, currentmodels)

def clean(atoms):
    global print_negative
    holds = []
    occurs = []
    for a in atoms:
        if a.name == 'holds':
            st = a.arguments
            while st[-1].number >= len(holds):
                holds.append([])
            if st[0].name == 'val':
                content = st[0].arguments
                if type(content[1]) is clingo.Symbol:
                    if content[1].name == 'false':
                        if print_negative:
                            holds[st[-1].number].append('-'+str(content[0]))
                    elif content[1].name == 'true':
                        holds[st[-1].number].append(str(content[0]))
                    else:
                        holds[st[-1].number].append(str(content[0])+"="+str(content[1]))
                else:
                    holds[st[-1].number].append(str(content[0])+"="+str(content[1]))
        elif a.name == 'occurs':
            st = a.arguments
            if len(st) > 0 and st[0].name == 'act': 
                actt = st[0].arguments
            while st[-1].number >= len(occurs):
                occurs.append([])
            occurs[st[-1].number].append(str(actt[0]))
    return occurs, holds

def printplan(occurs, holds, currentmodels):
    keys = range(max(len(holds),len(occurs)))
    if len(keys) > 0:
        print ""
        print "Plan "+str(currentmodels)+" :"
        for x in keys:
            holds[x].sort()
            print "Step "+str(x)+":\t\t"+", ".join(holds[x])
            if len(occurs) > x: 
                occurs[x].sort()
                print "Action:\t\t"+", ".join(occurs[x])
        print ""

def main(prg):
    global initially
    global translate
    global atoms
    global currentmodels
    modelcount = int(prg.configuration.solve.models)
    imin   = prg.get_const("imin")
    imax   = prg.get_const("imax")
    if imin is None: imin = -1
    else: imin = imin.number
    if imax is None: imax = 50
    else: imax = imax.number

    currentmodels = 0
    step = 0
    while (imax < 0 or step < imax) and \
           (modelcount == 0 or currentmodels == 0 or modelcount > currentmodels or step < imin):
        parts = []
        if step > 0:
            print "Adding Transition to step "+str(step)
            prg.release_external(clingo.Function("query", [step-1]))
            parts.append(("transition", [step]))
            parts.append(("query", [step]))
            prg.cleanup()
        else:
            parts.append(("base", []))
            if translate:
                parts.append(("translation", []))
            parts.append(("query", [0]))
            if initially:
                parts.append(("initially", []))
        prg.ground(parts)
        prg.assign_external(clingo.Function("query", [step]), True)
        ret = prg.solve(onmodel)
        step += 1
        prg.configuration.solve.models = modelcount - currentmodels
#end.

#include "incremental.lp".
