#
# Copyright (c) 2016, Christian Schulz-Hanke
#
import clingo
import os


class SolverFixed(object):

    def __init__(self,encoding = None,debug=False,silent=False,max_horizon=0,only_positive=False):
        mypath = os.path.dirname(os.path.dirname(os.path.realpath(__file__)))+"/"  
        if encoding == None:
            self.encoding = mypath+"coala/internal/fixed.lp"
        else:
            self.encoding = encoding
        self.silent = silent
        self.debug = debug
        self.holds = []
        self.solution = []
        self.transitions = []
        self.optimize = False
        self.max_horizon = max_horizon
        self.control = None
        self.print_negative = not only_positive
        
    def clean(self,atoms):#,stid=0):
        self.holds = []
        result = []
        for a in atoms:
            if a.name == 'holds':
                st = a.arguments
                while st[-1].number >= len(self.holds):
                    self.holds.append([])
                if st[0].name == 'val':
                    content = st[0].arguments
                    if content[1].type is clingo.SymbolType.Function:
                        if content[1].name == 'false':
                            if self.print_negative:
                                self.holds[st[-1].number].append('-'+str(content[0]))
                        elif content[1].name == 'true':
                            self.holds[st[-1].number].append(str(content[0]))
                        else:
                            self.holds[st[-1].number].append(str(content[0])+"="+str(content[1]))
                    else:
                        self.holds[st[-1].number].append(str(content[0])+"="+str(content[1]))
                elif st[0].name == 'neg_val':
                    content = st[0].arguments
                    if content[1].type is clingo.SymbolType.Function:
                        if content[1].name == 'false':
                            self.holds[st[-1].number].append(str(content[0]))
                        elif content[1].name == 'true':
                            if self.print_negative:
                                self.holds[st[-1].number].append('-'+str(content[0]))
                        else:
                            self.holds[st[-1].number].append("-"+str(content[0])+"="+str(content[1]))
                    else:
                        self.holds[st[-1].number].append("-"+str(content[0])+"="+str(content[1]))
                #self.holds[st[-1]].append(str(st[0]))
            elif a.name == 'occurs':
                st = a.arguments
                if st[0].name == 'act': sta = st[0].arguments
                while st[-1].number >= len(result):
                    result.append([])
                result[st[-1].number].append(str(sta[0]))
        return result
        
    def onmodel(self,model):
        atoms = model.symbols(atoms=True) #.atoms(clingo.Model.ATOMS)
        self.solution = atoms
    
    def solve(self,inputText):
        self.solution = []
        self.control = clingo.Control(['-W','no-atom-undefined',"-c","k="+str(self.max_horizon)])
        self.control.configuration.solve.models = 0
        self.control.load(self.encoding)
        self.control.add("base", [], inputText)
        if self.debug:
            print "Grounding.."
        if self.optimize:
            self.control.ground([("base",[]),("initialbase",[]),("utility",[])])
        else:
            self.control.ground([("base",[]),("initialbase",[]),("query",[])])
        
        if self.debug:
            print "Solving.."
        state = self.control.solve(on_model=self.onmodel,assumptions=[])
        if self.debug:
            print "Solving result: ",state
        
        result = self.clean(self.solution)
        if self.debug:
            print "Holds: ",self.holds
    
    
        return result, self.holds, state.satisfiable
