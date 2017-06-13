#
# Copyright (c) 2016, Christian Schulz-Hanke
#
import clingo
import os

class StateBuilder(object):

    def __init__(self,encoding_s = None,encoding_t = None,encoding_c = None,silent=False,only_positive=False,debug=False, encoding_non_internal=None, encoding_non_internal_transl=None):
        mypath = os.path.dirname(os.path.dirname(os.path.realpath(__file__)))+"/"     
        if encoding_s == None:
            self.encoding_s = mypath+"encodings/internal/states.lp"
        else:
            self.encoding_s = encoding_s
        if encoding_t == None:
            self.encoding_t = mypath+"encodings/internal/transitions.lp"
        else:
            self.encoding_t = encoding_t
        if encoding_c == None:
            self.encoding_c = mypath+"encodings/internal/conflicts.lp"
        else:
            self.encoding_c = encoding_c
        if encoding_non_internal == None:
            self.encoding_non_internal = mypath+"encodings/base.lp"
        else:
            self.encoding_non_internal = encoding_non_internal
        if encoding_non_internal_transl == None:
            self.encoding_non_internal_transl = mypath+"encodings/base_translation.lp"
        else:
            self.encoding_non_internal_transl = encoding_non_internal_transl
        self.states = []
        self.silent = silent
        self.transitions = False
        self.only_positive = only_positive
        self.debug = debug
        
    def set_translator(self,translator):
        self.translator = translator
        
    def translate(self,inpf):
        if not self.translator:
            if not self.silent:
                print "% No translator set"
            return False
        
        return self.translator.translate_file(inpf, return_string=True)
            
    def clean(self,atoms,stid=0,transitions=False):
        result = []
        rest = []
        act = []
        atoms.sort()
        for a in atoms:
            if a.name == 'holds':
                st = a.arguments
                if st[1].number == stid:
                    if st[0].name == 'val':
                        content = st[0].arguments
                        if content[1].type is clingo.SymbolType.Function:
                            if content[1].name == 'false':
                                if not self.only_positive:
                                    result.append('-'+str(content[0]))
                            elif content[1].name == 'true':
                                result.append(str(content[0]))
                            else:
                                result.append(str(content[0])+"="+str(content[1]))
                        else:
                            result.append(str(content[0])+"="+str(content[1]))
                    elif st[0].name == 'neg_val':
                        content = st[0].arguments
                        if content[1].type is clingo.SymbolType.Function:
                            if content[1].name == 'false':
                                result.append(str(content[0]))
                            elif content[1].name == 'true':
                                if not self.only_positive:
                                    result.append('-'+str(content[0]))
                            else:
                                if not self.only_positive:
                                    result.append('-'+str(content[0])+"="+str(content[1]))
                        else:
                            if not self.only_positive:
                                result.append('-'+str(content[0])+"="+str(content[1]))
                    else:
                        if st[0].name == 'act': 
                            st = st[0].arguments
                        act.append(str(st[0]))
                elif transitions and st[1].number == stid+1:
                    if st[0].name == 'val':
                        content = st[0].arguments
                        if content[1].type is clingo.SymbolType.Function:
                            if content[1].name == 'false':
                                if not self.only_positive:
                                    rest.append('-'+str(content[0]))
                            elif content[1].name == 'true':
                                rest.append(str(content[0]))
                            else:
                                rest.append(str(content[0])+"="+str(content[1]))
                        else:
                            rest.append(str(content[0])+"="+str(content[1]))
                    elif st[0].name == 'neg_val':
                        content = st[0].arguments
                        if content[1].type is clingo.SymbolType.Function:
                            if content[1].name == 'false':
                                rest.append(str(content[0]))
                            elif content[1].name == 'true':
                                if not self.only_positive:
                                    rest.append('-'+str(content[0]))
                            else:
                                if not self.only_positive:
                                    rest.append('-'+str(content[0])+"="+str(content[1]))
                        else:
                            if not self.only_positive:
                                rest.append('-'+str(content[0])+"="+str(content[1]))
        if transitions:
            return (result,act,rest)
        return result    
        
    def onmodel(self,model):
        atoms = model.symbols(atoms=True) #.atoms(clingo.Model.ATOMS)
        #optim = model.optimization()
        if self.debug:
            print atoms
        state = self.clean(atoms,transitions=self.transitions)
        self.states.append(state)
        if not self.silent:
            if self.transitions:
                if type(state) == tuple:
                    print "\r\n"
                    print "From State: " + str(state[0]) + "\r\n"
                    print "Action : " + str(state[1]) + "\r\n"
                    print "To State: " + str(state[2]) + "\r\n"
                else:
                    print "ERROR: (State,Transition,State) is no tuple : " + str(state) + "\r\n"
            else:
                print "State: " + str(state) + "\r\n"
                
    def onmodel_conflict(self,model):
        atoms = model.symbols(atoms=True) #.atoms(clingo.Model.ATOMS)
        state = self.clean(atoms,transitions=self.transitions)
        #state = self.clean(atoms,stid=1,transitions=False)
        self.states.append(state)
        if not self.silent:
            if self.transitions:
                if type(state) == tuple:
                    print "\tFrom State: " + str(state[0])
                    print "\tAction : " + str(state[1])
                    print "\tTo State: " + str(state[2])+"\r\n"
        
    
    def get_states(self,inputText):
        result = ""
        self.states = []
        self.transitions = False
        co = clingo.Control(['-W','no-atom-undefined'])
        co.configuration.solve.models = 0
        co.load(self.encoding_s)
        co.add("base", [], inputText)
        co.ground([("base",[])])
        
        if not self.silent:
            print "Solving.."
        
        co.solve(on_model=self.onmodel,assumptions=[])
        
        if self.silent:
            result += "\r\n"
            result += "Possible States: "+str(len(self.states))+"\r\n"
            result += "\r\n"
        if self.silent:
            for st in self.states:
                state = st #self.clean(st)
                result +=  "State: " + str(state) + "\r\n"
        else:
            print "\r\n"
            print "Possible States: "+str(len(self.states))+"\r\n"
    
        return result, self.states
    
    def get_states_transitions(self,inputText):
        result = ""
        self.states = []
        self.transitions = True
        co = clingo.Control(['-W','no-atom-undefined'])
        co.configuration.solve.models = 0
        co.load(self.encoding_s)
        co.load(self.encoding_t)
        co.add("base", [], inputText)
        co.ground([("base",[])])
        
        if not self.silent:
            print "Solving.."
            
        co.solve(on_model=self.onmodel,assumptions=[])
        
        if self.silent:
            result += "\r\n"
            result += "Possible Transitions: " + str(len(self.states)) + "\r\n"
            result += "\r\n"
        
        if self.silent:
            for st in self.states:
                state = st #self.clean(st,transitions=True)
                if type(state) == tuple:
                    result += "\r\n"
                    result += "From State: " + str(state[0]) + "\r\n"
                    result += "Action : " + str(state[1]) + "\r\n"
                    result += "To State: " + str(state[2]) + "\r\n"
                else:
                    result += "ERROR: (State,Transition,State) is no tuple : " + str(state) + "\r\n"
            result += "\r\n"
        else:
            print "\r\n"
            print "Possible Transitions: "+str(len(self.states))+"\r\n"
        
        return result, self.states
    
    def get_states_use_non_internal(self,inputText,reduced=False):
        result = ""
        self.states = []
        self.transitions = False
        co = clingo.Control(['-W','no-atom-undefined'])
        co.conf.solve.models = 0
        if reduced:
            encs = self.encoding_non_internal
        else:
            encs = self.encoding_non_internal_transl
        co.load(encs)
        co.add("base", [], inputText)
        co.ground([("base",[])])
        
        if not self.silent:
            print "Solving.."
        
        co.solve(on_model=self.onmodel,assumptions=[])
        
        if self.silent:
            result += "\r\n"
            result += "Possible States: "+str(len(self.states))+"\r\n"
            result += "\r\n"
            
        if self.silent:
            for st in self.states:
                state = st #self.clean(st)
                result +=  "State: " + str(state) + "\r\n"
        else:
            print "\r\n"
            print "Possible States: "+str(len(self.states))+"\r\n"
    
        return result, self.states
            
    def start(self,inputfile):
        if not self.silent:
            print "Translating"
            text = self.translate(inputfile)
            print "\r\nGetting States"
            print self.get_states(text)
            print "\r\nGetting Transitions"
            print self.get_states_transitions(text)
            print "Finished"
        
    def has_states(self,inputText):
        self.states = []
        self.transitions = False
        co = clingo.Control(['-W','no-atom-undefined'])
        co.load(self.encoding_s)
        co.add("base", [], inputText)
        co.ground([("base",[])])
        result = co.solve()
        return result.satisfiable
        
    def has_conflict(self,inputText):
        self.states = []
        self.transitions = True
        co = clingo.Control(['-W','no-atom-undefined'])
        co.conf.solve.models = 0
        co.load(self.encoding_s)
        co.load(self.encoding_c)
        co.add("base", [], inputText)
        co.ground([("base",[])])
        result = co.solve(on_model=self.onmodel_conflict,assumptions=[])
        return result.unsatisfiable, self.states
