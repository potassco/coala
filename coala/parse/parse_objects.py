#
# Copyright (c) 2016, Christian Schulz-Hanke
#
from __builtin__ import str
import copy
import inspect
import sys


old_arithmetics = False
additional_ifcons_facts = False
clingo_arithmetics = False

#
# The following classes are used to represent the parse tree.
# parse_object is the parent class of all objects except for strings.
# - In order to traverse the tree, you get children nodes by calling get_children()
# - If you want to add Information to the update function,
#        you can include it into the "update" object of the update_passdown class
# 
# The parse process currently works as follows (aspCompiler.py):
# 1. Parse Text to Objects using lex/ply (parser.py) 
# 2. Collect data from the objects (actions, fluents, integers)
# 3. Update the tree (pass down where fluents, actions etc. are; pass up where variables are)
# 4. Simplify the tree (some laws can be reduced if there is no information; This is needed for arithmetic laws)
#    - This works as a reconstruction of the tree
# 5. Generate ASP code (this uses the print_facts() function)
#
# All classes here have "parse_object" as parent,
# All laws additionally have "law" as parent
#
# There is a update function in parse_object that changes how objects will be printed.

class parse_object(object):
    
    def __init__(self):
        self.variables = []
        self.child_attributes = []
        self.reference = None
        self.negation = False
        self.binding = None
    
    # Get all children of the object (used for inheriting classes)
    def get_children(self):
        result = []
        for att in self.child_attributes:
            if hasattr(self,att):
                val = getattr(self,att)
                if val is not None and type(val) != str:
                    result.append(val)
        return result
    
    # Get all children of the object (returns result in form of a dictionary)
    def get_children_dict(self):
        result = {}
        #for att in ["head","body","if_part","ifcons_part","after_part","content","left","right"]:
        for att in self.child_attributes:
            if hasattr(self,att):
                val = getattr(self,att)
                if val is not None and type(val) != str:
                    result[att]=val
        return result
    
    # Get only the leafs of the tree. 
    # This would be empty if not overwritten by classes: Variable, Predicate, Action, Fluent, .. 
    def get_bottom_elements(self):
        result = []
        ch = self.get_children()
        for c in ch:
            if type(c) == str: continue
            result += c.get_bottom_elements()
        return result
    
    # Returns a where part if there is one for the current object
    # (Laws are located on top of the tree, so traversing doesn't make sense)
    def get_where(self):
        if hasattr(self, "where"):
            return self.where
        return None  

    # If there is a line/filename for this object, it is returned as a dictionary.
    def get_meta(self):
        result = {'file':None, 'line':None}
        if hasattr(self, "line"): result['line'] = self.line
        if hasattr(self, "filename"): result['file'] = self.filename
        return result
    
    # Gets variables from the leafs of the tree
    # Is overwritten by classes: Variable
    def get_variables(self,checkbound=False):
        my_vars = []
        ch = self.get_children()
        for c in ch:
            if c is None or type(c) == str: continue
            vs = c.get_variables(checkbound)
            if type(vs) == list:
                my_vars += vs
            else:
                my_vars.append(vs) 
        return my_vars
    
    
    def get_explicitly_bound_variables(self,where=False,bound=False):
        my_vars = []
        if not where:
            if hasattr(self, "where"):
                wh = self.where
                if wh is not None:
                    va = wh.get_explicitly_bound_variables(True,bound)
                    if len(va)>0:
                        return va
        else:     
            ch = self.get_children()
            for c in ch:
                if c is None or type(c) == str: continue
                vs = c.get_explicitly_bound_variables(where,bound)
                if type(vs) == list:
                    my_vars += vs
                else:
                    my_vars.append(vs) 
        return my_vars
    
    # Extracts domains for fluents.
    # Is overwritten by classes: Fluent, Predicate
    def get_fluents_domains(self,simple=True):
        #print  >> sys.stderr, "% Warning!, not implemented get_fluents_domains for", self.__class__ 
        result = []
        ch = self.get_children()
        wh = self.get_where()
        for x in ch:
            do = x.get_fluents_domains()
            if wh is not None:
                for d in do:
                    d.where = wh
                    result.append(d)
            else:
                result += do 
        return result
    
    def get_actions(self):
        return []
    
    def search_and_return(self,criteria):
        result = []
        ch = self.get_children()
        check = criteria(self)
        if check is not None:
            return check
        for x in ch:
            if type(x) == str:
                continue
            res = x.search_and_return(criteria)
            if type(res) == list:
                result += res
            else:
                result.append(res) 
        return result
    
    def search_and_return_path(self,criteria):
        result = []
        check = criteria(self)
        if check is not None:
            return [[check,[(self,""),]],]
        ch = self.get_children_dict()
        for att in ch:
            ix = ch[att]
            if type(ix) != list:
                ix = [ix,]
            for x in ix:
                if type(x) == str:
                    continue
                res = x.search_and_return_path(criteria)
                if type(res) == list:
                    for r in res:
                        if len(r) == 2:
                            r[1].insert(0,(self,att))
                        result.append(r)
                    #result += res
                else:
                    # error!
                    res[1].insert(0,(self,att))
                    result.append(res)
        return result
    
    # Prints the tree as ASP text.
    # This is used as the final translation.
    # Every class should overwrite this.
    def print_facts(self,prime=False):
        print  >> sys.stderr, "ERROR, not implemented print_facts for", self.__class__ 
        errout.error("ERROR, not implemented print_facts for"+str(self.__class__ ))
        return str(self)
    
    # If this is a law with a "where" part, we create a string out of it
    def compile_where(self):
        if not hasattr(self, "where"):
            return ""
        val = self.where
        if val is None:
            return ""
        else:
            va = val.compile_where_single()
            if va is None: return ""
            return " :- "+va
    
    # Get the context so that we can integrate it somewhere.
    # Every class should overwrite this.
    def compile_where_single(self):
        print  >> sys.stderr, "%ERROR, not implemented compile_where_single for", self.__class__
        errout.error("%ERROR, not implemented compile_where_single for"+str(self.__class__))
        return self.print_facts()
    
    # If arithmetics are moved to the where part,
    # this checks and returns variables of the where part of marked arithmetics
#     def mark_check_body(self):
#         result = []
#         ch = self.get_children()
#         for c in ch:
#             if c is None or type(c) == str: continue
#             res = c.mark_check()
#             if res is None: continue
#             if type(res) == list: result += res
#             else: result.append(res) 
#         if len(result) > 0: return result
#         else: return None
    
    # Top-level Update function.
    # Initiates the pass_down update.
    def update(self,actions=None,fluents=None,integers=None,integer_ids=None,idfunction=None,arith_idfunction=None,check=True,others=None,arith_helper_idfunction=None,law_type=None):
        my_others = {"idfunction":idfunction,"arith_idfunction":arith_idfunction,"arith_helper_idfunction":arith_helper_idfunction,"check":check}
        if others is not None:
            for o in others:
                my_others[o] = others[o]
        update = update_passdown(law=self,fluents=fluents,actions=actions,integers=integers,integer_ids=integer_ids,others=my_others,law_type=law_type)
        self.pass_down_update(update)
        if len(update.unbound_assignment) > 0:
            #print update.unbound_assignment
            self.replace_unbound_variables(update.unbound_assignment)
        return update
    
    # A function where classes can stick their additional
    # update code without copying the entire function
    def pass_down_update_overwrite(self,update):
        pass
    
    # The general pass_down function for the update.
    # Note that there is an empty function for other classes to overwrite
    # and there are some classes that wil overwrite this one as well
    def pass_down_update(self,update):
        wh = self.get_where()
        ch = self.get_children_dict()
        
        
        def subcrit(self,update): # Find int fluents in equations
            if type(self) in [fluent,unknown,predicate]:
                for inte in update.integer_ids:
                    if self.compare_to(inte):
                        return self
        def criteria(self,variab,update): # Find variable and get int flu
            if type(self) == equation: 
                my_vars = self.get_variables()
                for mvar in my_vars:
                    if str(mvar) == str(variab):
                        match = self.search_and_return(lambda x: subcrit(x,update))
                        if match is not None and type(match) == list and len(match)>0:
                            if len(match) == 1:
                                return (match[0],variab,self)
                            else:
                                return (match,variab,self)
        
        if wh is not None:
#             # First: Find backwards declared integer fluent Variables
#             def subcrit(self,update): # Find int fluents in equations
#                 if type(self) in [fluent,unknown,predicate]:
#                     for inte in update.integer_ids:
#                         if self.compare_to(inte):
#                             return self
#             def criteria(self,variab,update): # Find variable and get int flu
#                 if type(self) == equation: 
#                     my_vars = self.get_variables()
#                     for mvar in my_vars:
#                         if str(mvar) == str(variab):
#                             match = self.search_and_return(lambda x: subcrit(x,update))
#                             if match is not None:
#                                 if len(match) == 1:
#                                     return (match[0],variab,self)
#                                 else:
#                                     return (match,variab,self)
#             pre_vars = wh.get_variables()
#             #pre_vars_bound = wh.get_variables(checkbound=True)
#             for v in pre_vars: 
#                 #match = self.search_and_return(lambda x: criteria(x,v,update))
#                 match = self.search_and_return_path(lambda x: criteria(x,v,update))
#                 if match is not None:
#                     update.add_indirectly_bound_integer_variable(match)
#             # Now, update.get_int_for_indirectly_bound_variable can check if a variable is indir. bound to int
                    
            # Get Variables of Body and bound where
            body_vars = self.get_variables()
            where_vars = [str(x) for x in wh.get_variables(checkbound=True)]
            # Remove duplicates?
            
            # Check if bound in where
            unbound = []
            str_unbound = []
            for v in body_vars:
                if str(v) not in where_vars and str(v) not in str_unbound:
                    unbound.append(v)
                    str_unbound.append(str(v))
                    
            for v in unbound:
                match = self.search_and_return_path(lambda x: criteria(x,v,update))
                if match is not None:
                    update.add_indirectly_bound_integer_variable(match)
                    
            update.where_start(wh)
            update.path_inc(self,"where")
            update.where_variables = wh.pass_down_update(update)
            update.path_dec()
            #update.where_variables = [str(x) for x in wh.get_variables(True)] 
            #wh_vars = wh.pass_down_update(update) # Ignoring Return Variables!
            #if wh_vars != update.where_variables:
            #    print "unequal"
            update.where_end()    
        else:
            # No where means all variables are unbound
            
            body_vars = self.get_variables()
            unbound_vars = []
            str_unbound = []
            for v in body_vars: # Removes duplicates
                if str(v) not in str_unbound:
                    unbound_vars.append(v)
                    str_unbound.append(str(v))
            
#             def subcrit(self,update): # Find int fluents in equations
#                 if type(self) in [fluent,unknown,predicate]:
#                     for inte in update.integer_ids:
#                         #if self.compare_to(inte):
#                         if str(self) == str(inte):
#                             return self
#             def criteria(self,variab,update): # Find variable and get int flu
#                 if type(self) == equation: 
#                     my_vars = self.get_variables()
#                     for mvar in my_vars:
#                         if str(mvar) == str(variab):
#                             match = self.search_and_return(lambda x: subcrit(x,update))
#                             if match is not None and type(match) == list and len(match)>0:
#                                 if len(match) == 1:
#                                     return (match[0],variab,self)
#                                 else:
#                                     return (match,variab,self)
            for v in unbound_vars:
                match = self.search_and_return_path(lambda x: criteria(x,v,update))
                if match is not None:
                    update.add_indirectly_bound_integer_variable(match)
                
            pass            
                    
        for kc in ch:
            c = ch[kc]
            update.path_inc(self,kc)
            variables = c.pass_down_update(update)
            update.path_dec()
            for v in variables:
                if not v in self.variables:
                    self.variables.append(v)
        #ch = self.get_children()
        #for c in ch:
        #    variables = c.pass_down_update(update)
        #    for v in variables:
        #        if not v in self.variables:
        #            self.variables.append(v)
        self.pass_down_update_overwrite(update)
        return self.variables 
    
    # After updating, some things might get simpified.
    # Normaly, an object returns itself.
    # In order to replace oneself in the tree, a class might return the replacement for itself instead.
    def simplify(self,negation=False,in_where=False):
        if negation:
            self.negation = not self.negation
            negation = False
        #,"where"]: #################################ADD THIS
        for att in ["head","body","if_part","ifcons_part","after_part","content","left","right","where"]: #################################ADD THIS
        #,"where"]: #################################ADD THIS
        #,"where"]: #################################ADD THIS
        #,"where"]: #################################ADD THIS
        # Verschluckt aktuell "not" im where part!
        # plan(X)=Y macht aus X einen integer!!!
        #,"where"]: #################################ADD THIS
        #,"where"]: #################################ADD THIS
        #,"where"]: #################################ADD THIS
            if hasattr(self,att):
                val = getattr(self,att)
                if val is not None:
                    if type(val) == false_atom:
                        return None
                    if type(val) != str:
                        my_in_where = in_where or att == "where"
                        if type(val) == list:
                            nval = [] 
                            for v in val:
                                if type(v) == str: nval.append(v)
                                else:
                                    if v.is_false(): return None 
                                    simp = v.simplify(negation,my_in_where)
                                    if simp is not None: 
                                        if type(simp) == list: nval += simp
                                        else: nval.append(simp)
                        else:
                            nval = val.simplify(negation,my_in_where)
                        setattr(self,att,nval)
        return self
    
    def replace_unbound_variables(self,assignm,negate=False):
        for att in self.child_attributes:
            #neg = negate
            #if att == "after": neg = not neg
            if hasattr(self,att):
                val = getattr(self,att)
                if type(val) == list:
                    li = []
                    for x in val:
                        li.append(x.replace_unbound_variables(assignm,negate))#neg))
                    setattr(self, att, li)
                elif val is not None and type(val) != str:
                    setattr(self, att, val.replace_unbound_variables(assignm,negate))#neg))
        return self
        
    
    # General method to compare two parsed objects.
    # This only gets complicated if there are Variables in the Code.
    def compare_to(self,other,parent=True,accept_variables=True):
        #print >> sys.stderr, "compare: ",self,"("+self.__class__.__name__+"), ",other,"("+other.__class__.__name__+")"
        if self == other: return True
        if accept_variables and (other.__class__ == variable or self.__class__ == variable): return True
        if self.__class__ != other.__class__:
            return False
        c1 = self.get_children()
        c2 = other.get_children()
        if len(c1) != len(c2):
            return False
        if len(c1) < 1:
            str_self = self.print_facts() #str(self)
            str_other = other.print_facts() #str(other)
            return (accept_variables and (str_self.isupper() or str_other.isupper())) or str_self == str_other 
        for i in range(len(c1)):
            if type(c1[i]) == str:
                if type(c2[i]) == str: ot = c2[i]
                else: ot = c2[i].print_facts() #str(c2[i])
                return c1[i].isupper() or ot.isupper() or c1[i] == ot
            if not c1[i].compare_to(c2[i],parent=False,accept_variables=accept_variables):
                return False
        return True

    # There is a false object.
    # This replaces the object.__class__ == falseobjectclass call and is nicer to read
    def is_false(self):
        return False

# It's a list that is also a parse_object.
class atom_list(parse_object):
    def __init__(self, *content):
        parse_object.__init__(self)
        if content is not None:
            li = []
            for el in content:
                if type(el) == list: li += el
                else: li.append(el)
            self.content = li 
        else:
            self.content = None
        self.child_attributes = ["content"]
#         self.content = None
#         if len(content) > 0:
#             self.content = list(content)
    
    def get_children(self):
        if self.content is None: return []
        return self.content
        
    def combine(self,other_list,reverse=False):
        if self.content is None:
            return
        if other_list.__class__ == atom_list:# hasattr(other_list,"content"):
            if other_list.content is None:
                self.content = None
            else:
                if reverse:
                    self.content = other_list.content + self.content
                else:
                    self.content += other_list.content
        else:
            if reverse:
                self.content = [other_list,]+self.content
            else:
                self.content.append(other_list)
            
    def append(self,other_element):
        if self.content is None:
            return
        else:
            self.content.append(other_element)
    
    def __len__(self):
        if self.content is None:
            return 0
        return len(self.content)
    
    def __iter__(self):
        return iter(self.content)
    
    def __str__(self):
        if self.content is None: return ""
        return ','.join( str(x) for x in self.content)
    
    def typestr(self):
        if self.content is None: return "[]"
        return ','.join( x.typestr() if type(x) != str else x for x in self.content)
        #return ', '.join( x.typestr() if type(x) != str else "str" for x in self.content)
    
#     def get_fluents(self,simple=True):
#         result = []
#         for x in self.content:
#             res = x.get_fluents(simple)
#             if type(res) == list: result += res
#             else: result.append(res)
#         return result
    
    def get_actions(self):
        result = []
        if self.content is None: return result
        for x in self.content:
            res = x.get_actions()
            if type(res) == list: result += res
            else: result.append(res)
        return result
    
#     def mark_check_where(self):
#         result = []
#         if self.content is None: return
#         for c in self.content:
#             res = c.mark_check_where()
#             if res is not None:
#                 result.append(res) 
#         if len(result) == 0: return None
#         else: return result
#         #return parse_object.mark_check(self)
#     
#     def mark_check_body(self,marks,head=False,ifcons=False):
#         result = []
#         if self.content is None: return
#         for c in self.content:
#             res = c.mark_check_body(marks,head=head,ifcons=ifcons)
#             if res is not None:
#                 result.append(res) 
#         if len(result) == 0: return None
#         else: return result
#         #return parse_object.mark_check(self)
    
    def pass_down_update(self,update):
        if self.content is None: return self.variables
        for c in self.content:
            if type(c) == str: continue
            update.path_inc(self,"content")
            variables = c.pass_down_update(update)
            update.path_dec()
            for v in variables:
                if not v in self.variables:
                    self.variables.append(v)
        return self.variables
    
    
#     def simplify(self,negation=False,in_where=False):
#         if negation:
#             self.negation = not self.negation
#             negation = False
#         if self.content is None:
#             return None
#         else:
#             new_content = []
#             for v in self.content:
#                 if type(v) == str: new_content.append(v)
#                 elif v is not None:
#                     if v.is_false(): return None 
#                     simp = v.simplify(negation,in_where)
#                     if simp is not None: new_content.append(simp)
#                 self.content = new_content
#         if len(self.content) == 0:
#             return None
#         return self
    
    def compile_where_single(self):
        if self.content is None: return ""
        comb = []
        for c in self.content:
            if type(c) != str:
                compiled = c.compile_where_single()
                if compiled is not None: comb.append(compiled)
        if len(comb) < 1: return None
        return ",".join(comb)
    
    def replace_unbound_variables(self,assignm,negate=False):
        for i in range(len(self.content)):
            self.content[i] = self.content[i].replace_unbound_variables(assignm,negate)
        return self
    
class value_range(parse_object):
    def __init__(self,lower,upper):
        self.lower = lower
        self.upper = upper
        try:
            lo = int(str(self.lower))
            up = int(str(self.upper))
            self.content = range(lo,up+1)
        except:
            self.content = [self.lower,self.upper]
        
    def __iter__(self):
        return iter(self.content)
        
class rule(parse_object):
    pass

# Each law has it's own ID.
class law(rule):
    def __init__(self):
        parse_object.__init__(self)
        self.law_type = None
        self.other_conditions = {}
        
    def add_part(self,part,law_position):
        print  >> sys.stderr, "ERROR, not implemented add_part for", self.__class__ 
        errout.error("ERROR, not implemented add_part for"+str(self.__class__ ))
    
    # This checks for unbound variables and
    # adds their domain statements to the where part.
    # TODO : If there are integer vars, there should be a difference!
    def pass_down_update_overwrite(self, update):
        self.law_id = update.idfunction()
        
        #Creating arithmetic laws in the body; output: (caller,replaced_law,replacement,law_part)
        for (_,_,replacement,law_part) in update.where_arithmetic:
            if law_part in self.other_conditions:
                self.other_conditions[law_part].append(replacement)
            else:
                self.other_conditions[law_part] = atom_list(replacement)
        
        #Checking for variables in the body that are not bound and putting them into the where part
        def criteria(self): 
            if type(self) == equation: 
                my_vars = self.get_variables()
                if len(my_vars) > 0:
                    return (self,my_vars)
        
        var = self.search_and_return_path(criteria)
        
        if update.where_variables is None:
            update.where_variables = atom_list()
        
        # Check variables in equations, whether we need to add implied laws
        var_occ = {}
        var_equ = {}
        keys = []

        # Add domain statements for variables representing fluents            
        for ((equ,_),my_path) in var:
                
            variable_is_placeholder = False
                
            if not hasattr(self, "where") or self.where is None:
                self.where = atom_list()
            if type(self.where) == atom_list:
                if type(equ)==equation: # and type(equ.left) in [variable,unknown,predicate,str]:
                    
                    # equation "X op Y"
                    # - Find out if we have to use integers:
                    # - - Mark all integer fluents, noninteger fluents, variables and values
                    # - - replace unbound variables
                    # - Otherwise add a domain statement to where-part (op ?)
                    
                    equ_position = None
                    for (_,x) in my_path:
                        if x in ["head","if_part","ifcons_part","after_part"]:
                            equ_position = x
                            break
                        
                    
                                
                    # Equations "a = X" than can be used to replace "X" in other equations.
                    if equ.operator in ["=","=="] and type(equ.left) in [variable,unknown,predicate,str] \
                        and type(equ.right) in [variable,unknown,predicate,str] \
                        and equ_position != "head": # Not operation
                        variable_is_placeholder = True
                    
                    if equ.operator in ["=","=="]: 
                        
                        if equ.right == "<true>": #in ["<true>","true"] :
                            self.where.append( fluent(equ.left,True) )
                            continue 
                        if equ.right == "<false>": #in ["<false>","false"] : 
                            self.where.append( fluent(equ.left,False) )
                            continue
                        
                        additional_law = None
                        
                        #check if action or fluent / integer fluent
                        is_fluent = False
                        for flu in update.fluents:
                            if equ.left.compare_to(flu):
                                additional_law = fluent(equ.left,equ.right) #Domain statement
                                is_fluent = True
                                break 
                        if not is_fluent:
                            for inte in update.integer_ids: #TODO: do we need this?
                                if equ.left.compare_to(inte):#get a number for this law?
                                    update.set("has_integer",True)
                                    break
                        
                        # If right is variable
                        if not is_fluent and type(equ.right) == variable: # or (type(equ.right) == str and equ.right[0].isupper()):
                            current_var = str(equ.right)
                            fin_path = "head"
                            for (_,x) in my_path:
                                if x in ["head","if_part","ifcons_part","after_part"]:
                                    fin_path = x
                                    break
                            if not current_var in keys:
                                keys.append(current_var)
                            if variable_is_placeholder:
                                if not current_var in var_equ:
                                    var_equ[current_var] = [(equ.left,fin_path)]
                                else:
                                    var_equ[current_var].append((equ.left,fin_path))
                            else:
                                if not current_var in var_occ:
                                    var_occ[current_var] = [(equ.left,fin_path)]
                                else:
                                    var_occ[current_var].append((equ.left,fin_path))
    #                         if not fin_path == "head" and str(equ.left) in var_occ[current_var]:
    #                             (_,b) = var_occ[current_var][str(equ.left)]
    #                             if b not in ["if_part","after_part"]:
    #                                 var_occ[current_var][str(equ.left)]=(equ.left,fin_path)
    #                         else:
    #                             var_occ[current_var][str(equ.left)]=(equ.left,fin_path)
    
                        #end check
                        if additional_law is not None:
                            old_found=False
                            for old in self.where:
                                if additional_law.compare_to(old,accept_variables=False): # we check if there is such a law already
                                    old_found=True
                                    break
                            if not old_found: self.where.append(additional_law)
                    
                    else: # operator != "=" "=="
                        pass
                                
                    
                #else:
                #    raise NameError("Unbound Variable cannot be fixed, not bound in equation!")
            else:
                raise NameError("Unbound Variable cannot be fixed, no where part!")
        
        # Check for implied equations a=X if b=X means a:=b
        for var_key in keys:
            #if len(var_occ[var_key].keys()) > 1:
            if var_key in var_equ and len(var_equ[var_key]) >= 1: # > 1:
                stuff = var_equ[var_key] #.values() # Drop keys, they are only important for gathering the values
                if var_key in var_occ:
                    stuff += var_occ[var_key]
                #prime = True
                #prime_var = None
                for (f,p) in var_equ[var_key]: # Try to get a non-head as prime! (picking the last one should work)
                    if p != "head":
                        prime_var = f
                        prime_pos = p
                        break
                else:
                    prime_var = var_equ[var_key][0][0] 
                    prime_pos = var_equ[var_key][0][1]
                #prime_pos = var_equ[var_key][-1][1]
                #prime_var = var_equ[var_key][-1][0]
                for (flu, my_pos) in stuff:
                    
                    #if prime: 
                    #    prime = False
                    #    prime_var = flu
                    #    prime_pos = my_pos
                    #else:
                    if prime_var != flu or prime_pos != my_pos:
                        new_id = update.arith_idfunction()
                        arith_replacement = predicate("_arithmetic",atom_list(predicate("law",atom_list(str(new_id),[]))))
                        assignment = False
                        dynamic_law_part = False
                        
                        left_is_past_step = prime_pos == "after_part"
                        right_is_past_step = my_pos == "after_part"
                        
                        # arithmetic parts can only be placed in an after part, if no variables occurs in the head/ifcons
                        if prime_pos == "after_part" and my_pos == "after_part":
                            dynamic_law_part = True
                            att_chosen = "after_part"
                            left_is_past_step = False
                            right_is_past_step = False
                        elif prime_pos == "ifcons" and my_pos == "ifcons":
                            att_chosen = "ifcons_part"
                        else:
                            att_chosen = "if_part" 
                            
                        # Overwriting!
                        if my_pos == "head" or prime_pos == "head":
                            assignment = True
                            att_chosen = "head"
                        
                        left = arithmetic_atom(prime_var.print_facts(),update.arith_helper_idfunction(),negation=False,unknown=prime_var.type!="integer",apostroph=left_is_past_step,in_ifcons=prime_pos=="ifcons_part",law_part=prime_pos.replace("_part",""))
                        right = arithmetic_atom(flu.print_facts(),update.arith_helper_idfunction(),negation=False,unknown=flu.type!="integer",apostroph=right_is_past_step,in_ifcons=my_pos=="ifcons_part",law_part=my_pos.replace("_part",""))
                        if my_pos == "head" and not prime_pos == "head":
                            h = right
                            right = left
                            left = h
                        if my_pos == "head" and prime_pos == "head":
                            raise NameError("Head integer assignments with equal variable! Not fixed yet!!!") #TODO: fix
                        
                        right.negate()
                        
                        law = arithmetic_law([left,],[right,],"=",new_id,assignment,dynamic_law_part,[],self.where)
                        
                        
#                         if att_chosen == "head":
#                             if prime_pos == "head":
#                                 law = assignment(prime_var,flu)
#                             else:
#                                 law = assignment(flu,prime_var)
#                         else:
#                             # Create equation
#                             law = equation(prime_var,flu)
#                         law.pass_down_update(update)
                            
                        # Add equation to self (head/body/ifcons)
                        
                        # other_conditions will not be simplified!!!
                        #if not att_chosen in self.other_conditions:
                        #    self.other_conditions[att_chosen] = atom_list()
                        #self.other_conditions[att_chosen].append(equ)
                        
                        update.add_arithmetic_law(law)
                        
                        if hasattr(self,att_chosen):
                            law_part = getattr(self,att_chosen)
                            if type(law_part) == atom_list:
                                law_part.append(arith_replacement) #law
                            elif law_part is None:
                                setattr(self,att_chosen,atom_list(arith_replacement)) #law
                        else:
                            if att_chosen not in ["if_part","after_part","ifcons_part","head","body"]:
                                raise NameError("Adding implied equation to law part \""+att_chosen+"\" that does not exist!")
                            elif att_chosen in self.other_conditions.keys():
                                self.other_conditions[att_chosen].append(arith_replacement)
                            else:
                                self.other_conditions[att_chosen] = atom_list(arith_replacement)
                            
                                
                    
                                    
        # Add additions, but do not add their variables
        for addition in update.where_additions:
            
            if self.where is None:
                self.where = atom_list(addition)
            else:
                self.where.append(addition)
                   
                   
    def get_law_type(self):
        return self.law_type

    def replace_unbound_variables(self,assignm,negate=False):
        #return self
        if len(self.variables) > 0:
            nva = []
            for va in self.variables:
                # (x,y,after)
                for (x,y,_) in assignm:
                    if str(va) == str(y):
                        break
                else:
                    nva.append(va)
            self.variables = nva
        for att in self.child_attributes:
            neg = negate
            if att == "after_part": 
                neg = not neg
            if hasattr(self,att):
                val = getattr(self,att)
                if type(val) == list:
                    li = []
                    for x in val:
                        li.append(x.replace_unbound_variables(assignm,neg))
                    setattr(self, att, li)
                elif val is not None and type(val) != str:
                    setattr(self, att, val.replace_unbound_variables(assignm,neg))
        return self

class static_law(law): #static
    def __init__(self, head, if_part, ifcons_part, where,line=None,filename=None):
        law.__init__(self)
        self.law_type = "static_laws"
        self.head = head
        self.if_part = if_part
        self.ifcons_part = ifcons_part
        self.where = where
        self.line_number = line
        self.filename = filename
        self.law_id = None
        self.child_attributes = ["head","if_part","ifcons_part"]
        
    
    def add_part(self,part,law_position):
        if law_position in ["head"]:
            self.head.append(part)
        elif law_position in ["if_part","body","if","after"]:
            self.if_part.append(part)
        elif law_position in ["ifcons_part","ifcons"]:
            self.ifcons_part.append(part)
        else:
            print  >> sys.stderr, "ERROR, could not identify part "+law_position+" for", self.__class__ 
            errout.error("ERROR, could not identify part "+law_position+" for "+str(self.__class__ ))
            
                    
    def __str__(self):
        return str(self.head)+ \
            (" if "+str(self.if_part) if self.if_part is not None else "")+ \
            (" ifcons "+str(self.ifcons_part) if self.ifcons_part is not None else "")+ \
            (" where "+str(self.where) if self.where is not None else "")
            
    def typestr(self):
        return "static_law("+(self.head.typestr() if self.head is not None else "None")+ \
            "|"+(self.if_part.typestr() if self.if_part is not None else "None")+ \
            "|"+(self.ifcons_part.typestr() if self.ifcons_part is not None else "None")+")"
    
    def print_facts(self,prime=False):
        wherepart = self.compile_where()
        id_list = [str(self.law_id)]+self.variables
        myid = "law("+",".join(x for x in id_list)+")"
        #Law
        result = [ "static_law("+myid+")"+wherepart+"." ]
        
        stuff = [(self.head,"head"),(self.if_part,"if"),(self.ifcons_part,"ifcons")]
        for x in self.other_conditions:
            if x == "head":
                stuff.append((self.other_conditions[x],"head"))
            elif x == "ifcons":
                stuff.append((self.other_conditions[x],"ifcons"))
            else:
                stuff.append((self.other_conditions[x],"if"))
        for st in stuff:
            current = st[0]
            if current is None:
                continue
            cname = st[1]
            children = current.get_children()
            for ch in children:
                if type(ch) == str: resstr =  cname+"("+myid+","+ch+")"
                else: resstr =  cname+"("+myid+","+ch.print_facts(prime=True)+")"
                if ch.binding is not None:
                    whnew = ch.binding.compile_where_single()
                    if len(whnew) > 0:
                        if len(wherepart) > 0:
                            result += [ resstr+wherepart+", "+whnew+"." ] #Note that prime=False
                        else:
                            result += [ resstr+" :- "+whnew+"." ] #Note that prime=False
                    else:
                        result += [ resstr+wherepart+"." ] #Note that prime=False
                else:
                    result += [ resstr+wherepart+"." ]
        return result
        

class dynamic_law(law): #dynamic
    def __init__(self, head, after_part, ifcons_part, where,line=None,filename=None):
        law.__init__(self)
        self.law_type = "dynamic_laws"
        self.head = head
        self.after_part = after_part
        self.ifcons_part = ifcons_part
        self.where = where
        self.line_number = line
        self.filename = filename
        self.law_id = None
        self.child_attributes = ["head","after_part","ifcons_part"]
        
    def __str__(self):
        return str(self.head)+ \
            (" after "+str(self.after_part) if self.after_part is not None else "")+ \
            (" ifcons "+str(self.ifcons_part) if self.ifcons_part is not None else "")+ \
            (" where "+str(self.where) if self.where is not None else "")
            
    def typestr(self):
        return "dynamic_law("+(self.head.typestr() if self.head is not None else "None")+ \
            "|"+(self.after_part.typestr() if self.after_part is not None else "None")+ \
            "|"+(self.ifcons_part.typestr() if self.ifcons_part is not None else "None")+")"
            
    def print_facts(self,prime=False):
        wherepart = self.compile_where()
        id_list = [str(self.law_id)]+self.variables
        myid = "law("+",".join(x for x in id_list)+")"
        #Law
        result = [ "dynamic_law("+myid+")"+wherepart+"." ]
        
        stuff = [(self.head,"head"),(self.after_part,"after"),(self.ifcons_part,"ifcons")]
        for x in self.other_conditions:
            if x == "head":
                stuff.append((self.other_conditions[x],"head"))
            elif x == "after":
                stuff.append((self.other_conditions[x],"after"))
            else:
                stuff.append((self.other_conditions[x],"if"))
        for st in stuff:
            current = st[0]
            if current is None:
                continue
            cname = st[1]
            children = current.get_children()
            for ch in children:
                if ch.binding is not None:
                    whnew = ch.binding.compile_where_single()
                    if len(whnew) > 0:
                        if len(wherepart) > 0:
                            result += [ cname+"("+myid+","+ch.print_facts(prime=True)+")"+wherepart+", "+whnew+"." ]
                        else:
                            result += [ cname+"("+myid+","+ch.print_facts(prime=True)+") :- "+whnew+"." ]
                    else:
                        result += [ cname+"("+myid+","+ch.print_facts(prime=True)+")"+wherepart+"." ]
                else:
                    result += [ cname+"("+myid+","+ch.print_facts(prime=True)+")"+wherepart+"." ]
        return result

class nonexecutable_law(law): #nonexecutable
    def __init__(self, body, if_part, ifcons_part, where,line=None,filename=None):
        law.__init__(self)
        self.law_type = "nonexecutable_laws"
        self.body = body
        self.if_part = if_part
        self.ifcons_part = ifcons_part
        self.where = where
        self.line_number = line
        self.filename = filename
        self.law_id = None
        self.child_attributes = ["body","if_part","ifcons_part"]
        
    def __str__(self):
        return "nonexecutable "+str(self.body)+ \
            (" if "+str(self.if_part) if self.if_part is not None else "")+ \
            (" ifcons "+str(self.ifcons_part) if self.ifcons_part is not None else "")+ \
            (" where "+str(self.where) if self.where is not None else "")
            
    def typestr(self):
        return "nonexecutable("+(self.body.typestr() if self.body is not None else "None")+ \
            "|"+(self.if_part.typestr() if self.if_part is not None else "None")+ \
            "|"+(self.ifcons_part.typestr() if self.ifcons_part is not None else "None")+")"+"["+str(self.variables)+"]"
            
    def print_facts(self,prime=False):
        wherepart = self.compile_where()
        id_list = [str(self.law_id)]+self.variables
        myid = "law("+",".join(x for x in id_list)+")"
        #Law
        result = []
        
        stuff = [(self.body,"nonexecutable"),(self.if_part,"nonexecutable"),(self.ifcons_part,"ifcons")]
        for x in self.other_conditions:
            if x == "head":
                stuff.append((self.other_conditions[x],"nonexecutable"))
            else:
                stuff.append((self.other_conditions[x],"if"))
        for st in stuff:
            current = st[0]
            if current is None:
                continue
            cname = st[1]
            children = current.get_children()
            for ch in children:
                if ch.binding is not None:
                    whnew = ch.binding.compile_where_single()
                    if len(whnew) > 0:
                        if len(wherepart) > 0:
                            result += [ cname+"("+myid+","+ch.print_facts(prime=True)+")"+wherepart+", "+whnew+"." ] #Note that prime=False
                        else:
                            result += [ cname+"("+myid+","+ch.print_facts(prime=True)+") :- "+whnew+"." ] #Note that prime=False
                    else:
                        result += [ cname+"("+myid+","+ch.print_facts(prime=True)+")"+wherepart+"." ] #Note that prime=False
                else:
                    result += [ cname+"("+myid+","+ch.print_facts(prime=True)+")"+wherepart+"." ]
        return result
    
    def simplify(self,negation=False,in_where=False):
        res = parse_object.simplify(self, negation, in_where)
        if ((self.body is None) or (len(self.body)==0)) \
            and ((self.if_part is None) or (len(self.if_part)==0)) \
            and ((self.ifcons_part is None) or (len(self.ifcons_part)==0)):
            return kill_encoding(dynamic=True)
        return res


class impossible_law(law): #impossible
    def __init__(self, body, ifcons_part, where,line=None,filename=None):
        law.__init__(self)
        self.law_type = "impossible_laws"
        self.body = body
        self.ifcons_part = ifcons_part
        self.where = where
        self.line_number = line
        self.filename = filename
        self.law_id = None
        self.child_attributes = ["body","ifcons_part"]
        
    def __str__(self):
        return "impossible "+str(self.body)+ \
            (" ifcons "+str(self.ifcons_part) if self.ifcons_part is not None else "")+ \
            (" where "+str(self.where) if self.where is not None else "")
            
    def typestr(self):
        return "impossible_law("+(self.body.typestr() if self.body is not None else "None")+ \
            ";"+(self.ifcons_part.typestr() if self.ifcons_part is not None else "None")+")"
            
    def print_facts(self,prime=False):
        wherepart = self.compile_where()
        id_list = [str(self.law_id)]+self.variables
        myid = "law("+",".join(x for x in id_list)+")"
        #Law
        result = []
        
        stuff = [(self.body,"impossible"),(self.ifcons_part,"ifcons")]
        for x in self.other_conditions:
                stuff.append((self.other_conditions[x],"impossible"))
        for st in stuff:
            current = st[0]
            if current is None:
                continue
            cname = st[1]
            children = current.get_children()
            for ch in children:
                if ch.binding is not None:
                    whnew = ch.binding.compile_where_single()
                    if len(whnew) > 0:
                        if len(wherepart) > 0:
                            result += [ cname+"("+myid+","+ch.print_facts(prime=True)+")"+wherepart+", "+whnew+"." ]
                        else:
                            result += [ cname+"("+myid+","+ch.print_facts(prime=True)+") :- "+whnew+"." ]
                    else:
                        result += [ cname+"("+myid+","+ch.print_facts(prime=True)+")"+wherepart+"." ]
                else:
                    result += [ cname+"("+myid+","+ch.print_facts(prime=True)+")"+wherepart+"." ]
        return result


class inertial_law(law): #inertial
    def __init__(self, head, where,line=None,filename=None):
        law.__init__(self)
        self.law_type = "inertial_laws"
        self.head = head
        self.where = where
        self.line_number = line
        self.filename = filename
        self.child_attributes = ["head"]
        
    def __str__(self):
        return "inertial "+str(self.head)+ \
            (" where "+str(self.where) if self.where is not None else "")
            
    def typestr(self):
        return "inertial_law("+self.head.typestr()+")"
            
    def print_facts(self,prime=False):
        wherepart = self.compile_where()
        #Law
        result = []
        
        children = self.head.get_children()
        for x in self.other_conditions:
            children += self.other_conditions[x].get_children()
        for ch in children:
            if ch.binding is not None:
                whnew = ch.binding.compile_where_single()
                if len(whnew) > 0:
                    if len(wherepart) > 0:
                        result += [ "inertial("+ch.print_facts()+")"+wherepart+", "+whnew+"." ] #Note that prime=False
                    else:
                        result += [ "inertial("+ch.print_facts()+") :- "+whnew+"." ] #Note that prime=False
                else:
                    result += [ "inertial("+ch.print_facts()+")"+wherepart+"." ] #Note that prime=False
            else:
                result += [ "inertial("+ch.print_facts()+")"+wherepart+"." ] #Note that prime=False
        return result

class default_law(law): #default
    def __init__(self, head, if_part, after_part, where, dynamic=None,line=None,filename=None):
        law.__init__(self)
        self.law_type = "default_laws"
        self.head = head
        self.if_part = if_part
        self.after_part = after_part
        self.where = where
        self.line_number = line
        self.filename = filename
        self.law_id = None
        if dynamic is not None:
            self.dynamic = dynamic
        else:
            self.dynamic = after_part == None
        self.child_attributes = ["head","if_part","after_part"]
        
    def __str__(self):
        return "default "+str(self.head)+ \
            (" if "+str(self.if_part) if self.if_part is not None else "")+ \
            (" after "+str(self.after_part) if self.after_part is not None else "")+ \
            (" where "+str(self.where) if self.where is not None else "")
            
    def typestr(self):
        return "default_law("+(self.head.typestr() if self.head is not None else "None")+ \
            "|"+(self.if_part.typestr() if self.if_part is not None else "None")+ \
            "|"+(self.after_part.typestr() if self.after_part is not None else "None")+")"
            
    def print_facts(self,prime=False):
        wherepart = self.compile_where()
        id_list = [str(self.law_id)]+self.variables
        myid = "law("+",".join(x for x in id_list)+")"
        #Law
        result = []
        
        if not self.dynamic and self.if_part is None and self.after_part is None and self.head is not None:
            for ch in self.head:
                result += [ "default("+ch.print_facts(prime=True)+")"+wherepart+"." ]
            return result
        
        
        stuff = [(self.head,"default"),(self.if_part,"if"),(self.after_part,"after")]
        for x in self.other_conditions:
            if x == "head":
                stuff.append((self.other_conditions[x],"head"))
            else:
                stuff.append((self.other_conditions[x],"if"))
        for st in stuff:
            current = st[0]
            if current is None:
                continue
            cname = st[1]
            children = current.get_children()
            #if self.dynamic:
            #    result += [ "dynamic_law("+myid+")"+wherepart+"." ]
            for ch in children:
                if ch.binding is not None:
                    whnew = ch.binding.compile_where_single()
                    if len(whnew) > 0:
                        if len(wherepart) > 0:
                            result += [ cname+"("+myid+","+ch.print_facts(prime=True)+")"+wherepart+", "+whnew+"." ]
                        else:
                            result += [ cname+"("+myid+","+ch.print_facts(prime=True)+") :- "+whnew+"." ]
                    else:
                        result += [ cname+"("+myid+","+ch.print_facts(prime=True)+")"+wherepart+"." ]
                else:
                    result += [ cname+"("+myid+","+ch.print_facts(prime=True)+")"+wherepart+"." ]
        return result


class visible_law(law): #visible
    def __init__(self, head, if_part, where,line=None,filename=None):
        law.__init__(self)
        self.law_type = "visible_laws"
        self.head = head
        self.if_part = if_part
        self.where = where
        self.line_number = line
        self.filename = filename
        self.law_id = None
        self.child_attributes = ["head","if_part"]
        
    def __str__(self):
        return "visible "+str(self.body)+ \
            (" if "+str(self.if_part) if self.if_part is not None else "")+ \
            (" where "+str(self.where) if self.where is not None else "")
            
    def typestr(self):
        return "visible_law("+self.head.typestr()+ \
            "|"+(self.if_part.typestr() if self.if_part is not None else "")+")"
            
    def print_facts(self,prime=False):
        wherepart = self.compile_where()
        id_list = [str(self.law_id)]+self.variables
        myid = "law("+",".join(x for x in id_list)+")"
        #Law
        result = []
        
        stuff = [(self.head,"visible"),(self.if_part,"if")]
        for x in self.other_conditions:
            if x == "head":
                stuff.append((self.other_conditions[x],"head"))
            else:
                stuff.append((self.other_conditions[x],"if"))
        for st in stuff:
            current = st[0]
            if current is None:
                continue
            cname = st[1]
            children = current.get_children()
            for ch in children:
                if ch.binding is not None:
                    whnew = ch.binding.compile_where_single()
                    if len(whnew) > 0:
                        if len(wherepart) > 0:
                            result += [ cname+"("+myid+","+ch.print_facts()+")"+wherepart+", "+whnew+"." ] #Note that prime=False
                        else:
                            result += [ cname+"("+myid+","+ch.print_facts()+") :- "+whnew+"." ] #Note that prime=False
                    else:
                        result += [ cname+"("+myid+","+ch.print_facts()+")"+wherepart+"." ] #Note that prime=False
                else:
                    result += [ cname+"("+myid+","+ch.print_facts()+")"+wherepart+"." ] #prime is False
        return result

class kill_encoding(law):
    def __init__(self, dynamic=False):
        law.__init__(self)
        self.law_type = "killEncoding"
        self.dynamic = dynamic

class false_atom(parse_object):
    def __init__(self):
        parse_object.__init__(self)
    def typestr(self):
        return "FALSE"
    def __str__(self):
        return "FALSE"
    def is_false(self):
        return True
      

#class where_part(parse_object):
#    pass
 

# Facts are simple statements.
class fact(law):
    def __init__(self):
        law.__init__(self)
        self.child_attributes = ["head"]


class predicate_fact(fact):
    def __init__(self, head, where,line=None,filename=None):
        fact.__init__(self)
        self.law_type = "preds"
        self.head = head
        self.where = where
        self.line_number = line
        self.filename = filename
        
    def __str__(self):
        return str(self.head)
    
    def typestr(self):
        return "predicate_fact("+self.head.typestr()+")"

    def print_facts(self,prime=False):
        ###
        wherepart = self.compile_where()
        id_list = [str(self.law_id)]+self.variables
        myid = "law("+",".join(x for x in id_list)+")"
        #Law
        result = [ "static_law("+myid+")"+wherepart+"." ]
        
        children = self.head.get_children()
        for ch in children:
            result += [ "head("+myid+","+ch.print_facts(prime=True)+")"+wherepart+"." ]
        return result

class action_fact(fact):
    def __init__(self, head, where,line=None,filename=None):
        fact.__init__(self)
        self.law_type = "actions"
        self.head = head
        self.where = where
        self.line_number = line
        self.filename = filename
        
    def __str__(self):
        return str(self.head)
    
    def typestr(self):
        return "action("+self.head.typestr()+")"
    
    def get_actions(self):
        if type(self.head) == str: return str
        else: return self.head.get_actions()
        
    def print_facts(self,prime=False):
        result = ""
        wherepart = self.compile_where()
        for ac in self.head:
            st = ac.print_facts(prime=True)
            result += "action("+st+")"+wherepart+"."
        return result


class fluent_fact(fact):
    def __init__(self, head, where,multivalued=None,line=None,filename=None,dotted_domain=None):
        fact.__init__(self)
        self.law_type = "fluents"
        self.head = head
        self.where = where
        self.line_number = line
        self.filename = filename
        self.multivalued = multivalued
        self.dotted_domain = dotted_domain # (lower,upper)
        
    def __str__(self):
        return str(self.head)
    
    def typestr(self):
        return "fluent_fact("+self.head.typestr()+")"
    
#     def get_fluents(self,simple=True):
#         if type(self.head) == str: return self.head
#         else: return self.head.get_fluents(simple)

    def pass_down_update_overwrite(self, update):
        self.law_id = update.idfunction()

    def get_fluents_domains(self): 
        result = []
        wh = self.get_where()
        for x in self.head:
            
            if self.dotted_domain is not None:
                (lo,up) = self.dotted_domain
                dotted = asp_dotted_fact("_Value",lo,up)
                if wh is not None:
                        wh.append(dotted)
                else:
                    wh = atom_list(dotted)
                result.append(domain(x, "_Value", wh)) #x.content
            else:
                do = x.get_fluents_domains()
                for d in do:
                    if wh is not None: d.where = wh
                    else: wh = d.where
                    if self.multivalued is not None:
                        #if d.values == None: self.multivalued.append(d.values)
                        for x in self.multivalued:
                            result.append(domain(d.fluent, x, wh))
                    else:
                        result.append(d)
        return result
        self.type = "fluent" 
        return [domain(self,None),]
        
    def print_facts(self,prime=False):
        result = []
        wherepart = self.compile_where()
        for ac in self.head:
            st = ac.print_facts() # Prime is False
            result.append("fluent("+st+")"+wherepart+".")
        return result


class defined_fluent_fact(fact):
    def __init__(self, head, where, multivalued=None,line=None,filename=None):
        fact.__init__(self)
        self.law_type = "defined_fluents"
        self.head = head
        self.where = where
        self.line_number = line
        self.filename = filename
        
    def __str__(self):
        return str(self.head)
    
    def typestr(self):
        return "dfluent_fact("+self.head.typestr()+")"
    
    def print_facts(self,prime=False):
        result = ""
        wherepart = self.compile_where()
        for ac in self.head:
            st = ac.print_facts()
            result += "defined_fluent("+st+")"+wherepart+"."
        return result


class integer_fact(fact):
    def __init__(self, head, domain, where,line=None,filename=None):
        fact.__init__(self)
        self.law_type = "integers"
        self.head = head
        self.domain = domain
        self.where = where
        self.line_number = line
        self.filename = filename
        
    def __str__(self):
        return str(self.head)
    
    def typestr(self):
        return "integer("+self.head.typestr()+")"
    
    def print_facts(self,prime=False):
        result = []
        wherepart = self.compile_where()
        domain = False
        if self.domain is not None and len(self.domain) == 2:
            lower = self.domain.get_children()[0]
            if type(lower) != str:
                lower = lower.print_facts()
            upper = self.domain.get_children()[1]
            if type(upper) != str:
                upper = upper.print_facts()
            domain = True
        for ac in self.head:
            st = ac.print_facts()
            result.append("integer("+st+")"+wherepart+".")
            if domain:
                result.append("integer_domain("+st+","+lower+","+upper+")"+wherepart+".")
        return result

    def get_integers(self):
        return [self,]
    
    # We use this to translate integers to fluents if needed
    def pass_down_update_overwrite(self,update):
        if clingo_arithmetics:
            self.replacement = fluent_fact(atom_list(unknown(self.head)), self.where, None, self.line_number, self.filename, self.domain)
            update.integers_changed_to_fluents.append(self.replacement)
    
    # We use this to translate integers to fluents if needed
    def simplify(self,negation=False,in_where=False):
        if clingo_arithmetics and self.replacement is not None:
            return self.replacement
        else:
            return parse_object.simplify(self, negation, in_where)

class query(law):
    def __init__(self):
        law.__init__(self)


class initial_law(query):
    def __init__(self, head, where,line=None,filename=None):
        query.__init__(self)
        self.law_type = "initially_laws"
        self.head = head
        self.where = where
        self.line_number = line
        self.filename = filename
        self.child_attributes = ["head"]
        
    def __str__(self):
        return str(self.head)
    
    def typestr(self):
        return "initially("+self.head.typestr()+")"
    
    def print_facts(self,prime=False):
        result = []
        wherepart = self.compile_where()
        for ac in self.head:
            st = ac.print_facts(prime=True)
            if ac.binding is not None:
                whnew = ac.binding.compile_where_single()
                if len(whnew) > 0:
                    if len(wherepart) > 0:
                        result.append("initially("+st+")"+wherepart+", "+whnew+"." )
                    else:
                        result.append("initially("+st+") :- "+whnew+"." )
                else:
                    result.append("initially("+st+")"+wherepart+".")
            else:
                result.append("initially("+st+")"+wherepart+".")
        return result


class goal_law(query):
    def __init__(self, head, where,line=None,filename=None):
        query.__init__(self)
        self.law_type = "goals"
        self.head = head
        self.where = where
        self.line_number = line
        self.filename = filename
        self.child_attributes = ["head"]
        
    def __str__(self):
        return str(self.head)
    
    def typestr(self):
        return "finally("+self.head.typestr()+")"
    
    def print_facts(self,prime=False):
        result = []
        wherepart = self.compile_where()
        for ac in self.head:
            st = ac.print_facts(prime=True)
            result.append("finally("+st+")"+wherepart+".")
        return result


     
#class super_atom(object):
#    pass
#    #COMBINE!
#
#class atom(super_atom): # literal
#    pass
#


class role(parse_object):
    def __init__(self, content):
        parse_object.__init__(self)
        self.content = content
        self.child_attributes = ["content"]
        
    def __str__(self):
        return str(self.content)
    
    def typestr(self):
        return "role("+self.content.typestr()+")"

# This may only occur in a where part!!!
class action(parse_object):
    def __init__(self, content):
        parse_object.__init__(self)
        self.content = content
        self.child_attributes = ["content"]
        
    def __str__(self):
        return str(self.content)
    
    def typestr(self):
        if type(self.content) == str: return "action"
        else: return "action("+self.content.typestr()+")"
        
    def get_actions(self):
        #if type(self.head) == str: return str
        #else: return self.head.get_action()
        return self
    
    def compile_where_single(self):
        if self.negation: 
            print >> sys.stderr, "% Warning! Action "+str(self)+" is negated."
            errout.error("% Warning! Action "+str(self)+" is negated.")
        return "action(act("+self.content.print_facts()+"))"
    
    def pass_down_update_overwrite(self,update):
        if not update.where:
            print >> sys.stderr, "% Action "+str(self)+" can only appear in where parts!"
            errout.error("% Action "+str(self)+" can only appear in where parts!")
        update.add_where_action(self.content)
    
    def get_bottom_elements(self):
        return [self,]
    
    # Only used in where
    def get_explicitly_bound_variables(self,where=False,bound=False):
        if where: 
            x = self.content.get_explicitly_bound_variables(True,True)
            if type(x) == list: return x
            else: return [x]
        else: 
            x = self.content.get_explicitly_bound_variables(where,bound)
            if type(x) == list: return x
            else: return [x]

# This may only occur in a where part!!!
class fluent(parse_object):
    def __init__(self, content, domainelement=None):
        parse_object.__init__(self)
        self.content = content
        self.domainelement = domainelement
        self.child_attributes = ["content","domainelement"]
        
    def __str__(self):
        return str(self.content)
    
    def typestr(self):
        if type(self.content) == str: return "fluent"
        else: return "fluent("+self.content.typestr()+")"
        
#     def get_fluents(self,simple=True):
#         #if type(self.head) == str: return str
#         #else: return self.head.get_action()
#         
#         #if simple: 
#         #    return self
#         #else:
#         #    return assignment(self,"true")
#         
#         return self
    
    def print_facts(self,prime=False):
        #wherepart = self.compile_where()
        if self.domainelement is None:
            de = str(not self.negation).lower() #"true"
        else:
            de = str(self.domainelement)
        if prime:
            return "val("+self.content+","+de+")"
        else:
            return str(self.content)
        
    # Only used in where
    def get_explicitly_bound_variables(self,where=False,bound=False):
        if where: 
            bound=True
        my_vars = []
        ch = self.get_children()
        for c in ch:
            if c is None or type(c) == str: continue
            vs = c.get_explicitly_bound_variables(where,bound)
            if type(vs) == list:
                my_vars += vs
            else:
                my_vars.append(vs) 
        return my_vars
        
    def compile_where_single(self):
        if self.domainelement is None:
            return "fluent("+self.content.print_facts()+")"
        else:
            if type(self.content)==str:
                cont = self.content
            else:
                cont = self.content.print_facts()
            if type(self.domainelement)==str:
                dom = self.domainelement
            else:
                dom = self.domainelement.print_facts()
                 
            return "domain("+cont+","+dom+")"
    
    def pass_down_update_overwrite(self,update):
        if not update.where:
            print >> sys.stderr, "% Fluent "+str(self)+" can only appear in where parts!"
            errout.error("% Fluent "+str(self)+" can only appear in where parts!")
        for x in update.integers:
            if str(self.content) == str(x):
                print >> sys.stderr, "% \"where fluent "+str(self)+"="+str(self.domainelement)+"\" is not supported for integer fluent "+str(self)+"."
                errout.error("% \"where fluent "+str(self)+"="+str(self.domainelement)+"\" is not supported for integer fluent "+str(self)+".")
                self.variables = []
                return
        update.add_where_fluent(self.content)
    
    def get_bottom_elements(self):
        return [self,]

class fluent_multival(fluent):
    def __init__(self, content, multidomain=None, int_operator=False):
        fluent.__init__(self, content, None)
        self.multidomain = multidomain
        self.is_int = int_operator
 
    def get_fluents_domains(self):
        result = []
        if self.multidomain is None and self.binding is not None:
            self.multidomain = self.binding
            self.is_int = True
        for x in self.multidomain:
            result.append(domain(self.content,x))
        return result
    
    def pass_down_update_overwrite(self,update):
        pass

    
class predicate(parse_object):
    def __init__(self, name, parameters, apostroph=False):
        parse_object.__init__(self)
        self.name = name
        self.parameters = parameters
        self.compile_where_single = self.print_facts
        self.type = "??"
        self.child_attributes = ["parameters"]
        self.apostroph = apostroph # Apostroph refers to a different time step.
        
    def __str__(self):
        if self.parameters is None: 
            return str(self.name)
        else:
            return str(self.name)+"("+(",".join(str(x) for x in self.parameters))+")"
        
    def typestr(self):
        res = []
        for x in self.parameters:
            if type(x) == str: res.append(x)
            else: res.append(x.typestr())
        return "predicate("+", ".join(res)+")"
    
#     def get_fluents(self,simple=True): 
#         #if simple: 
#         #    return self
#         #else:
#         #    return assignment(self,"true")
#         return self

    def get_fluents_domains(self):
        return [domain(self,None),]
    
    def get_domain(self):
        return ["true","false"]
    
    def get_actions(self):
        self.type = "action"
        return self
    
    def get_bottom_elements(self):
        return [self,]
    
    def print_facts(self,prime=False):
        #wherepart = self.compile_where()
        
        if self.parameters is not None: 
            text = self.name+"("+",".join(x.print_facts() if type(x) != str else x for x in self.parameters)+")"
        elif type(self.name) == str:
            text= self.name
        else:
            print >> sys.stderr, "This should not happen!"
            #print self.name.typestr()
            text = self.name.print_facts()
        if prime:
            if self.type == "fluent":
                return "val("+text+","+str(not self.negation).lower()+")" #true)"
            elif self.type == "action":
                if self.negation: 
                    print >> sys.stderr, "% Warning! Action "+str(self)+" is negated."
                    errout.error("% Warning! Action "+str(self)+" is negated.")
                return "act("+text+")"      
            elif self.type == "integer":
                if self.negation: 
                    print >> sys.stderr, "% Warning! Fluent "+str(self)+" is negated."
                    errout.error("% Warning! Integer "+str(self)+" is negated.")
                return "_arithmetic("+text+")"     
        return text
    
    def pass_down_update(self,update):
        if update.get("check"):
            definite_type = False
            if self in update.actions:
                self.type = "action" 
                definite_type = True
                self.reference = self
            if self in update.fluents:
                if self.type == "action" and definite_type:
                    raise NameError(str(self)+" cannot be defined as action and fluent!")
                self.type = "fluent" 
                definite_type = True
                self.reference = self
            if self in update.integer_ids:
                if self.type == "action" and definite_type:
                    raise NameError(str(self)+" cannot be defined as fluent and action!")
                self.type = "integer" 
                update.set("has_integer",True)
                definite_type = True
                self.reference = self
            
            if update.had_where:
                had_act = False
                had_flu = False
                for act in update.where_actions:
                    if self.compare_to(act):
                        self.reference = act
                        self.type = "action"
                        definite_type = True
                        had_act = True
                        break 
                for flu in update.where_fluents:
                    if self.compare_to(flu):
                        self.reference = flu
                        self.type = "fluent"
                        definite_type = True
                        had_flu = True
                        break 
                if had_act and had_flu:
                    print >> sys.stderr, "% Error! "+str(self)+" is Fluent and Action at the same time"
                    errout.error("% Error! "+str(self)+" is Fluent and Action at the same time")
            
            if not definite_type:
                for act in update.actions:
                    if self.compare_to(act):
                        self.reference = act
                        self.type = "action"
                        definite_type = True
                        break 
            if not definite_type:
                for flu in update.fluents:
                    if self.compare_to(flu):
                        self.reference = flu
                        self.type = "fluent"
                        definite_type = True
                        break 
            if not definite_type:
                for inte in update.integer_ids:
                    if self.compare_to(inte):#get a number for this law?
                        self.reference = inte
                        self.type = "integer"
                        update.set("has_integer",True)
                        definite_type = True
                        break 
            
            if update.where:
                self.type = "asp"
            elif not definite_type and self.type == "??": # Assume Fluent!
                print >> sys.stderr, "% Warning: Cannot find "+str(self)+" in fluents or actions!"
                errout.error( "% Warning: Cannot find "+str(self)+" in fluents or actions!")
                self.type = "fluent"
            
        for c in self.parameters:
            if type(c) == str: continue
            update.path_inc(self,"parameters")
            prev = update.get("check")
            update.set("check",False)
            variables = c.pass_down_update(update)# Don't pass where
            update.set("check",prev)
            update.path_dec()
            for v in variables:
                if not v in self.variables:
                    self.variables.append(v)
                    
        #Code for adding binding to where part! 
        if self.binding is not None:
            #update.add_to_where(self.binding)
            variables = self.binding.get_variables()
            for v in variables:
                if str(v) in self.variables:
                    self.variables.remove(str(v))
            pass
        
        return self.variables
    
    # simplification for integers?
    
    def compare_to(self,other,parent=True,accept_variables=True):
        if self.__class__ == other.__class__:
            if self.name != other.name or len(self.parameters) != len(other.parameters): return False
            return self.parameters.compare_to(other.parameters,parent=False,accept_variables=accept_variables)
        # Tricky: compare Predicate to Unknown/Action/Fluent?
        if not parent: 
            if other.__class__ == variable: return True
            if type(other) == str:
                return other.isupper()
            o = other.print_facts()
            return type(o) == str and o.isupper()
        
        return False
    
    def arith_flatten(self,negation,update):
        return arithmetic_atom(self.print_facts(),update.arith_helper_idfunction(),negation,variables=self.variables,apostroph=self.apostroph)

    def get_explicitly_bound_variables(self,where=False,bound=False):
        if where: 
            bound=True
        my_vars = []
        ch = self.get_children()
        for c in ch:
            if c is None or type(c) == str: continue
            vs = c.get_explicitly_bound_variables(where,bound)
            if type(vs) == list:
                my_vars += vs
            else:
                my_vars.append(vs) 
        return my_vars

class arithmetic_law(law): # Will be generated out of equations!
    def __init__(self,head,body,operator,my_id,assignment,dynamic_law_part,variables,where=None):
        law.__init__(self)
        self.head = head
        self.body = body
        self.operator = operator
        self.my_id = my_id
        self.is_assignment = assignment #check if it is in a head...
        self.is_dynamic_law_part = dynamic_law_part
        self.variables = variables
        self.where = where
        self.child_attributes = ["head","body"]
        if self.operator in ["=","=="]: self.operator_type = "eq" # a+b = c+d -> a+b-c-d = 0
        elif self.operator == ">": self.operator_type = "gt" # a > b -> a-b > 0
        elif self.operator == "<": self.operator_type = "lt"
        elif self.operator == ">=": self.operator_type = "ge"
        elif self.operator == "<=": self.operator_type = "le"
        elif self.operator == "!=": self.operator_type = "ne"
        else:
            print >> sys.stderr, "Error! Unknown arithmetic symbol "+self.operator
            errout.error("Error! Unknown arithmetic symbol "+self.operator)
            self.operator_type = "eq"
        has_number = False
        for e in self.head:
            if e.has_no_variable():
                has_number = True
                break
        for e in self.body:
            if e.has_no_variable():
                has_number = True
                break
        if not has_number:
            self.body.append(arithmetic_atom('0','0'))
            
    def __str__(self):
        if type(self.head) == list:
            return "["+"+".join(str(x) for x in self.head) + str(self.operator)+ \
            ("+".join(str(x) for x in self.body))+  "]"
        return "["+str(self.head) + str(self.operator)+ \
            ("+".join(str(x) for x in self.body))+  "]"
    
    
    def typestr(self):
        return str(self)
    
    def print_facts(self, prime=False):
        wherepart = self.compile_where()
        result = []
        stid = "law("+','.join([str(self.my_id)]+self.variables)+")"
        if self.is_assignment:
            if self.is_dynamic_law_part:
                result.append("arithmetic_assignment_dynamic("+stid+")"+wherepart+".")
            else:
                result.append("arithmetic_assignment("+stid+")"+wherepart+".")
        result.append("arithmetic_law("+stid+","+self.operator_type+")"+wherepart+".")
        
        if additional_ifcons_facts:
            inverse_apostroph = True
        else:
            inverse_apostroph = False 
            # This was used to express that ' is t-1 and ' in the head inverses the meaning of ' to t
        if self.is_assignment:
            for e in self.head:
                #try:
                #    if e.apostroph: inverse_apostroph = True
                #except:
                #    pass
                result.append("arithmetic_head("+stid+","+e.print_facts()+")"+wherepart+".")
        else:
            for e in self.head:
                if e.law_part is not None: # CONDITION for part knowing it's timestep
                    if e.law_part == "ifcons":
                        result.append("arithmetic_ifcons("+stid+","+e.print_facts()+")"+wherepart+".") 
                    if e.law_part == "head":
                        result.append("arithmetic_head("+stid+","+e.print_facts()+")"+wherepart+".")
                    else:
                        result.append("arithmetic("+stid+","+e.print_facts()+")"+wherepart+".")
                else:
                    result.append("arithmetic("+stid+","+e.print_facts()+",0)"+wherepart+".")
        
        if old_arithmetics: inverse_apostroph = not inverse_apostroph 
        # In old arithmetics, it was the other way...
        # But there were also no apostroph's
        
        for e in self.body:
            try:
                # CONDITION for part knowing it's timestep
                if e.law_part is not None or \
                    (e.variable is None and not e.unknown): #: # CONDITION for numbers
                    #if e.law_part == "after":
                    #    result.append("arithmetic("+stid+","+e.print_facts()+",-1)"+wherepart+".")
                    #else:
                    if e.law_part == "ifcons":
                        result.append("arithmetic_ifcons("+stid+","+e.print_facts()+")"+wherepart+".")
                    result.append("arithmetic("+stid+","+e.print_facts()+")"+wherepart+".")
                elif e.apostroph != inverse_apostroph:
                    if self.is_dynamic_law_part:
                        result.append("arithmetic("+stid+","+e.print_facts()+",-1)"+wherepart+".")
                    else:
                        result.append("arithmetic("+stid+","+e.print_facts()+",0)"+wherepart+".")
                else: 
                    result.append("arithmetic("+stid+","+e.print_facts()+",0)"+wherepart+".")
                    if additional_ifcons_facts: result.append("arithmetic_ifcons("+stid+","+e.print_facts()+")"+wherepart+".") #new for ifcons!
            except:
                result.append("arithmetic("+stid+","+e.print_facts()+",0)"+wherepart+".")
            
        return result

class arithmetic_additive_law(arithmetic_law): # Will be generated out of equations!
    
    def __init__(self,head,body,my_id,dynamic_law_part,variables,where=None):
        arithmetic_law.__init__(self,head,body,"=",my_id,True,dynamic_law_part,variables,where)
        #print >> sys.stderr, "Warning! Incremental statements using += will result in inertial behavior for the fluent." 
        #print >> sys.stderr, "Warning! Incremental statements using += may result in different behavior!"
    
    def print_facts(self, prime=False):
        
        if self.other_conditions is not None and len(self.other_conditions) > 0:
            errout.error("Arithmetic additive law with other_conditions: "+str(self.other_conditions))
        
        wherepart = self.compile_where()
        result = []
        stid = "law("+','.join([str(self.my_id)]+self.variables)+")"

        result.append("arithmetic_additive_law("+stid+")"+wherepart+".")

        if additional_ifcons_facts:
            inverse_apostroph = True
        else:
            inverse_apostroph = False 
            # This was used to express that ' is t-1 and ' in the head inverses the meaning of ' to t
        
        for e in self.head:
            try:
                if e.apostroph: inverse_apostroph = True
            except:
                pass
            result.append("arithmetic_additive_fluent("+stid+","+e.variable+")"+wherepart+".")
            
        if self.is_dynamic_law_part:
            result.append("arithmetic_assignment_dynamic("+stid+")"+wherepart+".")
        else:
            result.append("arithmetic_assignment("+stid+")"+wherepart+".")
        #result.append("arithmetic_additive_law("+stid+","+self.operator_type+")"+wherepart+".")
        
        for e in self.head:
            e.encapsulate("additive_helper("+stid+",",")")
            result.append("arithmetic_head("+stid+","+e.print_facts()+")"+wherepart+".")
            
        
        for e in self.body:
            try:
                if e.variable is None and not e.unknown:
                    result.append("arithmetic("+stid+","+e.print_facts()+")"+wherepart+".")
                elif e.apostroph != inverse_apostroph:
                    if self.is_dynamic_law_part:
                        result.append("arithmetic("+stid+","+e.print_facts()+",-1)"+wherepart+".")
                    else:
                        result.append("arithmetic("+stid+","+e.print_facts()+",0)"+wherepart+".")
                else:
                    result.append("arithmetic("+stid+","+e.print_facts()+",0)"+wherepart+".")
                    if additional_ifcons_facts: result.append("arithmetic_ifcons("+stid+","+e.print_facts()+")"+wherepart+".") #new for ifcons!
            except:
                result.append("arithmetic("+stid+","+e.print_facts()+",0)"+wherepart+".")    
            
        return result

class arithmetic_atom(parse_object):
    def __init__(self,value,helper_id,negation=False,unknown=False,variables=[],apostroph=False,in_ifcons=False,law_part=None):
        parse_object.__init__(self)
        self.unknown = unknown
        self.value = None
        self.unknown_is = None
        self.variables=variables
        self.helper_id = helper_id
        self.apostroph=apostroph # Apostroph refers to a different time step.
        self.in_ifcons=in_ifcons
        
        if type(value) == str and value.isdigit() or value[0] == "-" and value[1:].isdigit():
            self.factor = float(value)
            self.variable = None
        elif type(value) == str and value.isupper():
            self.variable = None
            self.factor = 1
            self.unknown = True
            self.value = value
        else:
            self.variable = value
            self.factor = 1
        self.negation = negation
        self.law_part = law_part # head after if ifcons
    
    #def negate(self):
    #    self.negation = not self.negation
    
    def encapsulate(self,pre,post):
        if self.variable is not None:
            self.variable = pre+self.variable+post
        
    def has_no_variable(self):
        return not self.unknown and self.variable is None
        
    def can_add(self,other):
        return not self.unknown and not other.unknown and self.variable == other.variable # Equal or both None
    
    def negate(self):
        self.negation = not self.negation
    
    def add(self,other):
        if self.variable == other.variable:
            a = self.factor
            b = other.factor
            if self.negation == other.negation:
                self.factor = a+b
            elif a-b >= 0:
                self.factor = a-b
            else:
                self.negation = other.negation
                self.factor = -a+b
                
            return self
        else:
            raise NameError("Arithmetics: Internal error adding two variables.")
    
    def multiply(self,other):
        if other.__class__ is not arithmetic_atom: raise NameError("Arithmetics: Found wrong object for multiplication!")
        if self.unknown:
            if other.unknown:
                if self.variable is None and other.variable is None:
                    self.variable = other.value
                    self.unknown_is = "Factor"
                else:
                    raise NameError("Arithmetics: Multiplying variables is not possible with linear constraints!")
            a = self.factor
            b = other.factor
            c = other.variable
            self.factor = a*b
            if c is not None:
                if self.variable is None:
                    if self.unknown_is is None:
                        self.unknown_is = "Factor" # This must be a FACTOR!!!
                        self.variable = c
                    else:
                        raise NameError("Arithmetics: We can only allow Linear constraints! Take care with Variables!")
                else:
                        raise NameError("Arithmetics: We can only allow Linear constraints! Take care with Variables!")
        elif other.unknown:
            self.unknown = True
            if self.variable is not None: self.unknown_is = "Factor"
            self.value = other.value
            a = self.factor
            b = other.factor
            c = other.variable
            self.factor = a*b
            if c is not None:
                if self.variable is None:
                    if self.unknown_is is None:
                        self.unknown_is = "Factor" # This must be a FACTOR!!!
                        self.variable = c
                    else:
                        raise NameError("Arithmetics: We can only allow Linear constraints! Take care with Variables!")            
                else:
                    raise NameError("Arithmetics: We can only allow Linear constraints! Take care with Variables!")
        elif self.variable is None:
            self.factor *= other.factor
            if other.variable is not None:
                self.variable = other.variable
        else:
            if other.variable is None:
                self.factor *= other.factor #== other.factor???
            else:
                raise NameError("Arithmetics: We can only allow Linear constraints!")
        self.negation ^= other.negation # XOR
        return self
    
    # This will only return true if we are sure that we can divide
    def dividable(self,other):
        if other.variable is not None or self.unknown or other.unknown: return False
        a = self.factor
        b = other.factor
        return float(a) / float(b) == int(a)/int(b)
    
    # This will only return true if there might be a way to express the division
    def dividable_by_any_chance(self,other):
        return other.variable is None
    
    def divide(self, other):
        if other.__class__ is not arithmetic_atom: raise NameError("Arithmetics: Found wrong object for division!")
        if other.variable is not None: 
            if self.variable == other.variable: # 123*a / ( 321*a ) == 123/321 (if "a" is a variable) 
                self.variable = None
                self.factor /= other.factor
                return self
            else:
                raise NameError("Arithmetics: Division using linear constraints cannot be done using variables!")
        if self.unknown or other.unknown:
            raise NameError("Arithmetics: Our current version requires a clear distinction between fluents and numbers for division!")
        a = self.factor
        b = other.factor
        #if float(a) / float(b) == a/b:
        self.factor = a/b
        
        self.negation ^= other.negation # XOR
        return self
    
    def is_one(self):
        return self.variable is None and not self.unknown and \
            ((int(self.factor) == 1 and not self.negation) \
                or ((int(self.factor) == -1 and self.negation)))
        
    def is_zero(self):
        return int(self.factor) == 0
            
    def __str__(self):
        if self.value is None and self.variable is None:
            return "("+str(self.factor)+")"
        return "("+str(self.variable)+("'" if self.apostroph else "")+"*"+("-" if self.negation else "")+(str(self.value) if self.value is not None else "1")+")"
    
    def print_facts(self, prime=False):
        addition = ""
        if self.law_part in ["if","ifcons","body"]: # Adding time step
            addition = ",0"
        elif self.law_part == "after":
            addition = ",-1"
        if self.unknown: # If we do not know is a variable is a fluent, we let asp handle it.
            if self.variable is not None:
                return "_unknown,"+self.variable+","+((self.value+",") if self.value is not None else "")+("-" if self.negation else "")+str(int(self.factor))+","+str(self.helper_id)+addition
            else:
                return "_unknown,"+self.value+","+("-" if self.negation else "")+str(int(self.factor))+","+str(self.helper_id)+addition
        elif self.variable is not None:
            return self.variable+","+("-" if self.negation else "")+str(int(self.factor))+","+str(self.helper_id)+addition
        else:
            # Invert negation here: A single number will be written on the other side of the equation
            #return ("-" if not self.negation else "")+str(int(self.factor))
            return ("-" if self.negation else "")+str(int(self.factor)) ###+","+str(self.helper_id)
        
    def replace_unbound_variables(self,assignm,negate=False):
        if self.value is not None:
            for (x,y,after) in assignm:
                if str(self.value) == str(y):
                    self.value = None
                    self.variable = x.content
                    if after != negate: self.apostroph = not self.apostroph
                    break
        return self
        
class arithmetic_helper_division(parse_object):
    def __init__(self,variable,lunknown,factor,runknown,iseq,where):
        parse_object.__init__(self)
        self.value = variable
        self.value_u = lunknown
        self.divideby = factor
        self.divideby_u = runknown
        self.iseq = iseq
        self.where = where
        
    def print_facts(self, prime=False):
        wherepart = self.compile_where()
        result = "arithmetic_helper_division("+self.value + \
            ","+((str(int(self.value_u))) if self.value_u is not None else "1") + \
            ","+str(int(self.divideby))+ \
            ","+((str(int(self.divideby_u))) if self.divideby_u is not None else "1") + \
            ","+self.iseq+")"+wherepart+"."
        return result

class equation(parse_object):
    def __init__(self, left, right, operator="="):
        parse_object.__init__(self)
        self.left = left
        self.right = right
        self.operator = operator
        self.child_attributes = ["left","right"]
        self.has_integer = False
        self.replacement = None
        self.replaced_law = None
        self.is_arithmetic_helper = False
        self.is_in_where = False # Needed for simplify
        
    def __str__(self):
        return str(self.left)+str(self.operator)+str(self.right)
    
    def typestr(self):
        left = self.left.typestr() if hasattr(self.left, "typestr") else str(type(self.left).__name__)
        right = self.right.typestr() if hasattr(self.right, "typestr") else str(type(self.right).__name__)
        return "equation("+left+","+self.operator+","+right+")"
        #return "equation("+self.left.typestr()+","+self.operator+","+self.right.typestr()+")"
        
    def print_facts(self,prime=False):
        #wherepart = self.compile_where()
        if not prime:
            return str(self)

        if type(self.right) in [unknown,predicate,str,variable]:
            if self.operator in ["=","=="]:
                return "val("+str(self.left)+","+str(self.right)+")"
        
        raise NameError("Internal Error! An equation is printed in a way it should not. It should be replaced instead...")
        #return "val(_arithmetic("+str(self.law_id)+","+str(not self.negation).lower()+"))"#true))"
        
    def get_fluents_domains(self):
        if self.operator in ["=","=="]: #":=" ?
            return [domain(self.left,self.right),]
        else:
            return None
        
    def pass_down_update(self,update):
        if self.is_arithmetic_helper:
            return []
        
        self.is_in_where = update.where
        update.set("has_integer",False)
        update.reset_unbound_variables()
        simple=False
        
        
        if self.operator in ["="] and \
            self.left.__class__ in [unknown, variable, predicate] \
            and self.right.__class__ in [str,unknown,variable]:
                simple=True
        
        if type(self.left) != str:
            update.path_inc(self,"left")
            variables = self.left.pass_down_update(update)
            update.path_dec()
            for v in variables:
                if not v in self.variables:
                    self.variables.append(v)
                
        if update.get("has_integer"): simple=False
        
        if type(self.right) != str:
            update.path_inc(self,"right")
            if simple: update.set("fluent equation head",True)
            variables = self.right.pass_down_update(update)
            if simple: update.set("fluent equation head",None)
            update.path_dec()
            for v in variables:
                if not v in self.variables:
                    self.variables.append(v)
        
        if len(update.unbound_variables)>0: # Variable of law not bound in where part
            #    pass           
            #else:
            if self.operator in ["="]: # Variables are removed from the indexes of laws.
                if self.left.__class__ in [unknown, predicate] \
                and self.right.__class__ == variable:
                    #print "p/u = v"
                    for inte in update.integers:
                        if self.left.compare_to(inte):
                            if update.is_in_head():
                                self.replace_unbound_variables(update.unbound_assignment)
                            update.add_unbound_assignment((self.left,self.right))
                            break
                if self.left.__class__ == variable \
                and self.right.__class__ in [unknown,predicate]:
                    #print "v = p/u"
                    for inte in update.integers:
                        if self.right.compare_to(inte):
                            if update.is_in_head():
                                self.replace_unbound_variables(update.unbound_assignment)
                            update.add_unbound_assignment((self.right,self.left))
                            break
            # is equation? |bound| > 1
            # ignore for now
            # is assignment? |bound| == 1
            #print update.unbound_variables
        if type(self.left) == unknown and type(self.right) == variable and self.right.unbound == True:
            #print str(self.left) + str(self.operator) + str(self.right)
            #update.set()
            #update.
            pass
        
        
        if clingo_arithmetics:
            # HEAD := BODY
            # split to HEAD=_X , BODY_1=_Y, BODY_2=_Z # That's a bad encoding...
            # replace self with assignment(Head=_X)
            self.replacement = True
            
                
            
            # Get head fluents
            
            if type(self.left) == str:
                head_leaf = self.left
            else:
                head_leaf = self.left.get_bottom_elements()
            if type(self.right) == str:
                body_leaf = self.right
            else:
                body_leaf = self.right.get_bottom_elements()
            
            # Replace multivalued fluent statements directly (e.g. f=10 ) 
            if self.operator == "=":
                if type(body_leaf) == str:
                    if type(self.left) == negation:
                        if type(self.right) == str:
                            value = "-"+self.right
                        else:
                            value = negation(self.right)
                        self.replacement=assignment(self.left.content,value)
                        domain_statement = fluent(self.left.content,domainelement=value) #TODO: Only for relevant parts!!!
                        update.add_to_where(domain_statement) #TODO: Only for relevant parts!!!
                    else:
                        self.replacement=assignment(self.left,self.right)
                        domain_statement = fluent(self.left.content,domainelement=self.right) #TODO: Only for relevant parts!!!
                        update.add_to_where(domain_statement) #TODO: Only for relevant parts!!!
                    return self.variables
                if type(body_leaf) == list and len(body_leaf)==1:
                    if type(self.left) == negation:
                        if type(self.right) == str:
                            value = "-"+self.right
                        else:
                            value = negation(self.right)
                        self.replacement=assignment(self.left.content,value)
                        domain_statement = fluent(self.left.content,domainelement=value) #TODO: Only for relevant parts!!!
                        update.add_to_where(domain_statement) #TODO: Only for relevant parts!!!
                    else:
                        self.replacement=assignment(self.left,self.right)
                        domain_statement = fluent(self.left.content,domainelement=self.right) #TODO: Only for relevant parts!!!
                        update.add_to_where(domain_statement) #TODO: Only for relevant parts!!!
                    return self.variables
                
            if type(body_leaf) == str:
                body_leaf = [body_leaf,]
            if type(head_leaf) == str:
                head_leaf = [head_leaf,]
            
            replacements = {}
            for x in head_leaf:
                if type(x) != str:
                    varn = "_VAR_"
                    if x.apostroph:
                        varn += "PAST_"
                    varn += str(x)
                    replacements[x] = varn
                    if not varn in self.variables:
                        self.variables.append(varn)
                
            for x in body_leaf:
                if type(x) != str:
                    varn = "_VAR_"
                    if x.apostroph:
                        varn += "PAST_"
                    varn += str(x)
                    replacements[x] = varn
                    if not varn in self.variables:
                        self.variables.append(varn)
            
            # generate new assignments
            lawpart = update.get_law_part()
            if lawpart == "head":
                bodypart = "body"
            else:
                bodypart = lawpart

            for x in head_leaf:
                if type(x) != str:
                    y = copy.deepcopy(x)
                    repl = variable(replacements[x])
                    x.content = repl # Replace fluent, will be used for moving the law to the where part
                    update.add_where_arithmetic(self,self,assignment(y,repl),lawpart)
                    domain_statement = fluent(y,domainelement=repl)
                    update.add_to_where(domain_statement)
            for x in body_leaf:
                if type(x) != str:
                    y = copy.deepcopy(x)
                    repl = variable(replacements[x])
                    x.content = repl # Replace fluent, will be used for moving the law to the where part
                    domain_statement = fluent(y,domainelement=repl)
                    update.add_to_where(domain_statement)
                    if y.apostroph:
                        update.add_where_arithmetic(self,self,assignment(y,repl),"after")
                    else:
                        update.add_where_arithmetic(self,self,assignment(y,repl),bodypart)
                    
            # Add Law with replaced variables to where part!
            
            
            my_where_arithmetic = equation(self.left,self.right,self.operator)
            #my_where_arithmetic = equation(self.head,self.body,self.operator)
            update.add_to_where(my_where_arithmetic)

        # Replace equations using substitution laws
        elif  not self.operator == ".." and ( \
            update.get("has_integer") or (not simple) \
            and ( not update.where or \
            (len(update.indir_bound_int_var) > 0 and update.can_replace_where_arithmetic()))): #rewrite to arithmetic(X)
            
            for elem in update.indir_bound_int_var:
                if elem[2] == self:
                    self.replacement = True # We will replace this element, since it contains an unbound varialbe.
                    return []               # ^- The replacement will be done in the pass_down_update_overwrite function of the law, not here (check there if there are any errors)!
            
            self.has_integer = True
            self.my_id = update.arith_idfunction()
            self.replacement = predicate("_arithmetic",atom_list(predicate("law",atom_list(str(self.my_id),self.variables))))
            my_assignment = update.is_in_head()
            dynamic_law_part = update.is_in_dynamic_law()

            # Create a flat structure from our arithmetics.
            if type(self.left) == str: le = [arithmetic_atom(self.left,update.arith_helper_idfunction()),]
            else:
                le = self.left.arith_flatten(negation=False,update=update)
                if type(le) is not list: le = [le,]
            if type(self.right) == str: ri = [arithmetic_atom(self.right,update.arith_helper_idfunction()),]
            else:
                ri = self.right.arith_flatten(negation=False,update=update)#True) #The right part is negates
                if type(ri) is not list: ri = [ri,]
            # This part summarizes the single numbers
            
            ri = [x for x in ri if x is not None] # remove all Nones from list
            le = [x for x in le if x is not None]
            
            #law_part=update.get_law_part()
            val = None
            head = []
            body = []
            occurrences = []
            for l in le: # Replaces variables with the fluents.
                #l.law_part = law_part
                if l.has_no_variable():
                    if val is None: val = l
                    else: val.add(l)
                else:
                    for elem in update.indir_bound_int_var: 
                        if str(l.value) == str(elem[1]):
                            l.value = None
                            l.variable = str(elem[0])
                            l.law_part = elem[3]
                            if not elem[3] in occurrences:
                                occurrences.append(elem[3])
                            l.unknown = False
                            l.unknown_is = None
                            if l.law_part == "after":
                                body.append(l)
                                l.apostroph = True
                            elif l.law_part == "ifcons":
                                body.append(l)
                                l.is_ifcons = True
                            elif l.law_part == "head":
                                head.append(l)
                                my_assignment = True
                            else:
                                body.append(l)    
                            break
                    else:
                        head.append(l)
            for r in ri:
                #r.law_part = law_part
                if r.has_no_variable():
                    if val is None: val = r
                    else: val.add(r)
                else:
                    
                    for elem in update.indir_bound_int_var: 
                        if str(r.value) == str(elem[1]):
                            r.value = None
                            r.variable = str(elem[0])
                            r.law_part = elem[3]
                            if not elem[3] in occurrences:
                                occurrences.append(elem[3])
                            r.unknown = False
                            r.unknown_is = None
                            r.negate()
                            if r.law_part == "after":
                                body.append(r)
                                r.apostroph = True
                            elif r.law_part == "ifcons":
                                body.append(r)
                                r.is_ifcons = True
                            elif r.law_part == "head":
                                head.append(r)
                                my_assignment = True
                            else:
                                body.append(r)                                
                            break
                    else:
                        r.negate() # These are moved from the right side to the left... therefore negated
                        body.append(r)
            if val is not None:
                body.append(val)
            #print " ".join(x.print_facts() for x in head)
            #print " ".join(x.print_facts() for x in body)
            
            # If we are in the where part, equations are replaced (update is used to keep track and add it to the law)
            if update.where:
                arithmetic_law_placement = "if"
                if "head" in occurrences:
                    arithmetic_law_placement = "head"
                elif "ifcons" in occurrences and not "if" in occurrences and not "after" in occurrences:
                    arithmetic_law_placement = "ifcons"
                    
                self.replaced_law = arithmetic_law(head,body,self.operator,self.my_id,my_assignment,dynamic_law_part,self.variables,update.get_where())#self.get_where())
                self.replaced_law.binding = self.binding
                
                update.add_arithmetic_law(self.replaced_law)
                update.add_where_arithmetic(self,self.replaced_law,self.replacement,arithmetic_law_placement)
                self.replacement = True
            else: # This is replaced by a fact if not in where
                self.replaced_law = arithmetic_law(head,body,self.operator,self.my_id,my_assignment,dynamic_law_part,self.variables,update.get_where())#self.get_where())
                self.replaced_law.binding = self.binding
                
                update.add_arithmetic_law(self.replaced_law)
                
        #Code for adding binding to where part! 
        if self.binding is not None:
            #update.add_to_where(self.binding)
            variables = self.binding.get_variables()
            for v in variables:
                if str(v) in self.variables:
                    self.variables.remove(str(v))
            pass
        
        return self.variables

    def compile_where_single(self):
        if self.is_arithmetic_helper: return None
        return self.print_facts()
        
    def simplify(self, negation=False,in_where=False):
        if self.is_arithmetic_helper: # These helpers are removed for the translation
            return None
        if type(self.replacement) == bool and self.replacement==True:
            return None 
        if self.replacement is not None:
            #print "rep:",self.replacement
            return self.replacement.simplify(negation,in_where)
        if not in_where and not self.is_in_where and type(self.left) in [variable,unknown,predicate,str] and self.operator in ["=","=="]:
            if self.right == "<true>": #in ["<true>","true"] : 
                result = fluent(self.left,not negation)
                result.binding = self.binding
                return result
            if self.right == "<false>": #in ["<false>","false"] : 
                result = fluent(self.left,negation)
                result.binding = self.binding
                return result
            inner = assignment(self.left,self.right,negation)
            inner.binding = self.binding
            return inner.simplify(negation,in_where)
        #return parse_object.simplify(self, negation=negation)
        if negation:
            if self.operator in ["=","=="]: self.operator = "!="
            elif self.operator == "<": self.operator = ">="
            elif self.operator == ">": self.operator = "<="
            elif self.operator == "<=": self.operator = ">"
            elif self.operator == ">=": self.operator = "<"
            elif self.operator == "!=": self.operator = "="
            else:
                raise NameError("Unknown Equation Symbol "+self.operator)
        #print "rep:",self
        return self
    
    def replace_unbound_variables(self,assignment,negate=False):
        #self.left = self.left.replace_unbound_variables(assignment,negate)
        #self.right = self.right.replace_unbound_variables(assignment,negate)
        if self.replacement is not None and type(self.replacement) != bool:
            for co in self.replacement.parameters.content:
                con = co.parameters.content
                repl = []
                for c in con:
                    found = False
                    # (x,y,after)
                    for (_,y,_) in assignment:
                        if str(c) == str(y):
                            found = True
                            break
                    if not found: repl.append(c)
                co.parameters.content=repl
        if self.replaced_law is not None:
            #print type(self.replaced_law)
            self.replaced_law.replace_unbound_variables(assignment,negate)
        #print "repl:",self
        return self

    # we overwrite this method and see only variables as bound,
    # when there is just a single one.
    def get_variables(self,checkbound=False):
        my_vars = []
        ch = self.get_children()
        for c in ch:
            if c is None or type(c) == str: continue
            vs = c.get_variables(checkbound)
            if type(vs) == list:
                my_vars += vs
            else:
                my_vars.append(vs)
        if checkbound and len(my_vars) > 1: return [] 
        return my_vars

class equation_where_arithmetics(parse_object):
    def __init__(self, arith_list):
        parse_object.__init__(self)
        self.arith_list = arith_list
        self.head = None
        self.body = None
        self.ifcons = None
        
        self.head_atom = None
        
        self.child_attributes = ["arith_list"]
        self.has_integer = False
        self.replacement = None
        self.replaced_law = None
        
        self.is_assignment = False
        
    def __str__(self):
        if self.head_atom is None:
            return str()
        else:
            return str(self.head_atom)+":="+str(self.right)
    
    def typestr(self):
        return "equation_arith("+str(self.arith_list)+")"
        #return "equation("+self.left.typestr()+","+self.operator+","+self.right.typestr()+")"
        
    def print_facts(self,prime=False):
        wherepart = self.compile_where()
        result = []
        stid = "law("+','.join([str(self.my_id)]+self.variables)+")"
        if self.is_assignment:
            if self.is_dynamic_law_part:
                result.append("arithmetic_assignment_dynamic("+stid+")"+wherepart+".")
            else:
                result.append("arithmetic_assignment("+stid+")"+wherepart+".")
        result.append("arithmetic_law("+stid+",eq)"+wherepart+".")
        
        inverse_apostroph = additional_ifcons_facts
        # This was used to express that ' is t-1 and ' in the head inverses the meaning of ' to t
            
        if self.head is not None:    
            if self.is_assignment:
                for e in self.head:
                    #try:
                    #    if e.apostroph: inverse_apostroph = True
                    #except:
                    #    pass
                    result.append("arithmetic_head("+stid+","+e.print_facts()+")"+wherepart+".")
            else:
                for e in self.head:
                    result.append("arithmetic("+stid+","+e.print_facts()+",0)"+wherepart+".")
        
        if old_arithmetics: inverse_apostroph = not inverse_apostroph 
        # In old arithmetics, it was the other way...
        # But there were also no apostroph's
        
        if self.body is not None:
            for e in self.body:
                try:
                    if e.variable is None and not e.unknown:
                        result.append("arithmetic("+stid+","+e.print_facts()+")"+wherepart+".")
                    elif e.apostroph != inverse_apostroph:
                        if self.is_dynamic_law_part:
                            result.append("arithmetic("+stid+","+e.print_facts()+",-1)"+wherepart+".")
                        else:
                            result.append("arithmetic("+stid+","+e.print_facts()+",0)"+wherepart+".")
                    else: 
                        result.append("arithmetic("+stid+","+e.print_facts()+",0)"+wherepart+".")
                        if additional_ifcons_facts: result.append("arithmetic_ifcons("+stid+","+e.print_facts()+")"+wherepart+".") #new for ifcons!
                except:
                    result.append("arithmetic("+stid+","+e.print_facts()+",0)"+wherepart+".")
            
        return result
    
    def get_fluents_domains(self):
        if self.head_atom is None:
            return None
        else:
            return [domain(self.head_atom),]
        
    def pass_down_update(self,update):
        
        self.my_id = update.arith_idfunction()
        
        return []
        
        if self.is_arithmetic_helper:
            return []
        
        update.set("has_integer",False)
        update.reset_unbound_variables()
        simple=False
        
        if self.operator in ["="] and \
            self.left.__class__ in [unknown, variable, predicate] \
            and self.right.__class__ in [str,unknown,variable]:
                simple=True
        
        if type(self.left) != str:
            update.path_inc(self,"left")
            variables = self.left.pass_down_update(update)
            update.path_dec()
            for v in variables:
                if not v in self.variables:
                    self.variables.append(v)
                
        if update.get("has_integer"): simple=False
        
        if type(self.right) != str:
            update.path_inc(self,"right")
            if simple: update.set("fluent equation head",True)
            variables = self.right.pass_down_update(update)
            if simple: update.set("fluent equation head",None)
            update.path_dec()
            for v in variables:
                if not v in self.variables:
                    self.variables.append(v)
        
        if len(update.unbound_variables)>0:
            if update.is_in_head():
                #print "head"
                #self.replace_unbound_variables(update.unbound_assignment)
                pass           
            else:
                if self.operator in ["="]:
                    if self.left.__class__ in [unknown, predicate] \
                    and self.right.__class__ == variable:
                        #print "p/u = v"
                        update.add_unbound_assignment((self.left,self.right))
                    if self.left.__class__ == variable \
                    and self.right.__class__ in [unknown,predicate]:
                        #print "v = p/u"
                        update.add_unbound_assignment((self.right,self.left))
                # Equations with multiple unbound variables will be handled later.
                # We need at least on of these to somehow bind variables (no, we will not do fancy stuff)
        if type(self.left) == unknown and type(self.right) == variable and self.right.unbound == True:
            #print str(self.left) + str(self.operator) + str(self.right)
            #update.set()
            #update.
            pass


        if update.get("has_integer") or (not simple and not update.where): #rewrite to arithmetic(X)
            self.has_integer = True
            self.my_id = update.arith_idfunction()
            self.replacement = predicate("_arithmetic",atom_list(predicate("law",atom_list(str(self.my_id),self.variables))))
            assignment = update.is_in_head()
            dynamic_law_part = update.is_in_dynamic_law()

            # Create a flat structure of our arithmetics
            if type(self.left) == str: le = [arithmetic_atom(self.left,update.arith_helper_idfunction()),]
            else:
                le = self.left.arith_flatten(negation=False,update=update)
                if type(le) is not list: le = [le,]
            if type(self.right) == str: ri = [arithmetic_atom(self.right,update.arith_helper_idfunction()),]
            else:
                ri = self.right.arith_flatten(negation=False,update=update)#True) #The right part is negates
                if type(ri) is not list: ri = [ri,]
            # This part summarizes the single numbers
            
            ri = [x for x in ri if x is not None] # remove all Nones from list
            le = [x for x in le if x is not None]
            
            val = None
            head = []
            body = []
            for l in le:
                if l.has_no_variable():
                    if val is None: val = l
                    else: val.add(l)
                else:
                    head.append(l)
            for r in ri:
                if r.has_no_variable():
                    if val is None: val = r
                    else: val.add(r)
                else:
                    r.negate() # These are moved from the right side to the left... therefore negated
                    body.append(r)
            if val is not None:
                body.append(val)
            #print " ".join(x.print_facts() for x in head)
            #print " ".join(x.print_facts() for x in body)
            
            self.replaced_law = arithmetic_law(head,body,self.operator,self.my_id,assignment,dynamic_law_part,self.variables,update.get_where())#self.get_where())
            self.replaced_law.binding = self.binding
            update.add_arithmetic_law(self.replaced_law)
            
        #Code for adding binding to where part! 
        if self.binding is not None:
            #update.add_to_where(self.binding)
            variables = self.binding.get_variables()
            for v in variables:
                if str(v) in self.variables:
                    self.variables.remove(str(v))
            pass
        
        return self.variables

    def compile_where_single(self):
        return self.print_facts()
        
    def simplify(self, negation=False,in_where=False):
        if self.replacement is not None:
            #print "rep:",self.replacement
            return self.replacement.simplify(negation,in_where)
        return self
    
        
class operation(parse_object):
    def __init__(self, left, right, operator="+"):
        parse_object.__init__(self)
        self.left = left
        self.right = right
        self.operator = operator
        self.child_attributes = ["left","right"]
        
    def __str__(self):
        return str(self.left)+str(self.operator)+str(self.right)
    
    def typestr(self):
        if type(self.left) == str: le = self.left
        else: le = self.left.typestr()
        if type(self.right) == str: re = self.right
        else: re = self.right.typestr()
        #return "operation("+le+","+self.operator+","+re+")"
        return "("+le+","+self.operator+","+re+")"
    
    def print_facts(self,prime=False):
        if type(self.left) == str: le = self.left
        else: le = self.left.print_facts()
        if type(self.right) == str: re = self.right
        else: re = self.right.print_facts()

        return le+self.operator+re
        
        #return str(self)
    
    def arith_flatten(self,negation,update):
        if type(self.left) == str: le = arithmetic_atom(self.left,update.arith_helper_idfunction(),negation)
        else: le = self.left.arith_flatten(negation,update)
        
        if self.operator == "-":
            negation = not negation
        elif self.operator == "*":
            negation = False
        
        if type(self.right) == str: ri = arithmetic_atom(self.right,update.arith_helper_idfunction(),negation)
        else: ri = self.right.arith_flatten(negation,update)
        
        if self.operator in ["+","-"]:
            result = []
            if type(le) == list: result += le
            else: result.append(le)
            if type(ri) == list: result += ri
            else: result.append(ri)
            return result
        elif self.operator == "*":
            if type(le) == arithmetic_atom and type(ri) == arithmetic_atom:
                le.multiply(ri)
            else:
                raise NameError("Error: Linear Constraints; A multiplication cannot be used here!")
            return le
        elif self.operator == "/":
            #print le.print_facts(),"/",ri.print_facts()
            if type(ri) == arithmetic_atom and ri.is_zero():
                raise NameError("Error: Don't even try to divide by zero. That does not work... never.")
            if type(ri) == arithmetic_atom and ri.is_one():
                return le
            if type(le) == arithmetic_atom and le.dividable(ri):
                le.divide(ri)
                return le
            elif type(le) == arithmetic_atom and le.dividable_by_any_chance(ri):
                return self.generate_arithmetic_helper(le,ri,update)
            else:
                raise NameError("Error: Linear Constraints; Division cannot be simplified in this case!")
        else: 
            raise NameError("Error: Linear Constraints; Operatior "+self.operator+" cannot be used here!")

    def generate_arithmetic_helper(self,l,r,update):
        helper = update.get("arithmetic_divisions")
        if helper is None: helper = []
        if type(l) == arithmetic_atom and type(r) == arithmetic_atom:
            helper_elements = []
            variable = l.variable
            lunknown = l.value
            # Not asking for r.variable, since that won't be possible.
            factor = r.factor
            runknown = r.value
            unkn = l.unknown or r.unknown or len(l.variables) > 0 or len(r.variables) > 0
            
            helper_elements = [variable]
            if l.unknown and lunknown is not None: helper_elements += [lunknown]
            helper_elements += [str(int(factor))]
            if r.unknown and runknown  is not None: helper_elements += [runknown]
            
            # hlp = "_division_helper("+",".join(helper_elements)+")" # Clingcon does not like _
            hlp = "division_helper("+",".join(helper_elements)+")"
            if not unkn:
                res = arithmetic_helper_division(variable,lunknown,factor,runknown,hlp,None)
            else:
                res = arithmetic_helper_division(variable,lunknown,factor,runknown,hlp,update.where_part)
            helper.append(res)
            
            l.unknown = False
            l.variable = hlp
            l.negation ^= r.negation
            update.set("arithmetic_divisions",helper)
            return l
        return None

class assignment(parse_object):
    def __init__(self, head, body, negated = False):
        parse_object.__init__(self)
        self.head = head
        self.body = body
        if type(body) == operation:
            self.complex_calculation = True
        else:
            self.complex_calculation = False
        #print body.typestr(),":",body,self.complex_calculation
        self.negated = negated
        self.child_attributes = ["head","body"]
        self.replacement = None
        self.replacement_name = "_arithmetic"
        self.where_variables = []
        
    def __str__(self):
        return ("not " if self.negated else "")+str(self.head)+"="+str(self.body)
    
    def typestr(self):
        head = self.head.typestr() if type(self.head) != str else "str"
        body = self.body.typestr() if type(self.body) != str else "str"
        return "assignment("+head+","+body+")"
    
    def get_domain(self):
        return self.body

    def print_facts(self,prime=False):
        #wherepart = self.compile_where()
        if not prime:
            if self.negated:
                raise NameError("Negated fact has no *simple* form")
            return str(self.head)

        if type(self.head) == str:
            head = self.head
        else:
            head = self.head.print_facts()
        if type(self.body) == str:
            body = self.body
        else:
            body = self.body.print_facts()
            
        if self.negated:
            return "neg_val("+head+","+body+")"
        else:
            return "val("+head+","+body+")"

    def pass_down_update(self,update):
        if update.had_where:
            self.where_variables = update.where_variables # Required for additive fluents (incremental assignments)
        
        update.set("has_integer",False)
        if type(self.head) != str:
            update.path_inc(self,"head")
            variables = self.head.pass_down_update(update)
            update.path_dec()
            for v in variables:
                if not v in self.variables:
                    self.variables.append(v)
        is_arithmetic_assignment = False
        if update.get("has_integer"):
            is_arithmetic_assignment = True
            
        if type(self.body) != str:
            update.path_inc(self,"body")
            variables = self.body.pass_down_update(update)
            update.path_dec()
            for v in variables:
                if not v in self.variables:
                    self.variables.append(v)

        if is_arithmetic_assignment:
            if clingo_arithmetics:
                # HEAD := BODY
                # split to HEAD=_X , BODY_1=_Y, BODY_2=_Z # That's a bad encoding...
                # replace self with assignment(Head=_X)
                self.replacement = True
                
                # Get head fluents
                
                try:
                    head_leaf = self.head.get_bottom_elements()
                    body_leaf = self.body.get_bottom_elements()
                except Exception:
                    self.replacement = None
                    return self.variables
                
                # generate variables
                
                replacements = {}
                for x in head_leaf:
                    varn = "_VAR_"
                    if x.apostroph:
                        varn += "PAST_"
                    varn += str(x)
                    replacements[x] = varn
                    if not varn in self.variables:
                        self.variables.append(varn)
                    
                for x in body_leaf:
                    varn = "_VAR_"
                    if x.apostroph:
                        varn += "PAST_"
                    varn += str(x)
                    replacements[x] = varn
                    if not varn in self.variables:
                        self.variables.append(varn)
                
                # generate new assignments

                for x in head_leaf:
                    y = copy.deepcopy(x)
                    repl = variable(replacements[x])
                    x.content = repl # Replace fluent, will be used for moving the law to the where part
                    update.add_where_arithmetic(self,self,assignment(y,repl),"head")
                    domain_statement = fluent(y,domainelement=repl)
                    update.add_to_where(domain_statement)
                for x in body_leaf:
                    y = copy.deepcopy(x)
                    repl = variable(replacements[x])
                    x.content = repl # Replace fluent, will be used for moving the law to the where part
                    domain_statement = fluent(y,domainelement=repl)
                    update.add_to_where(domain_statement)
                    if y.apostroph:
                        update.add_where_arithmetic(self,self,assignment(y,repl),"after")
                    else:
                        update.add_where_arithmetic(self,self,assignment(y,repl),"body")
                        
                # Add Law with replaced variables to where part!
                
                
                
                my_where_arithmetic = equation(self.head,self.body,"=")
                update.add_to_where(my_where_arithmetic)
                
            else:
                self.has_integer = True
                self.my_id = update.arith_idfunction()
                self.replacement = self.create_replacement()
                has_assignment = update.is_in_head()
                if not has_assignment:
                    print >> sys.stderr, "Error: Assignment in Body!"
                    errout.error("Error: Assignment in Body!")
                dynamic_law_part = update.is_in_dynamic_law(check_default_laws=True)
                if type(self.head) == str: le = [arithmetic_atom(self.head,update.arith_helper_idfunction()),]
                else:
                    le = self.head.arith_flatten(negation=False,update=update)
                    if type(le) is not list: le = [le,]
                if type(self.body) == str: ri = [arithmetic_atom(self.body,update.arith_helper_idfunction()),]
                else:
                    ri = self.body.arith_flatten(negation=False,update=update)#True) #The right part is negates
                    if type(ri) is not list: ri = [ri,]
                # This part summarizes the single numbers
                val = None
                head = []
                body = []
                for l in le:
                    if l.has_no_variable():
                        if val is None: val = l
                        else: val.add(l)
                    else:
                        head.append(l)
                for r in ri:
                    if r.has_no_variable():
                        if val is None: val = r
                        else: val.add(r)
                    else:
                        r.negate() # These are moved from the right side to the left... therefore negated
                        body.append(r)
                if val is not None:
                    body.append(val)
                #print " ".join(x.print_facts() for x in head)
                #print " ".join(x.print_facts() for x in body)
                
                law = self.create_law(head,body,dynamic_law_part,update)
                law.binding = self.binding
                #arithmatic_law(head,body,"=",self.my_id,assignment,dynamic_law_part,self.variables,update.get_where())#self.get_where())
                update.add_arithmetic_law(law)
            
        #Code for adding binding to where part! 
        if self.binding is not None:
            #update.add_to_where(self.binding)
            variables = self.binding.get_variables()
            for v in variables:
                if str(v) in self.variables:
                    self.variables.remove(str(v))
            pass
        
        return self.variables
    
    def create_law(self,head,body,dynamic_law_part,update):
        return arithmetic_law(head,body,"=",self.my_id,assignment,dynamic_law_part,self.variables,update.get_where())#self.get_where())
    
    def create_replacement(self):
        return predicate(self.replacement_name,atom_list(predicate("law",atom_list(str(self.my_id),self.variables))))
    
    def simplify(self, negation=False,in_where=False,binding=None):
        if self.replacement is not None:
            if type(self.replacement) == bool and self.replacement==True:
                return None
            result = self.replacement.simplify(negation,in_where)
            if binding is not None:
                result.binding = binding
                if self.binding is not None:
                    result.binding += self.binding
            else:
                result.binding = self.binding
            return result
        if negation:
            self.negation = not self.negation
        return self

class incremental_assignment(assignment):
    
    def __init__(self, head, body, negated = False):
        assignment.__init__(self, head, body, negated)
        self.replacement_name = "_arithmetic" #"_additive_arithmetic"

    def typestr(self):
        head = self.head.typestr() if type(self.head) != str else "str"
        body = self.body.typestr() if type(self.body) != str else "str"
        return ("increment" if not self.negated else "decrement")+"("+head+","+body+")"
    
    def create_law(self,head,body,dynamic_law_part,update):
        var = self.variables
        for wv in self.where_variables:
            if not wv in var:
                var.append(wv)
        return arithmetic_additive_law(head,body,self.my_id,dynamic_law_part,var,update.get_where())#self.get_where())
    
    def create_replacement(self):
        var = self.variables
        for wv in self.where_variables:
            if not wv in var:
                var.append(wv)
        return predicate(self.replacement_name,atom_list(predicate("law",atom_list(str(self.my_id),var))))
    
# unknown may sound weird, but while parsing it, we don't know what this is.
# It may be a Fluent, Actions
class unknown(parse_object):
    def __init__(self, content, apostroph=False):
        parse_object.__init__(self)
        self.content = content
        self.type = "??"
        self.child_attributes = []#"content"
        self.apostroph = apostroph
        
    def __str__(self):
        return str(self.content) #+("'" if self.apostroph else "")
    
    def typestr(self):
        if type(self.content) == str: return self.type
        return self.type+"("+self.content.typestr()+")"
    
#     def get_fluents(self,simple=True):
#         self.type = "fluent"
#         #if type(self.content) == str: return self.content
#         #else: return self.content.get_fluents()
#         
#         #if simple: 
#         #    return self
#         #else:
#         #    return assignment(self,"true")
#         
#         return self
    
    def get_actions(self):
        self.type = "action"
        return self
    
    def get_bottom_elements(self):
        return [self,]
    
    def get_domain(self):
        if self.type == "fluent":
            return ["true","false"]
        else:
            return None
        
    def get_fluents_domains(self):
        self.type = "fluent" 
        return [domain(self,None),]
    
    def pass_down_update(self,update):#Dont use the .._overwrite here
        if not update.get("check"): return self.variables
        definite_type = False
        variables = self.variables
        if update.is_action_allowed():
            if self in update.actions:
                self.type = "action" 
                definite_type = True
                self.reference = self
        if self in update.fluents:
            if self.type == "action" and definite_type:
                raise NameError(str(self)+" cannot be defined as action and fluent!")
            self.type = "fluent" 
            definite_type = True
            self.reference = self
        if self in update.integer_ids:
            if self.type == "action" and definite_type:
                raise NameError(str(self)+" cannot be defined as fluent and action!")
            self.type = "integer" 
            update.set("has_integer",True)
            definite_type = True
            self.reference = self
            
        if update.had_where:
            had_act = False
            had_flu = False
            if update.is_action_allowed():
                for act in update.where_actions:
                    if self.compare_to(act):
                        self.reference = act
                        self.type = "action"
                        definite_type = True
                        had_act = True
                        break 
            for flu in update.where_fluents:
                if self.compare_to(flu):
                    self.reference = flu
                    self.type = "fluent"
                    definite_type = True
                    had_flu = True
                    break 
            if had_act and had_flu:
                print >> sys.stderr, "Error! "+str(self)+" is Fluent and Action at the same time"
                errout.error("Error! "+str(self)+" is Fluent and Action at the same time")
        
        if not definite_type:
            if update.is_action_allowed():
                for act in update.actions:
                    if self.compare_to(act):
                        self.reference = act
                        self.type = "action"
                        definite_type = True
                        break 
        if not definite_type:
            for flu in update.fluents:
                if self.compare_to(flu):
                    self.reference = flu
                    self.type = "fluent"
                    definite_type = True
                    break 
        if not definite_type:
            for inte in update.integer_ids:
                if self.compare_to(inte):# get a number for this law?
                    self.reference = inte
                    self.type = "integer"
                    update.set("has_integer",True)
                    definite_type = True
                    break 
        if update.where:
                self.type = "asp"
        elif not definite_type and update.get("fluent equation head") is not None:
            self.type = "str"
        elif not definite_type and self.type == "??":
            # Assume Fluent!
            if update.is_action_allowed():
                print >> sys.stderr, "% Warning: Cannot find "+str(self)+" in fluents or actions!"
                errout.error("% Warning: Cannot find "+str(self)+" in fluents or actions!")
            else:
                print >> sys.stderr, "% Warning: Cannot find "+str(self)+" in fluents!"
                errout.error("% Warning: Cannot find "+str(self)+" in fluents!")
            update.add_unbound_variables((self,self.variables))
            self.type = "fluent"
            
        return variables
    
    def print_facts(self,prime=False):
        #return self.print_facts_unknown(prime)
        st = str(self.content)
        if not prime: return st
        if self.type == "action":
            if self.negation: 
                print >> sys.stderr, "% Warning! Action "+str(self)+" is negated."
                errout.error("% Warning! Action "+str(self)+" is negated.")
            return "act("+st+")"
        elif self.type == "fluent":
            return "val("+st+","+str(not self.negation).lower()+")"
        else: 
            return st
    
    def print_facts_unknown(self,prime=False,equalpart="true"):
        #wherepart = self.compile_where()
        st = str(self.content)
        if not prime: return st
        if self.type == "action":
            return "act("+st+")"
        elif self.type == "fluent":
            return "val("+st+","+equalpart+")"
        else: 
            return st
        #result += self.type+"("+st+")"+wherepart+"."
        #return result
    
    def arith_flatten(self,negation,update):
        return arithmetic_atom(self.print_facts(),update.arith_helper_idfunction(),negation=negation,unknown=self.type!="integer",apostroph=self.apostroph)
    
    def compile_where_single(self):
        return self.print_facts()

class variable(parse_object):
    def __init__(self, content):
        parse_object.__init__(self)
        self.content = content
        self.type = "??" #This is an assumption!
        self.child_attributes = []#"content"
        self.unbound = None
        self.apostroph = False
        
    def __str__(self):
        return str(self.content)
    
    def typestr(self):
        if type(self.content) == str: 
            return "var"
        else: 
            return "var("+self.content.typestr()+")"
        
    def get_fluents_domains(self):
        self.type = "fluents"
        return [domain(self,None),]
    
    def pass_down_update(self,update):
        #where_binding = update.get("where_binding")
        if update.is_in_action_fact():
            self.type = "action"
            self.unbound = False
            return [str(self),]
        
        found = False
        if update.had_where: #where_binding is not None:
            fls = update.where_fluents #where_binding["fluents"]
            acs = update.where_actions #where_binding["actions"]
            ins = update.indir_bound_int_var
            assigned_fluent = False
            for x in fls:
                if str(self) == str(x):
                    self.type = "fluent"
                    found = True
                    assigned_fluent = True
                    self.unbound = False
                    break
            for x in acs:
                if str(self) == str(x):
                    if assigned_fluent:
                        print "% Warning! Variable "+str(self)+" could be a fluent or action!"
                    self.type = "action"
                    found = True
                    self.unbound = False
                    break
            for x in ins:
                if str(self) == str(x[1]):
                    self.type = "fluent" # integer!!
                    found = True
                    assigned_fluent = True
                    self.unbound = True
                    update.set("has_integer",True)
                    update.add_unbound_variables((self,str(self)))
                    return [] # This is not a bound variable 
            if self.type not in ["action","fluent"]:
                if not update.is_action_allowed():
                    self.type = "fluent"
                    #Doing an assumption
        else:
            for x in update.indir_bound_int_var: 
                if str(self) == str(x[1]):
                    self.type = "fluent" # integer!!
                    found = True
                    assigned_fluent = True
                    self.unbound = True
                    update.set("has_integer",True)
                    update.add_unbound_variables((self,str(self)))
                    return [] # This is not a bound variable 
        if not found and not update.where and not str(self) in update.where_variables:
            self.unbound = True
            update.add_unbound_variables((self,str(self)))
            # This may not be an error anymore
            #print >> sys.stderr, "% Warning! Variable "+str(self)+" is not bound in: "+str(update.law)+"!"
            #errout.error("% Warning! Variable "+str(self)+" is not bound in: "+str(update.law)+"!")
        return [str(self),]
    
    def print_facts(self,prime=False):
        if type(self.content) == str:
            my_str = self.content
        else:
            my_str = self.content.print_facts()
        if prime:
            if self.negation:
                return "val("+my_str+",false)"
            else:
                if self.type == "action":
                    return "act("+my_str+")"
                elif self.type == "fluent":
                    return "val("+my_str+",true)"
                else:
                    print >> sys.stderr, "% Warning!!! "+my_str+" could also be an action!"
                    errout.error("% Warning!!! "+my_str+" could also be an action!")
                    return "val("+my_str+",true)"
        return my_str
    
    def get_variables(self,checkbound=False):
        return self
    
    def get_explicitly_bound_variables(self,where=False,bound=False):
        if where and bound:
            return self
        else:
            return []

    def get_bottom_elements(self):
        return [self,]
    
    def arith_flatten(self,negation,update):
        return arithmetic_atom(self.print_facts(),update.arith_helper_idfunction(),negation)

    def replace_unbound_variables(self,assignm,negate=False):
        for (x,y,after) in assignm:
            if str(self.content) == str(y):
                if after: 
                    z = copy.deepcopy(x)
                    z.apostroph = not z.apostroph
                    return z
                return x
        return self
        
# This is a class that says that it's content is negated in the parse tree.
# This is always removed during the simplification process
class negation(parse_object):
    def __init__(self, content):
        parse_object.__init__(self)
        self.content = content
        self.child_attributes = ["content"]
        
    def __str__(self):
        return "not "+str(self.content)
    
    def typestr(self):
        if type(self.content) == str:
            return "-"+self.content
        return "neg("+self.content.typestr()+")"

    def print_facts(self,prime=False): # Ignore negation here, it is passed while updating.
        if type(self.content) == str:
            return self.content
        else:
            if type(self.content) is unknown:
                return self.content.print_facts_unknown(prime=True,equalpart="false")
            else:
                print >> sys.stderr, "Cannot negate "+str(self.content)
                errout.error("Cannot negate "+str(self.content))
                return self.content.print_facts()
                #return "val("+self.content.print_facts()+",false)"

    def simplify(self, negation=False,in_where=False):
        if self.content is None:
            return None
        if type(self.content) == str:
            return "not "+self.content
        if in_where:
            self.content = self.content.simplify(negation=negation,in_where=in_where)
            return self
        return self.content.simplify(negation=not negation,in_where=in_where)
    
    def compile_where_single(self):
        if self.content is None:
            return ""
        return "not "+self.content.print_facts()
    
    def arith_flatten(self,negation,update):
        return self.content.arith_flatten(not negation, update)

# Some asp code.
# We don't want to mess with that.
# We just print it as given.
# We wish you best luck and hope that you know what you are doing.
class asp_code(parse_object):
    def __init__(self,text):
        parse_object.__init__(self)
        self.text = text
        
    def __str__(self):
        return str(self.text)
    
    def typestr(self):
        return "asp"

class asp_dotted_fact(parse_object):
    def __init__(self,term,lower,upper):
        parse_object.__init__(self)
        self.term = term
        self.lower = lower
        self.upper = upper
        self.child_attributes = ["term","lower","upper"]
        
    def __str__(self):
        return str(self.term)+"="+str(self.lower)+".."+str(self.upper)
    
    def typestr(self):
        return str(self)
    
    def print_facts(self,prime=False):
        return str(self)
    
    def compile_where_single(self):
        return self.print_facts()

# This is the domain of a fluent (or integer)
class domain(parse_object):
    def __init__(self,fluent,values,where=None):
        parse_object.__init__(self)
        self.fluent = fluent
        if type(values) != list: 
            if values is None:
                self.values = ["true","false"]
            else:
                self.values = [values,]
        else: self.values = values
        self.where = where
        
    def __str__(self):
        result = ""
        wh = ""
        if self.where is not None:
            wh = self.compile_where()
        for x in self.values:
            result += "domain("+str(self.fluent)+","+str(x)+")"+wh+"."
        return result
    
    def print_facts(self,prime=False):
        result = []
        wh = ""
        if self.where is not None:
            wh = self.compile_where()
        for x in self.values:
            result.append("domain("+str(self.fluent)+","+str(x)+")"+wh+".")
        return result
    
    def typestr(self):
        return "domain("+self.fluent.typestr()+","+self.values.typestr()+")"
    
    def get_domain_fluent(self):
        return self.fluent

# This object is only used during the pass_down update
class update_passdown(object):
    def __init__(self, law=None, fluents=[], actions=[], integers=[], integer_ids=[], others={}, law_type = None):
        self.fluents = fluents
        self.actions = actions
        self.integers = integers
        self.integer_ids = integer_ids
        self.law = law
        self.law_type = law_type
        self.arithmetic_laws = []
        self.pass_up = {}
        self.where = False
        self.had_where = False
        self.where_part = None
        self.where_actions = []
        self.where_fluents = []
        self.where_variables = []
        self.unbound_variables = []
        self.unbound_assignment = []
        self.where_arithmetic = []
        self.where_additions = []
        self.indir_bound_int_var = []
        self.path = []
        self.integers_changed_to_fluents = []
        if type(others) == dict:
            self.others = others
        else:
            self.others = {'others':others}
            
    def get(self,val):
        if val in self.others:
            return self.others[val]
        else:
            return None
        
    def get_reset(self,val):
        if val in self.others:
            result = self.others[val]
            self.others[val] = False
            return result
        else:
            self.others[val] = False
            return False
        
    def set(self,key,val):
        self.others[key] = val
            
    def idfunction(self):
        if self.others["idfunction"] is not None:
            return self.others["idfunction"]()
        return None
    
    def arith_idfunction(self):
        if self.others["arith_idfunction"] is not None:
            return self.others["arith_idfunction"]()
        return None
    
    def arith_helper_idfunction(self):
        if self.others["arith_helper_idfunction"] is not None:
            return self.others["arith_helper_idfunction"]()
        return None
        
    def pass_up(self,context,passup_object):
        if context in self.pass_up:
            self.pass_up[context].append(passup_object)
        else:
            self.pass_up[context] = [passup_object,]
        
    def get_pass_up(self):
        return self.pass_up
    
    def path_inc(self,caller,att):
        self.path.append((caller,att))
        
    def get_path(self):
        return self.path
        
    def path_dec(self):
        self.path.pop()
        
    def is_in_head(self):
        if self.law_type == "goals": return False
        for ob in self.path:
            caller = ob[0]; att = ob[1]
            if att == "head" and law in inspect.getmro(caller.__class__):
                return True
        return False
    
    def is_in_body(self):
        for ob in self.path:
            caller = ob[0]; att = ob[1]
            if att in ["if_part","after_part","body"] and law in inspect.getmro(caller.__class__):
                return True
        return False
    
    def is_in_ifcons(self):
        for ob in self.path:
            caller = ob[0]; att = ob[1]
            if att == "ifcons_part" and law in inspect.getmro(caller.__class__):
                return True
        return False
    
    def is_in_dynamic_law(self,check_default_laws=False):
        for ob in self.path:
            caller = ob[0];
            if dynamic_law == caller.__class__:
                return True
            if dynamic_law in inspect.getmro(caller.__class__):
                return True
            if check_default_laws:
                if default_law == caller.__class__ or default_law in inspect.getmro(caller.__class__):
                    return caller.dynamic
        return False
    
    def is_in_action_fact(self):
        for ob in self.path:
            caller = ob[0];
            if action_fact == caller.__class__:
                return True
            if action_fact in inspect.getmro(caller.__class__):
                return True
        return False

    def is_action_allowed(self):
        for ob in self.path:
            caller = ob[0]
            func = ob[1];
            if action_fact == caller.__class__ or action_fact in inspect.getmro(caller.__class__):
                return True
            if dynamic_law == caller.__class__ or dynamic_law in inspect.getmro(caller.__class__):
                if func == "after_part": return True
            if nonexecutable_law == caller.__class__ or nonexecutable_law in inspect.getmro(caller.__class__):
                if func in ["body", "if_part"]: return True
        return False
    
    def can_replace_where_arithmetic(self):
        for ob in self.path: # + [(totest,"self")]:
            caller = ob[0]
            if caller.__class__ in [static_law,dynamic_law,default_law,impossible_law,inertial_law,nonexecutable_law]:
                return True
            else: 
                for x in inspect.getmro(caller.__class__):
                    if x in [static_law,dynamic_law,default_law,impossible_law,inertial_law,nonexecutable_law]:
                        return True
        return False
        
    def add_arithmetic_law(self,elem):
        self.arithmetic_laws.append(elem)
    
    def where_start(self,where_part):
        self.where_part = where_part
        self.where = True
        self.had_where = True
        
    def where_end(self):
        self.where = False
        
    def get_where(self):
        return self.where_part
        
    def add_where_fluent(self,elem):
        if not elem in self.where_fluents:
            self.where_fluents.append(elem)
    
    def add_where_action(self,elem):
        if not elem in self.where_actions:
            self.where_actions.append(elem)
    
    def add_to_where(self,elem):
        if self.where_part is not None:
            if not elem in self.where_part:
                self.where_part.append(elem)
        else:
            self.where_additions.append(elem)
    
    def add_unbound_variables(self,elem):
        if not elem in self.unbound_variables:
            self.unbound_variables.append(elem)
            
    def reset_unbound_variables(self):
        self.unbound_variables = []
    
    def add_unbound_assignment(self,elem):
        x = (elem[0],elem[1],self.is_action_allowed())
        if not x in self.unbound_assignment:
            self.unbound_assignment.append(x)
            
    # Expects output of update.search_..._path !
    def add_indirectly_bound_integer_variable(self,elem):
        if type(elem) == list:
            for e in elem:
                part_of = "body"
                if type(e) == list and len(e) == 2:
                    pa = e[1]
                    for tup in pa:
                        if tup[1] == "head":
                            part_of = "head"
                            break
                        elif tup[1] == "ifcons_part":
                            part_of = "ifcons"
                            break
                        elif tup[1] == "after_part":
                            part_of = "after"
                            break
                    # Get head/ifcons/if out of pa
                    
                    e = (e[0][0],e[0][1],e[0][2],part_of)
#                 for ex in self.indir_bound_int_var:
#                     for i in range(len(e)):
#                         if str(e[i])!=str(ex[i]):
#                             break
#                     else:
#                         return                            
                if not e in self.indir_bound_int_var:
                    self.indir_bound_int_var.append(e)
        elif not elem in self.indir_bound_int_var:
            self.indir_bound_int_var.append(elem)
    
    def add_where_arithmetic(self,caller,replaced_law,replacement,arithmetic_law_placement):
        self.where_arithmetic.append((caller,replaced_law,replacement,arithmetic_law_placement))
    
    # Returns fluent, path in law
    def get_int_for_indirectly_bound_variable(self,var):
        vst = str(var)
        for elem in self.indir_bound_int_var:
            if str(elem[1]) == vst:
                return elem[0], elem[3]
        return None, None # If not found 
        
    def get_law_part(self):
        for ob in self.path:
            caller = ob[0]
            func = ob[1];
            if dynamic_law == caller.__class__ or dynamic_law in inspect.getmro(caller.__class__):
                if func == "ifcons_part" : return "ifcons"
                if func == "after_part" : return "after"
                if func == "head" : return "head"
            elif nonexecutable_law == caller.__class__ or nonexecutable_law in inspect.getmro(caller.__class__):
                if func in ["body", "if_part"]: return "after"
                if func == "ifcons_part" : return "ifcons"
            elif law in inspect.getmro(caller.__class__):
                if func == "ifcons_part" : return "ifcons"
                elif func == "after_part" : return "after"
                elif func == "head" : return "head"
                else: return "if"
        
        

class errout(object):
    errors = []
    @staticmethod
    def error(text):
        errout.errors.append(text)
        
    @staticmethod
    def reset():
        errout.errors = []
        
    @staticmethod
    def print_errors():
        for e in errout.errors:
            print e
        errout.errors = []
    
