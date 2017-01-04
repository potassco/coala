#
# Copyright (c) 2016, Christian Schulz-Hanke
#
from __builtin__ import str
import sys
import inspect

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

class parse_object(object):
    
    def __init__(self):
        self.variables = []
        self.child_attributes = []
        self.reference = None
        self.negation = False
    
    # Get all children of the object (used for inheriting classes)
    def get_children(self):
        result = []
        #for att in ["head","body","if_part","ifcons_part","after_part","content","left","right"]:#TODO: this is not meta enough.
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
    def get_variables(self):
        my_vars = []
        ch = self.get_children()
        for c in ch:
            if c is None or type(c) == str: continue
            my_vars += c.get_variables()
        return my_vars
    
    # Extracts domains for fluents.
    # Is overwritten by classes: Fluent, Predicate
    def get_fluents_domains(self,simple=True):
        #print  >> sys.stderr, "Warning!, not implemented get_fluents_domains for", self.__class__ 
        result = []
        ch = self.get_children()
        wh = self.get_where()
        for x in ch:
            do = x.get_fluents_domains()
            if wh is not None:
                for d in do:
                    d.where = wh#TODO: TODODOOOO
                    result.append(d)
            else:
                result += do 
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
            return " :- "+va
    
    # Get the context so that we can integrate it somewhere.
    # Every class should overwrite this.
    def compile_where_single(self):
        print  >> sys.stderr, "ERROR, not implemented compile_where_single for", self.__class__
        errout.error("ERROR, not implemented compile_where_single for"+str(self.__class__))
        return self.print_facts()
    
    # Top-level Update function.
    # Initiates the pass_down update.
    def update(self,actions=None,fluents=None,integers=None,integer_ids=None,idfunction=None,arith_idfunction=None,check=True,others=None,arith_helper_idfunction=None):
        my_others = {"idfunction":idfunction,"arith_idfunction":arith_idfunction,"arith_helper_idfunction":arith_helper_idfunction,"check":check}
        if others is not None:
            for o in others:
                my_others[o] = others[o]
        update = update_passdown(fluents=fluents,actions=actions,integers=integers,integer_ids=integer_ids,others=my_others)
        self.pass_down_update(update)
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
        if wh is not None:
            #prev = update.where #There may only be one update...
            update.where_start(wh)
            wh.pass_down_update(update)
            update.where_end() #prev
            #variables = wh.pass_down_update(actions,fluents,idfunction,arith_idfunction,check=False)
            #for v in variables:
            #    if not v in self.variables:
            #        self.variables.append(v)
                    
        ch = self.get_children_dict()
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
    def simplify(self,negation=False):
        if negation:
            self.negation = not self.negation
            negation = False
        for att in ["head","body","if_part","ifcons_part","after_part","content","left","right"]:
            if hasattr(self,att):
                val = getattr(self,att)
                if val is not None:
                    if type(val) == false_atom:
                        return None
                    if type(val) != str:
                        if type(val) == list:
                            nval = [] 
                            for v in val:
                                if type(v) == str: nval.append(v)
                                else:
                                    if v.is_false(): return None 
                                    nval.append(v.simplify(negation))
                        else:
                            nval = val.simplify(negation)
                        setattr(self,att,nval)
        return self
    
    # General method to compare two parsed objects.
    # This only gets complicated if there are Variables in the Code.
    def compare_to(self,other,parent=True):
        #print >> sys.stderr, "compare: ",self,"("+self.__class__.__name__+"), ",other,"("+other.__class__.__name__+")"
        if self == other: return True
        if self.__class__ != other.__class__:
            if other.__class__ == variable or self.__class__ == variable: return True
            return False
        c1 = self.get_children()
        c2 = other.get_children()
        if len(c1) != len(c2):
            return False
        if len(c1) < 1:
            str_self = self.print_facts() #str(self)
            str_other = other.print_facts() #str(other)
            return str_self.isupper() or str_other.isupper() or str_self == str_other 
        for i in range(len(c1)):
            if type(c1[i]) == str:
                if type(c2[i]) == str: ot = c2[i]
                else: ot = c2[i].print_facts() #str(c2[i])
                return c1[i].isupper() or ot.isupper() or c1[i] == ot
            if not c1[i].compare_to(c2[i],parent=False):
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
    
    def compile_where_single(self):
        if self.content is None: return ""
        comb = []
        for c in self.content:
            if type(c) != str:
                comb.append(c.compile_where_single())
        return ",".join(comb)

class rule(parse_object):
    pass

# Each law has it's own ID.
class law(rule):
    def __init__(self):
        parse_object.__init__(self)
        self.law_type = None
        
    def pass_down_update_overwrite(self, update):
        self.law_id = update.idfunction()
        
    def get_law_type(self):
        return self.law_type


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
        for st in stuff:
            current = st[0]
            if current is None:
                continue
            cname = st[1]
            children = current.get_children()
            for ch in children:
                if type(ch) == str: result += [ cname+"("+myid+","+ch+")"+wherepart+"." ]
                else: result += [ cname+"("+myid+","+ch.print_facts(prime=True)+")"+wherepart+"." ]
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
        for st in stuff:
            current = st[0]
            if current is None:
                continue
            cname = st[1]
            children = current.get_children()
            for ch in children:
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
        for st in stuff:
            current = st[0]
            if current is None:
                continue
            cname = st[1]
            children = current.get_children()
            for ch in children:
                result += [ cname+"("+myid+","+ch.print_facts(prime=True)+")"+wherepart+"." ]
        return result
    
    def simplify(self,negation=False):
        res = parse_object.simplify(self, negation)
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
        for st in stuff:
            current = st[0]
            if current is None:
                continue
            cname = st[1]
            children = current.get_children()
            for ch in children:
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
        for ch in children:
            result += [ "inertial("+ch.print_facts()+")"+wherepart+"." ] #Note that prime=False
        return result

class default_law(law): #default
    def __init__(self, head, if_part, after_part, where,line=None,filename=None):
        law.__init__(self)
        self.law_type = "default_laws"
        self.head = head
        self.if_part = if_part
        self.after_part = after_part
        self.where = where
        self.line_number = line
        self.filename = filename
        self.law_id = None
        self.child_attributes = ["head","if_part","after_part"]
        
    def __str__(self):
        return "default "+str(self.head)+ \
            (" if "+str(self.if_part) if self.if_part is not None else "")+ \
            (" after "+str(self.after_part) if self.after_part is not None else "")+ \
            (" where "+str(self.where) if self.where is not None else "")
            
    def typestr(self):
        return "defined_law("+(self.head.typestr() if self.head is not None else "None")+ \
            "|"+(self.if_part.typestr() if self.if_part is not None else "None")+ \
            "|"+(self.after_part.typestr() if self.after_part is not None else "None")+")"
            
    def print_facts(self,prime=False):
        wherepart = self.compile_where()
        id_list = [str(self.law_id)]+self.variables
        myid = "law("+",".join(x for x in id_list)+")"
        #Law
        result = []
        
        if self.if_part is None and self.after_part is None and self.head is not None:
            for ch in self.head:
                result += [ "default("+ch.print_facts(prime=True)+")"+wherepart+"." ]
            return result
        
        
        stuff = [(self.head,"default"),(self.if_part,"if"),(self.after_part,"after")]
        for st in stuff:
            current = st[0]
            if current is None:
                continue
            cname = st[1]
            children = current.get_children()
            for ch in children:
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
        for st in stuff:
            current = st[0]
            if current is None:
                continue
            cname = st[1]
            children = current.get_children()
            for ch in children:
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
    def __init__(self, head, where,multivalued=None,line=None,filename=None):
        fact.__init__(self)
        self.law_type = "fluents"
        self.head = head
        self.where = where
        self.line_number = line
        self.filename = filename
        self.multivalued = multivalued
        
    def __str__(self):
        return str(self.head)
    
    def typestr(self):
        return "fluent_fact("+self.head.typestr()+")"
    
#     def get_fluents(self,simple=True):
#         if type(self.head) == str: return self.head
#         else: return self.head.get_fluents(simple)

    def get_fluents_domains(self): 
        result = []
        wh = self.get_where()
        for x in self.head:
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
            upper = self.domain.get_children()[1]
            domain = True
        for ac in self.head:
            st = ac.print_facts()
            result.append("integer("+st+")"+wherepart+".")
            if domain:
                result.append("integer_domain("+st+","+lower+","+upper+")"+wherepart+".")
        return result

    def get_integers(self):
        return [self,]

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
        return "initial("+self.head.typestr()+")"
    
    def print_facts(self,prime=False):
        result = []
        wherepart = self.compile_where()
        for ac in self.head:
            st = ac.print_facts(prime=True)
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
        return "goal("+self.head.typestr()+")"
    
    def print_facts(self,prime=False):
        result = []
        wherepart = self.compile_where()
        for ac in self.head:
            st = ac.print_facts(prime=True)
            result.append("goal("+st+")"+wherepart+".")
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
            print >> sys.stderr, "Warning! Action "+str(self)+" is negated."
            errout.error("Warning! Action "+str(self)+" is negated.")
        return "action(act("+self.content.print_facts()+"))"
    
    def pass_down_update_overwrite(self,update):
        if not update.where:
            print >> sys.stderr, "Action "+str(self)+" can only appear in where parts!"
            errout.error("Action "+str(self)+" can only appear in where parts!")
        update.add_where_action(self.content)
    
    def get_bottom_elements(self):
        return [self,]

# This may only occur in a where part!!!
class fluent(parse_object):
    def __init__(self, content, domainelement=None):
        parse_object.__init__(self)
        self.content = content
        self.domainelement = domainelement
        self.child_attributes = ["content"]
        
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
        
    def compile_where_single(self):
        if self.domainelement is None:
            return "fluent("+self.content.print_facts()+")"
        else:
            ##TODO: If is not integer!
            return "domain("+self.content.print_facts()+","+self.domainelement.print_facts()+")"
    
    def pass_down_update_overwrite(self,update):
        if not update.where:
            print >> sys.stderr, "Fluent "+str(self)+" can only appear in where parts!"
            errout.error("Fluent "+str(self)+" can only appear in where parts!")
        update.add_where_fluent(self.content)
    
    def get_bottom_elements(self):
        return [self,]

class predicate(parse_object):
    def __init__(self, name, parameters):
        parse_object.__init__(self)
        self.name = name
        self.parameters = parameters
        self.compile_where_single = self.print_facts
        self.type = "??"
        self.child_attributes = ["parameters"]
        
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
            print "This should not happen!"
            #print self.name.typestr()
            text = self.name.print_facts()
        if prime:
            if self.type == "fluent":
                return "val("+text+","+str(not self.negation).lower()+")" #true)"
            elif self.type == "action":
                if self.negation: 
                    print >> sys.stderr, "Warning! Action "+str(self)+" is negated."
                    errout.error("Warning! Action "+str(self)+" is negated.")
                return "act("+text+")"      
            elif self.type == "integer":
                if self.negation: 
                    print >> sys.stderr, "Warning! Fluent "+str(self)+" is negated."
                    errout.error("Warning! Integer "+str(self)+" is negated.")#TODO!
                return "_arithmetic("+text+")"#TODO: return somethin if we are an integer      
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
                    print >> sys.stderr, "Error! "+str(self)+" is Fluent and Action at the same time"
                    errout.error("Error! "+str(self)+" is Fluent and Action at the same time")
            
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
                    if self.compare_to(inte):#TODO: get a number for this law?
                        self.reference = inte
                        self.type = "integer"
                        update.set("has_integer",True)
                        definite_type = True
                        break 
            
            if update.where:
                self.type = "asp"
            elif not definite_type and self.type == "??": # Assume Fluent!
                print >> sys.stderr, "Waring: Cannot find "+str(self)+" in fluents or actions!"
                errout.error( "Waring: Cannot find "+str(self)+" in fluents or actions!")
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
        return self.variables
    
    #TODO: simplification for integers?
    
    def compare_to(self,other,parent=True):
        if self.__class__ == other.__class__:
            if self.name != other.name or len(self.parameters) != len(other.parameters): return False
            return self.parameters.compare_to(other.parameters,parent=False)
        # Tricky: compare Predicate to Unknown/Action/Fluent?
        if not parent: 
            if other.__class__ == variable: return True
            if type(other) == str:
                return other.isupper()
            o = other.print_facts()
            return type(o) == str and o.isupper()
        
        return False
    
    def arith_flatten(self,negation,update):
        return arithmetic_atom(self.print_facts(),update.arith_helper_idfunction(),negation)

class arithmatic_law(law): # Will be generated out of equations!
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
        
        #TODO: extract stuff from body... it needs to be a list of int_variables with factors
            
    
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
        
        if self.is_assignment:
            for e in self.head:
                result.append("arithmetic_head("+stid+","+e.print_facts()+")"+wherepart+".")
        else:
            for e in self.head:
                result.append("arithmetic("+stid+","+e.print_facts()+")"+wherepart+".")
        for e in self.body:
            result.append("arithmetic("+stid+","+e.print_facts()+")"+wherepart+".")
        return result

class arithmetic_atom(parse_object):
    def __init__(self,value,helper_id,negation=False):
        parse_object.__init__(self)
        self.unknown = False
        self.value = None
        self.unknown_is = None
        self.helper_id = helper_id
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
    
    #def negate(self):
    #    self.negation = not self.negation
        
    def has_no_variable(self):
        return not self.unknown and self.variable is None
        
    def can_add(self,other):
        return not self.unknown and not other.unknown and self.variable == other.variable # Equal or both None
        #TODO: Add unknown to unknown?
    
    def negate(self):
        self.negation = not self.negation
    
    def add(self,other):
        #TODO: Add unknown to unknown?
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
            raise NameError("Arithmetics: Another Nooooooooooooo!")
    
    def multiply(self,other): #TODO: If this was unknown, we cannot be certain what will happen!
        if other.__class__ is not arithmetic_atom: raise NameError("Arithmetics: Nooooooooooooo!")
        if self.unknown:
            if other.unknown:
                if self.value == other.value:
                    raise NameError("Arithmetics: There are some limitations on how to use variables in arithmetics!")
                    #TODO: oh Shit. Can we do anything here?
                else:
                    if self.variable is None and other.variable is None:
                        self.variable = other.value
                        self.unknown_is = "Factor"
                    else:
                        raise NameError("Arithmetics: There are some limitations on how to use variables in arithmetics!")
                        #TODO: oh shit. Can we do anything here?
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
    
    def divide(self, other): #TODO: If this was unknown, we cannot be certain what will happen!
        if other.__class__ is not arithmetic_atom: raise NameError("Arithmetics: Nooooooooooooo!")
        if other.variable is not None:
            raise NameError("Arithmetics: There are some limitations on how to use variables in arithmetics!")
        if self.unknown or other.unknown:
            raise NameError("Arithmetics: TODO: We cannot be sure what to do here!") #TODO math?
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
    
    def print_facts(self, prime=False):
        if self.unknown:
            if self.variable is not None:
                return "_unknown,"+self.variable+","+self.value+","+("-" if self.negation else "")+str(int(self.factor))+","+str(self.helper_id)
            else:
                return "_unknown,"+self.value+","+("-" if self.negation else "")+str(int(self.factor))+","+str(self.helper_id)
        elif self.variable is not None:
            return self.variable+","+("-" if self.negation else "")+str(int(self.factor))+","+str(self.helper_id)
        else:
            # Invert negation here: A single number will be written on the other side of the equation
            #return ("-" if not self.negation else "")+str(int(self.factor))
            return ("-" if self.negation else "")+str(int(self.factor)) ###+","+str(self.helper_id)
        
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
        update.set("has_integer",False)
        simple=False
        
        if self.operator in ["="] and \
            self.left.__class__ in [unknown, variable, predicate] \
            and self.right.__class__ in [str,unknown,variable]:
                simple=True
        
        if type(self.left) != str:
            variables = self.left.pass_down_update(update)
            for v in variables:
                if not v in self.variables:
                    self.variables.append(v)
                
        if update.get("has_integer"): simple=False
        
        if type(self.right) != str:
            if simple: update.set("fluent equation head",True)
            variables = self.right.pass_down_update(update)
            if simple: update.set("fluent equation head",None)
            for v in variables:
                if not v in self.variables:
                    self.variables.append(v)

        if update.get("has_integer") or (not simple and not update.where): #rewrite to arithmetic(X)
            self.has_integer = True
            self.my_id = update.arith_idfunction()
            self.replacement = predicate("_arithmetic",atom_list(predicate("law",atom_list(str(self.my_id),self.variables))))
            assignment = update.is_in_head()
            dynamic_law_part = update.is_in_dynamic_law()
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
            
            law = arithmatic_law(head,body,self.operator,self.my_id,assignment,dynamic_law_part,self.variables,update.get_where())#self.get_where())
            update.add_arithmetic_law(law)
            
        
        return self.variables

    def compile_where_single(self):
        return self.print_facts()
        
    def simplify(self, negation=False):
        if self.replacement is not None:
            return self.replacement.simplify(negation)
        if type(self.left) in [unknown,predicate,str] and self.operator in ["=","=="]:
            if self.right == "<true>": #in ["<true>","true"] : 
                return fluent(self.left,not negation)
            if self.right == "<false>": #in ["<false>","false"] : 
                return fluent(self.left,negation)
            inner = assignment(self.left,self.right,negation)
            return inner.simplify()
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
            unkn = l.unknown or r.unknown
            
            helper_elements = [variable]
            if l.unknown: helper_elements += [lunknown]
            helper_elements += [str(int(factor))]
            if r.unknown: helper_elements += [runknown]
            
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
        update.set("has_integer",False)
        if type(self.head) != str:
            variables = self.head.pass_down_update(update)
            for v in variables:
                if not v in self.variables:
                    self.variables.append(v)
        is_arithmetic_assignment = False
        if update.get("has_integer"):
            is_arithmetic_assignment = True
            
        if type(self.body) != str:
            variables = self.body.pass_down_update(update)
            for v in variables:
                if not v in self.variables:
                    self.variables.append(v)

        if is_arithmetic_assignment:
            self.has_integer = True
            self.my_id = update.arith_idfunction()
            self.replacement = predicate("_arithmetic",atom_list(predicate("law",atom_list(str(self.my_id),self.variables))))
            assignment = update.is_in_head()
            if not assignment:
                print >> sys.stderr, "Error: Assignment in Body!"
                errout.error("Error: Assignment in Body!")
            dynamic_law_part = update.is_in_dynamic_law()
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
            
            law = arithmatic_law(head,body,"=",self.my_id,assignment,dynamic_law_part,self.variables,update.get_where())#self.get_where())
            update.add_arithmetic_law(law)
            
        
        return self.variables
    
    def simplify(self, negation=False):
        if self.replacement is not None:
            return self.replacement.simplify(negation)
        if negation:
            self.negation = not self.negation
        return self

# unknown may sound weird, but while parsing it, we don't know what this is.
# It may be a Fluent, Actions
class unknown(parse_object):
    def __init__(self, content):
        parse_object.__init__(self)
        self.content = content
        self.type = "??"
        self.child_attributes = []#"content"
        
    def __str__(self):
        return str(self.content)
    
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
                if self.compare_to(inte):#TODO: get a number for this law?
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
            print >> sys.stderr, "Waring: Cannot find "+str(self)+" in fluents or actions!"
            errout.error("Waring: Cannot find "+str(self)+" in fluents or actions!")
            self.type = "fluent"
            
        return variables
    
    def print_facts(self,prime=False):
        #return self.print_facts_unknown(prime)
        st = str(self.content)
        if not prime: return st
        if self.type == "action":
            if self.negation: 
                print >> sys.stderr, "Warning! Action "+str(self)+" is negated."
                errout.error("Warning! Action "+str(self)+" is negated.")
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
        return arithmetic_atom(self.print_facts(),update.arith_helper_idfunction(),negation)
    
    def compile_where_single(self):
        return self.print_facts()

class variable(parse_object):
    def __init__(self, content):
        parse_object.__init__(self)
        self.content = content
        self.type = "??" #This is an assumption!
        self.child_attributes = []#"content"
        
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
        #TODO: Get a way of knowing if this here is an action/fluent or integer!!...
        #where_binding = update.get("where_binding")
        if update.had_where: #where_binding is not None:
            fls = update.where_fluents #where_binding["fluents"]
            acs = update.where_actions #where_binding["actions"]
            assigned_fluent = False
            for x in fls:
                if str(self) == str(x):
                    self.type = "fluent"
                    assigned_fluent = True
                    break
            for x in acs:
                if str(self) == str(x):
                    if assigned_fluent:
                        print "Warning! Variable "+str(self)+" could be a fluent or action!"
                    self.type = "action"
                    break
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
                    print >> sys.stderr, "Warning!!! "+my_str+" could also be an action!"
                    errout.error("Warning!!! "+my_str+" could also be an action!")
                    return "val("+my_str+",true)"
        return my_str
    
    def get_variables(self):
        return self

    def get_bottom_elements(self):
        return [self,]
    
    def arith_flatten(self,negation,update):
        return arithmetic_atom(self.print_facts(),update.arith_helper_idfunction(),negation)

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
        return "neg("+self.content.typestr()+")"

    def print_facts(self,prime=False):
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

    def simplify(self, negation=False):
        if self.content is None:
            return None
        if type(self.content) == str:
            return "not "+self.content
        return self.content.simplify(negation=True)
    
    def compile_where_single(self):
        if self.content is None:
            return ""
        return "not "+self.content.print_facts()

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
    def __init__(self, fluents=[], actions=[], integers=[], integer_ids=[], others={}):
        self.fluents = fluents
        self.actions = actions
        self.integers = integers
        self.integer_ids = integer_ids
        self.arithmetic_laws = []
        self.pass_up = {}
        self.where = False
        self.had_where = False
        self.where_part = None
        self.where_actions = []
        self.where_fluents = []
        self.path = []
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
        for ob in self.path:
            caller = ob[0]; att = ob[1]
            if att == "head" and law in inspect.getmro(caller.__class__):
                return True
        return False
    
    def is_in_dynamic_law(self):
        for ob in self.path:
            caller = ob[0];
            if dynamic_law == caller.__class__:
                return True
            if dynamic_law in inspect.getmro(caller.__class__):
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
    
