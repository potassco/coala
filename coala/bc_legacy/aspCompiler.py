#
# Copyright (c) 2016, Christian Schulz-Hanke
#
import sys
import os

def booleanDomain(wherepart=[],wheriables=[],variables=[]): 
	return [(['true'],wherepart,wheriables,variables),(['false'],wherepart,wheriables,variables)]

def isBoolDomain(data):
	find_true = False
	find_false = False
	if type(data) == list:
		for tup in data:
			if type(tup) == tuple:
				ar = tup[0]
				if type(ar) == list:
					for el in ar:
						if el == 'true':
							find_true = True
						elif el == 'false':
							find_false = True
						else:
							return False
				elif ar == 'true':
					find_true = True
				elif ar == 'false':
					find_false = True
				else:
					return False
			
	return find_false and find_true

class AspCompiler(object):

	def __init__(self,ignorance=False,decoupled=False):
		self.actions = []
		self.actions_str = []
		self.fluents = []
		self.flu_domains = {}
		self.errors = []
		self.debug = False
		self.lawid = 1
		self.tofile = True
		self.no_error = True
		self.silent = False
		self.decoupled = decoupled
		self.return_string = False
		self.string = ''
		self.ignorance = ignorance
		self.ignore_undefined = False
		self.current_vars = []
		self.current_meta_info = None
		self.negated_actions = False		
		self.where_action_list = []
		self.where_fluent_list = []
		self.text_written = False
		if self.decoupled: self.static_law = "head"
		else: self.static_law = "static_law"
		if self.decoupled: self.dynamic_law = "head"
		else: self.dynamic_law = "dynamic_law"
		if self.decoupled: self.difcons = "ifcons"
		else: self.difcons = "difcons"
		if self.decoupled: self.default_if = "if"
		else: self.default_if = "default_if"
		if self.decoupled: self.default_after = "after"
		else: self.default_after = "default_after"
		if self.decoupled: self.nonexecutable_if = "if"
		else: self.nonexecutable_if = "nonexecutable_if"
		if self.decoupled: self.nonexecutable_ifcons = "ifcons"
		else: self.nonexecutable_ifcons = "nonexecutable_ifcons"
		if self.decoupled: self.impossible_ifcons = "ifcons"
		else: self.impossible_ifcons = "impossible_ifcons"
		self.my_lines = []
		self.meta_info = []
		
	def submit_text(self,text,meta):
		self.my_lines = text.split("\n")
		self.meta_info = meta 
		
	def get_atom_type(self,value,allow_actions=True):
		
		only_action = value in self.where_action_list
		only_fluent = value in self.where_fluent_list
		if only_action and only_fluent:
			self.error("Warning: Identifier "+str(value)+" is bound as fluent and action.", fatal=False)
		
		if not allow_actions:
			if self.is_fluent(value): return "f"
			else: return None
		maxres = -2
		atom_type = None
		if not only_fluent:
			for act in self.actions:
				for sac in act[0][0]:
					x = self.is_fitting(value,sac,act[0][-1])
					if x >= 0 and x > maxres:
						maxres = x
						atom_type = "a"
						if x == 2: return atom_type
		
		if type(value) == tuple and value[0] == '-':
			if len(value) > 2:
				self.error("Error with negation in "+str(value))
			value = value[1]
		#if value in self.current_vars and value in self.where_action_list:
		#print self.where_action_list	
		if not only_action:
			for flu in self.fluents:
				for sflu in flu[0][0]:
					x = self.is_fitting(value,sflu,flu[0][-1])
					if x >= 0 and  x > maxres:
						maxres = x
						atom_type = "f"
						if x == 2: return atom_type
		return atom_type
		
	def is_action(self,value):
		for act in self.actions:
			for sac in act[0][0]:
				if self.is_fitting(value,sac,act[0][-1]) >= 0:
					return True		
		return False	
		
	def is_fluent(self,value):
		if type(value) == tuple and value[0] == '-':
			if len(value) > 2:
				self.error("Error with negation in "+str(value))
			value = value[1]
		if value in self.current_vars and value in self.where_action_list:
			return False # It is an action instead
		for flu in self.fluents:
			for sflu in flu[0][0]:
				if self.is_fitting(value,sflu,flu[0][-1]) >= 0:
					return True 
		return False   
	
	# -1: not fitting
	# 0: There is a variable that could fit
	# 1: Structurely comparable, but variables
	# 2: Stings and equal
	def is_fitting(self,value,comp,var):
		#print "testing: ",value," : ",comp," ; ",var," ; ",self.current_vars
		if value == comp:
			return 2
		if value in self.current_vars:
			return 0
		if comp in var:
			return 0
		if type(value) == type(comp):
			if len(value) != len(comp):
				return -1
			if type(value) == list:
				result = 2
				for i in range(len(value)):
					x = self.is_fitting(value[i],comp[i],var)
					if x < 0: return -1
					if x < 2: result = x #TODO: How to do this here?
				return result
			elif type(value) == tuple:
				if value[0] != comp[0]:
					return -1
				result = 2
				for i in range(1,len(value)):
					x = self.is_fitting(value[i],comp[i],var)
					if x < 0: return -1
					if x < 2: result = 1 #TODO: How to do this here?
				return result
		return -1
	
	def to_string_array(self,value,tf=False,after_part=False):
		result = []
		
		if type(value) == tuple or type(value) == list:
			for at in value:
				result.append(self.to_string(at,tf,after_part))
		elif value != None:
			result = [self.to_string(value,tf,after_part)]
		
		return result
	
	def to_string(self,value,tf=False,after_part=False,allow_actions=True):
		result = ''
		
		if type(value) == tuple:
			if value[0] == '-':
				if len(value) > 3:
					self.error('ERROR: Odd Negation '+str(value))
					return str(value)
				elif len(value) == 3:
					result = self.to_string(value[1],True,after_part,allow_actions)+value[0]+self.to_string(value[2],True,after_part,allow_actions)
				elif not tf:
					if type(value[1]) == tuple and value[1][0] == 'fval':
						val = self.to_string(value[1][1],True,after_part,allow_actions)
						equ = self.to_string(value[1][2],True,after_part,allow_actions)
						at_type = self.get_atom_type(value[1][1], allow_actions)
						if at_type == "a":
							self.error("ERROR: Actions are not multivalued and cannot be negated! -"+val+"="+equ+" is not allowed!")
						elif at_type is None:
							if not self.ignore_undefined: self.error("ERROR: Fluent "+val+" was not declared before!!")
							#TODO: postdeclaration?
						return 'neg_val('+val+','+equ+')'
					else:
						val = self.to_string(value[1],True,after_part,allow_actions)
						at_type = self.get_atom_type(value[1], allow_actions)
						if at_type == "f":
							return 'val('+val+',false)'
						elif at_type == "a":
							if self.negated_actions:
								return 'act('+val+',false)'
							else:
								self.error("ERROR: Actions cannot be negated! -"+val+" is not allowed!")
								return 'val('+val+',false)'
						else:
							if not self.ignore_undefined: self.error("ERROR: Fluent "+val+" was not declared before!!")
							return 'val('+val+',false)'
							#TODO: postdeclaration?
				else:
					result = '-'+self.to_string(value[1],True,after_part,allow_actions)
			elif value[0] == 'fval' and len(value) == 3: # Multivalued stuff
				if not tf:
					return 'val('+self.to_string(value[1], True,after_part,allow_actions)+","+self.to_string(value[2], True,after_part,allow_actions)+")"
				else:
					return self.to_string(value[1], True,after_part,allow_actions)
				#else:
				#	result = self.to_string(value[1],True,after_part,allow_actions)+value[0]+self.to_string(value[2],True,after_part,allow_actions)
					#return self.to_string(value[1], True) # only return the fluent, not the equivalence
			elif value[0] == '_':
				result = 'not '+self.to_string(value[1],True,after_part,allow_actions)
			elif len(value)==3 and value[0] in ('!=',"<=",">=","==","=",">","<","**","*","+","/"):
				result = self.to_string(value[1],True,after_part,allow_actions)+value[0]+self.to_string(value[2],True,after_part,allow_actions)
			else:
				result = self.to_string(value[0],True,after_part,allow_actions)+'('
				ind = 1
				for i in range(1,len(value)):
					if ind == 0:
						result += ','
					result += self.to_string(value[i],True,after_part,allow_actions)
					ind = 0
				result += ')'
				if not tf:
					at_type = self.get_atom_type(value, allow_actions)
					if at_type == "f":
						return 'val('+result+',true)'
					elif at_type == "a":
						if self.negated_actions:
							if after_part:
								return 'act('+result+',true)'
							else:
								return str(result)
						else:
							return 'act('+result+')'
					else:
						if not self.ignore_undefined: self.error("ERROR: Fluent "+result+" was not declared!!")
						return 'val('+result+',true)'
						#TODO: postdeclaration?
				
		elif type(value) == list:
			mind = 1
			for el in value:
				if mind == 0:
					result += ','
				result += self.to_string(el,tf,after_part)
				mind = 0
		elif type(value) == str and not tf: 
			at_type = self.get_atom_type(value, allow_actions)
			if at_type == "f":
				return 'val('+value+',true)'
			elif at_type == "a":
				if self.negated_actions:
					if after_part:
						return 'act('+value+',true)'
					else:
						return value
				else:
					result = 'act('+value+')'
			else: 
				if not self.ignore_undefined: self.error("ERROR: The fluent or other "+str(value)+" was not defined.")
				return 'val('+value+',true)'
		elif type(value) == str:
			result = str(value)
		else:
			self.error("ERROR: Unexpected object type: "+str(type(value))+" of "+str(value))
			result = str(value)
		
		return result
	
	def to_string_old(self,value,tf=False,after_part=False,allow_actions=True):
		result = ''
		
		if type(value) == tuple:
			if value[0] == '-':
				if len(value) > 3:
					self.error('ERROR: Odd Negation '+str(value))
					return str(value)
				elif len(value) == 3:
					result = self.to_string(value[1],True,after_part,allow_actions)+value[0]+self.to_string(value[2],True,after_part,allow_actions)
				elif not tf:
					if type(value[1]) == tuple and value[1][0] == '=':
						val = self.to_string(value[1][1],True,after_part,allow_actions)
						equ = self.to_string(value[1][2],True,after_part,allow_actions)
						if not self.is_fluent(value[1][1]):
							if allow_actions and self.is_action(value[1][1]):
								self.error("ERROR: Actions are not multivalued and cannot be negated! -"+val+"="+equ+" is not allowed!")
								#if self.negated_actions:
								#	return 'act('+val+',false)'
								#else:
								#	self.error("ERROR: Actions cannot be negated! -"+val+" is not allowed!")
							else:
								if not self.ignore_undefined: self.error("ERROR: Fluent "+val+" was not declared before!!")
								#TODO: postdeclaration?
								return 'neg_val('+val+','+equ+')'
						return 'neg_val('+val+','+equ+')'
					else:
						val = self.to_string(value[1],True,after_part,allow_actions)
						if not self.is_fluent(value[1]):
							if allow_actions and self.is_action(value[1]):
								if self.negated_actions:
									return 'act('+val+',false)'
								else:
									self.error("ERROR: Actions cannot be negated! -"+val+" is not allowed!")
							else:
								if not self.ignore_undefined: self.error("ERROR: Fluent "+val+" was not declared before!!")
								return 'val('+val+',false)'
								#TODO: postdeclaration?
						return 'val('+val+',false)'
				else:
					result = '-'+self.to_string(value[1],True,after_part,allow_actions)
			elif value[0] == '=':
				if not tf and len(value) == 3:
					return 'val('+self.to_string(value[1], True,after_part,allow_actions)+","+self.to_string(value[2], True,after_part,allow_actions)+")"
				else:
					result = self.to_string(value[1],True,after_part,allow_actions)+value[0]+self.to_string(value[2],True,after_part,allow_actions)
					#return self.to_string(value[1], True) # only return the fluent, not the equivalence
			elif value[0] == '_':
				result = 'not '+self.to_string(value[1],True,after_part,allow_actions)
			elif len(value)==3 and value[0] in ('!=',"<=",">=","==",">","<","**","*","+","/"):
				result = self.to_string(value[1],True,after_part,allow_actions)+value[0]+self.to_string(value[2],True,after_part,allow_actions)
			else:
				result = self.to_string(value[0],True,after_part,allow_actions)+'('
				ind = 1
				for i in range(1,len(value)):
					if ind == 0:
						result += ','
					result += self.to_string(value[i],True,after_part,allow_actions)
					ind = 0
				result += ')'
				if not tf:
					if self.is_fluent(value):
						return 'val('+result+',true)'
					elif allow_actions and self.is_action(value):
						if self.negated_actions:
							if after_part:
								return 'act('+result+',true)'
							else:
								return str(result)
						else:
							return 'act('+result+')'
					else:
						if not self.ignore_undefined: self.error("ERROR: Fluent "+result+" was not declared!!")
						return 'val('+result+',true)'
						#TODO: postdeclaration?
				
		elif type(value) == list:
			mind = 1
			for el in value:
				if mind == 0:
					result += ','
				result += self.to_string(el,tf,after_part)
				mind = 0
		elif type(value) == str and not tf: 
			if self.is_fluent(value):
				return 'val('+value+',true)'
			elif allow_actions and self.is_action(value):
				if self.negated_actions:
					if after_part:
						return 'act('+value+',true)'
					else:
						return value
				else:
					result = 'act('+value+')'
			else: 
				if not self.ignore_undefined: self.error("ERROR: The fluent or other "+str(value)+" was not defined.")
				return 'val('+value+',true)'
		elif type(value) == str:
			result = str(value)
		else:
			self.error("ERROR: Unexpected object type: "+str(type(value))+" of "+str(value))
			result = str(value)
		
		return result
	
	def clean_fluents(self,data):
		result = []
		if type(data) == list:
			for sett in data:
				meta = sett[1]
				sett = sett[0]
				flret = None 
				if type(sett) == tuple:
					fls = sett[0]
					flall = []
					if type(fls) == list:
						for fl in fls:
							if type(fl) == tuple and fl[0] == '=':
								flall.append(fl[1])
							else:
								flall.append(fl)
					#flret = (flall,sett[1],sett[2],sett[3])
					flret = (flall,sett[-3],sett[-2],sett[-1])
				if flret != None and not flret in result:
					result.append((flret,meta))
			
		return result
	
	def add_domain(self,fluent,data,fluent_string):
		#print "add_domain ",fluent,data,fluent_string
		if type(fluent) == tuple and fluent[0] == 'fval':
			val = self.to_string(fluent[2], True)
			if fluent_string in self.flu_domains:
				do = self.flu_domains[fluent_string]
				if not val in do: 
					if isBoolDomain(do): #do == booleanDomain():
						self.error("Error: Fluent "+fluent_string+" has boolean plus some element as domain.. "+val)
					do.append(([val],data[-3],data[-2],data[-1]))
			else: self.flu_domains[fluent_string] = [([val],data[-3],data[-2],data[-1])] 
		else: 
			if fluent_string in self.flu_domains:
				do = self.flu_domains[fluent_string]
				if len(do)<1 : do = booleanDomain(wherepart=data[-3],wheriables=data[-2],variables=data[-1])
				elif not isBoolDomain(do): #do != booleanDomain():
					do += booleanDomain(wherepart=data[-3],wheriables=data[-2],variables=data[-1])
					self.error("Error: Fluent "+str(fluent_string)+" has a boolean and another domain.. "+str(do))
				else:
					do += booleanDomain(wherepart=data[-3],wheriables=data[-2],variables=data[-1])
					self.flu_domains[fluent_string] = do
			else: self.flu_domains[fluent_string] = booleanDomain(wherepart=data[-3],wheriables=data[-2],variables=data[-1])
	
	#def extract_all(self,data,no_to_str=None,after=None):
	def extract_all(self,data,after=None):
		no_to_str = len(data) - 3
		result = []
		if type(data) == list:
			return [self.to_string(data)]
		self.current_vars = data[-1]
		for i in range(len(data)):
			if no_to_str != None and no_to_str <= i: 
				result.append(data[i])
			elif after != None and after == i:
				result.append(self.to_string_array(data[i],after_part=True))
			else: 
				result.append(self.to_string_array(data[i]))
		return result
	
	def next_id(self):
		myid = self.lawid
		self.lawid += 1
		return myid
	
	def make_id(self,data):
		try:
			data = list(set(data))
		except:
			pass
		result = str(self.next_id())
		if len(data) > 0:
			result += ','+self.to_string(data,True)
		return result
	
	def write(self,data):
		self.text_written = True
		if self.return_string:
			self.string += data+os.linesep
		if not self.tofile:
			if not self.silent and self.debug:
				print data
			return
		try:
			self.f.write(data+os.linesep)
		except:
			print >> sys.stderr, "% ERRRRRRR"
			if not self.ignorance:
				raise
	
	def error(self,data,fatal=True,meta=True):
		if meta and not self.current_meta_info is None:
			fi = self.current_meta_info['file']
			li = self.current_meta_info['line']
			found = False
			if not self.meta_info is None:
				for x in self.meta_info:
					if fi == x[2] and li <= x[1] and len(self.my_lines) > x[0]+li:
						data += " ("+fi+":"+str(li)+": '"+self.my_lines[x[0]+li-1]+"' )"
						found = True
						break
			if not found:
				data += " ("+fi+":"+str(li)+")"
		self.errors.append(data)
		if self.tofile:
			try:
				self.f.write("% "+data+os.linesep)
			except:
				print >> sys.stderr, "% ERRRRRRR"
		if fatal and not self.ignorance:
			self.no_error = False
			raise NameError(data)
	
	def close(self):
		if self.f != None:
			try:
				self.f.close()
			except:
				print >> sys.stderr,  "% ERRRRRRR"
				pass
		self.f = None
		
	def read_errors(self,errs):
		for erro in errs:
			self.error(erro)
	
	def compile(self,data,filenam):
		self.lawid = 1
		self.no_error = True
		self.string = ''
		
		self.filename = filenam   
		self.f = None
		
		self.reset_self()
		
		#print "FLS: ",self.fluents
		
		if self.tofile:
			try:
				self.f = open(self.filename,'w')
			except:
				print >> sys.stderr, "% Could not open file "+str(self.filename)
			
		self.read_errors(data['errors'])
		
		try:
			self.actions = data['actions']
			self.fluents = self.clean_fluents(data['fluents']+data['defined_fluents'])
			
			self.compile_others(data['others'])
		
			self.compile_predicates(data['preds']) 
			self.compile_actions(data['actions']) 
			self.compile_fluents(data['fluents'])
			self.compile_defined_fluents(data['defined_fluents'])
			self.compile_domains()
				
			if self.text_written:
				self.write('')
				self.text_written = False
				
			self.compile_static_laws(data['static_laws'])
				
			if self.text_written:
				self.write('')
				self.text_written = False
			
			self.compile_dynamic_laws(data['dynamic_laws'])
				
			if self.text_written:
				self.write('')
				self.text_written = False
			
			self.compile_impossible_laws(data['impossible_laws'])
			self.compile_nonexecutable_laws(data['nonexecutable_laws'])
			self.compile_default_laws(data['default_laws'])
			self.compile_inertial_laws(data['inertial_laws'])
				
			if self.text_written:
				self.write('')
				self.text_written = False
				
			self.compile_visibles(data['visible_laws'])
			self.compile_initially_laws(data['initially_laws'])
			self.compile_goals(data['goals'])
			
			if data['killEncoding'][0] == 1 or data['killEncoding'][1] == 1:
				self.compile_kill(data['killEncoding'][0], data['killEncoding'][1])
			
		except Exception as e:
			if not self.ignorance:
				raise
			if not self.silent:
				print str(e)
			self.close()
			return None

		self.close()
		
		if self.return_string:
			return self.string
		
		return self.filename
	
	def reset_self(self):
		#self.actions = []
		self.actions_str = []
		#self.fluents = []
		self.fluents_str = []
		self.flu_domains = {}
		
	
	def compile_others(self,text):
		for part in text: # We trust you on this one.
			self.write(part)
	
	def compile_predicates(self,laws):
		for ac in laws:
			self.current_meta_info = ac[1]
			ac = ac[0]
			wherepart = self.return_compiled_where(ac[-3],ac[-2],ac[-1])
			for sac in ac[0]:
				act = self.to_string(sac,True)
				self.write(act+wherepart+'.')
		self.current_meta_info = None
	
	def compile_actions(self,laws):
		for ac in laws:
			self.current_meta_info = ac[1]
			ac = ac[0]
			wherepart = self.return_compiled_where(ac[-3],ac[-2],ac[-1])
			for sac in ac[0]:
				act = self.to_string(sac,True)
				if len(ac[-1]) == 0:
					if act in self.actions_str:
						self.error("Warning: Action "+act+" was declared twice",fatal=False)
					self.actions_str.append(act)	
				if self.negated_actions:
					self.write('action(' + act + ')'+wherepart+'.')
				else:
					self.write('action(act(' + act + '))'+wherepart+'.')
		self.current_meta_info = None
	
	def compile_fluents(self,laws):
		for ac in laws:
			self.current_meta_info = ac[1]
			ac = ac[0]
			wherepart = self.return_compiled_where(ac[-3],ac[-2],ac[-1])
			for sac in ac[0]:
				fl = self.to_string(sac,True)
				fl_full = self.to_string(sac,False)
				self.add_domain(sac,ac,fl)
				if len(ac[-1]) == 0:
					if fl_full in self.actions_str:
						self.error("Error: Fluent "+fl+" was declared as an Action before!")
						if not self.ignorance: return
					if fl_full in self.fluents_str:
						self.error("Warning: Fluent "+fl+" was declared twice",fatal=False)
						if not self.ignorance: return
					self.fluents_str.append(fl_full)
				self.write('fluent(' + fl + ')'+wherepart+'.')
		self.current_meta_info = None
	
	def compile_defined_fluents(self,laws):
		for ac in laws:
			self.current_meta_info = ac[1]
			ac = ac[0]
			wherepart = self.return_compiled_where(ac[-3],ac[-2],ac[-1])
			for sac in ac[0]:
				fl = self.to_string(sac,True)
				fl_full = self.to_string(sac,False)
				self.add_domain(sac,ac,fl)
				if len(ac[-1]) == 0:
					if fl_full in self.actions_str:
						self.error("Error: Fluent "+fl+" was declared as an Action before!")
						if not self.ignorance: return
					if fl_full in self.fluents_str:
						self.error("Warning: Fluent "+fl+" was declared twice",fatal=False)
						if not self.ignorance: return
					self.fluents_str.append(fl_full)
				self.write('defined_fluent(' + fl + ')'+wherepart+'.')
		self.current_meta_info = None
				
	def compile_domains(self):
		for fld in self.flu_domains:
			result = ""
			for data in self.flu_domains[fld]:
				if len(data) == 4:
					result+='domain('+fld+','+data[0][0]+')'+self.return_compiled_where(data[-3],data[-2],data[-1])+'. '
				else:
					self.error("Error with domain "+str(data))
			self.write(result)
	
	def compile_static_laws(self,laws):
		for ac in laws: #TODO error with negative heads!
			self.current_meta_info = ac[1]
			ac = ac[0]
			wherepart = self.return_compiled_where(ac[-3],ac[-2],ac[-1])
			data = self.extract_all(ac)#,3)
			myidstr = self.make_id(data[-1])
			#wherepart = self.return_compiled_where(data[-3],data[-2],data[-1])
			if len(data) == 6:
				if self.decoupled: self.write('static_law(law('+myidstr+'))'+wherepart+'.')
				for p in data[0]: self.write(self.static_law+'(law('+myidstr+'),'+p+')'+wherepart+'.')
				for p in data[1]: self.write('if(law('+myidstr+'),'+p+')'+wherepart+'.')
				for p in data[2]: self.write('ifcons(law('+myidstr+'),'+p+')'+wherepart+'.')
			else:
				self.error("Error with size of static law "+str(ac))
		self.current_meta_info = None
	
	def compile_dynamic_laws(self,laws):
		for ac in laws:
			self.current_meta_info = ac[1]
			ac = ac[0]
			wherepart = self.return_compiled_where(ac[-3],ac[-2],ac[-1])
			data = self.extract_all(ac,1) #3,1)
			myidstr = self.make_id(data[-1])
			#wherepart = self.return_compiled_where(data[-3],data[-2],data[-1])
			if len(data)== 6:
				if self.decoupled: self.write('dynamic_law(law('+myidstr+'))'+wherepart+'.')
				for p in data[0]: self.write(self.dynamic_law+'(law('+myidstr+'),'+p+')'+wherepart+'.')
				for p in data[1]: self.write('after(law('+myidstr+'),'+p+')'+wherepart+'.')
				for p in data[2]: self.write(self.difcons+'(law('+myidstr+'),'+p+')'+wherepart+'.')
			else:
				self.error("Error with size of dynamic law "+str(ac))
		self.current_meta_info = None
	
	def compile_impossible_laws(self,laws):
		for ac in laws:
			self.current_meta_info = ac[1]
			ac = ac[0]
			wherepart = self.return_compiled_where(ac[-3],ac[-2],ac[-1])
			data = self.extract_all(ac) #,2)
			myidstr = self.make_id(data[-1])
			#wherepart = self.return_compiled_where(data[-3],data[-2],data[-1])
			if len(data) == 5:
				for p in data[0]: self.write('impossible(law('+myidstr+'),'+p+')'+wherepart+'.')
				for p in data[1]: self.write(self.impossible_ifcons+'(law('+myidstr+'),'+p+')'+wherepart+'.')
			else:
				self.error("Error with size of impossible law "+str(ac))
		self.current_meta_info = None
	
	def compile_nonexecutable_laws(self,laws):
		for ac in laws:
			self.current_meta_info = ac[1]
			ac = ac[0]
			wherepart = self.return_compiled_where(ac[-3],ac[-2],ac[-1])
			data = self.extract_all(ac,0) #,3,0)
			myidstr = self.make_id(data[-1])
			#wherepart = self.return_compiled_where(data[-3],data[-2],data[-1])
			if len(data) == 6:
				for p in data[0]: self.write('nonexecutable(law('+myidstr+'),'+p+')'+wherepart+'.')
				for p in data[1]: self.write('nonexecutable(law('+myidstr+'),'+p+')'+wherepart+'.') #TODO:  _if ?
				for p in data[2]: self.write(self.nonexecutable_ifcons+'(law('+myidstr+'),'+p+')'+wherepart+'.') #TODO: Currently not supported
			else:
				self.error("Error with size of nonexecutable law "+str(ac))
		self.current_meta_info = None
	
	def compile_default_laws(self,laws):
		for ac in laws:
			self.current_meta_info = ac[1]
			ac = ac[0]
			wherepart = self.return_compiled_where(ac[-3],ac[-2],ac[-1])
			data = self.extract_all(ac,2) #,3,2)
			myidstr = self.make_id(data[-1])
			#wherepart = self.return_compiled_where(data[-3],data[-2],data[-1])
			if len(data) == 4:
					for p in data[0]: self.write('default('+p+')'+wherepart+'.')
			elif len(data) == 6:
				if len(data[1]) == 0 and len(data[2]) == 0:
					for p in data[0]: self.write('default('+p+')'+wherepart+'.')
				else:
					if len(data[2]) == 0 or len(data[1]) == 0:
						for p in data[0]: self.write('default(law('+myidstr+'),'+p+')'+wherepart+'.') #TODO: Currently not supported
						for p in data[1]: self.write(self.default_if+'(law('+myidstr+'),'+p+')'+wherepart+'.') #TODO: Currently not supported
						for p in data[2]: self.write(self.default_after+'(law('+myidstr+'),'+p+')'+wherepart+'.') #TODO: Currently not supported
					else:
						self.error("Error with size of default law "+str(ac))
				#for p in ifconspart: self.write('default_ifcons(law('+myidstr+'),'+p+').')
			else:
				self.error("Error with size of default law "+str(ac))
		self.current_meta_info = None

	def compile_inertial_laws(self,laws):
		for ac in laws:
			self.current_meta_info = ac[1]
			ac = ac[0]
			wherepart = self.return_compiled_where(ac[-3],ac[-2],ac[-1])
			if len(ac) == 4:
				self.current_vars = ac[-1]
				head = self.to_string_array(ac[0],True)
				#variables = ac[1]
				#myidstr = self.make_id(variables)
				if len(head) > 0:
					#if len(ifpart) == 0 and len(ifconspart) == 0:
						for p in head: self.write('inertial('+p+')'+wherepart+'.')
					#else:
					#	for p in head: self.write('inertial(law('+myidstr+'),'+p+').') #Currently not supported
					#	for p in ifpart: self.write('inertial_if(law('+myidstr+'),'+p+').') #Currently not supported
					#	for p in ifconspart: self.write('inertial_ifcons(law('+myidstr+'),'+p+').') #Currently not supported
			else:
				self.error("Error with inertial "+str(ac))
		self.current_meta_info = None
	
	def compile_initially_laws(self,laws):
		for ac in laws:
			self.current_meta_info = ac[1]
			ac = ac[0]
			wherepart = self.return_compiled_where(ac[-3],ac[-2],ac[-1])
			self.current_vars = ac[-1]
			if type(ac[0]) == list:
				for p in ac[0]:
					self.write('initially('+self.to_string(p,allow_actions=False)+')'+wherepart+'.')
			else:self.write('initially('+self.to_string(ac[0],allow_actions=False)+')'+wherepart+'.')
		self.current_meta_info = None
	
	def compile_goals(self,laws):
		for ac in laws:
			self.current_meta_info = ac[1]
			ac = ac[0]
			wherepart = self.return_compiled_where(ac[-3],ac[-2],ac[-1])
			self.current_vars = ac[-1]
			if type(ac[0]) == list:
				for p in ac[0]:
					self.write('finally('+self.to_string(p)+')'+wherepart+'.')
			else:self.write('finally('+self.to_string(ac[0])+')'+wherepart+'.')
		self.current_meta_info = None
			
	def compile_visibles(self,laws):
		for ac in laws:
			self.current_meta_info = ac[1]
			ac = ac[0]
			wherepart = self.return_compiled_where(ac[-3],ac[-2],ac[-1])
			data = self.extract_all(ac,1) #,3,1)
			myidstr = self.make_id(data[-1])
			#wherepart = self.return_compiled_where(data[-3],data[-2],data[-1])
			if len(data)== 7: # formula if after ifcons where bind
				if self.decoupled: self.write('observes_law(law('+myidstr+'))'+wherepart+'.')
				for p in data[0]: self.write('observes(law('+myidstr+'),'+p+')'+wherepart+'.')
				for p in data[1]: self.write('if(law('+myidstr+'),'+p+')'+wherepart+'.')
				for p in data[2]: self.write('after(law('+myidstr+'),'+p+')'+wherepart+'.')
				for p in data[3]: self.write('ifcons(law('+myidstr+'),'+p+')'+wherepart+'.')
			else:
				print len(data)
				self.error("Error with size of dynamic law "+str(ac))
		self.current_meta_info = None
		
		
	def compile_kill(self,a,b):
		if len(self.fluents) > 0:
			flu = self.fluents[0][0][0]
			if type(flu) == list:
				flu = flu[0]
		else:
			self.error("Error: No fluents known")
			return
		if a:
			self.write('impossible(-1,val('+flu+',false)). impossible(-1,val('+flu+',true)).')
		if b:
			self.write('nonexecutable(-1,val('+flu+',false)). nonexecutable(-1,val('+flu+',true)).')

	def return_compiled_where(self,wherepart,wherevar,var,optionals=None,check=True):
		if check:
			for a in var:
				if not a in wherevar:
					self.error("Warning: Variable "+str(a)+" not bound in "+str(wherevar)+"?",fatal=False)
		wherelist = []
		self.where_action_list = []
		self.where_fluent_list = []
		result = ''
		
		for par in wherepart:
			if par[0] == '#pred':
				if par[1] in var:
					self.error("Error: <where> contains Variable "+str(par[1])+" without context!", True)
				wherelist.append(self.to_string(par[1], tf=True))
			elif par[0] == '#act':
				self.where_action_list.append(par[1])
				if self.negated_actions:
					wherelist.append('action('+self.to_string(par[1], tf=True)+')')
				else:
					wherelist.append('action(act('+self.to_string(par[1], tf=True)+'))')
			elif par[0] == '#flu':
				self.where_fluent_list.append(par[1])
				if len(par[1]) == 3 and par[1][0] == 'fval':
					wherelist.append('domain('+self.to_string(par[1][1], tf=True)+','+self.to_string(par[1][2], tf=True)+')')
				else:
					wherelist.append('fluent('+self.to_string(par[1], tf=True)+')')
			else:
				self.error("Error: <where> "+str(par)+" unknown.")
				
		if len(wherelist) > 0 or type(optionals) == list:
			result = ' :- '
			commatime = False
			if type(wherelist) != list: wherelist = []
			if type(optionals) != list: optionals = []
			for par in wherelist + optionals:
				if commatime: result += ','+par
				else: commatime = True; result += par
				
				
		return result


