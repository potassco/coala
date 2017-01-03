#
# Copyright (c) 2016, Christian Schulz-Hanke
#
import sys
import coala.bc_legacy.aspCompiler as aspCom

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

class AspCompiler(aspCom.AspCompiler):

	def __init__(self,ignorance=False,decoupled=False,agent=False):
		#super(aspCom.AspCompiler,self).__init__(ignorance,decoupled)
		aspCom.AspCompiler.__init__(self, ignorance, decoupled)
		self.ignore_roles_for_agents = agent
		self.visibles_are_fluents = True
		self.visibles = None
		self.there_were_roles = False
		self.roles = []
		self.compiled_domains = []
		self.redefine_fluents_on_visible = False
		
		self.global_actions = []
		self.global_fluents = []
		self.params = []
		#self.params_bound = []
		
	# Some space for you to make notes.	
	
	def apply_parameters(self,data,role):
		to_check = ['dynamic_laws',
			'default_laws',
			'static_laws',
			'visible_laws',
			'actions',
			'preds',
			'impossible_laws',
			'fluents',
			'initially_laws',
			'inertial_laws',
			'defined_fluents',
			'goals',
			'nonexecutable_laws']
		for dtype in to_check:
			if dtype in data:
				li = data[dtype]
				#print "pre:",data[dtype]
				if type(li) == list:
					#for elem in li:
					for i in range(len(li)):
						li[i] = (self.param_translate(li[i][0],role=role),li[i][1])
				#print "fin:",data[dtype]
						
		return data
	
	def param_translate(self,element,initial=True,role=None):
		#print element
		if type(element) == tuple:
			le = list(element)
			bindings = []
			for i in range(len(le)):
				le[i],new_bindings = self.param_translate(le[i], False)
				bindings += new_bindings
			if initial:
				#Todo: BIND!
				bindagent = False
				if not role is None:
					for (x,y) in bindings:
						le[-3].append(('#pred','param(_AGENT,'+x+','+y+')'))
						if not bindagent:
							le[-3].append(('#pred','agent(_AGENT,'+role+')'))
							bindagent = True
						le[-2].append('_AGENT')
						le[-2].append(y)
						le[-1].append('_AGENT')
						le[-1].append(y)
				else:
					for (x,y) in bindings:
						le[-3].append(('#pred','param('+x+','+y+')'))
						le[-2].append(y)
						le[-1].append(y)
				return tuple(le)
			else:
				return tuple(le),bindings
		elif not initial:
			if type(element) == list:
				bindings = []
				for i in range(len(element)):
					element[i],new_bindings = self.param_translate(element[i], False)
					bindings += new_bindings
				return element,bindings
			elif type(element) == str:
				if element in self.params:
					l = self.param_to_var(element)
					return l,[(element,l)]
				return element,[]
			else: #Convert to str? 
				if element is None:
					return element,[]
				if str(element) in self.params:
					l = self.param_to_var(str(element))
					return l,[(str(element),l)]
				return element,[]
		return element
	
	def param_to_var(self,value):
		return "_PARAM_"+value.upper()

	def is_parameter(self,value):
		if len(self.params) > 0:
			for p in self.params:
				if str(value) == str(p): return True
		return False
		
	def is_visible_fluent(self,value):
		if self.visibles_are_fluents: return False
		if type(value) == tuple and value[0] == '-':
			if len(value) > 2:
				self.error("Error with negation in "+str(value))
			value = value[1]
		for flu in self.visibles:
			for sflu in flu[0][0]:
				if self.is_fitting(value,sflu,flu[-1]):
					return True 
		return False
	
	def to_string_array(self,value,tf=False,after_part=False,role=None,add_role=False,first_layer=True):
		#if first_layer: self.params_bound = [] Todo: remove
		result = []
		
		if type(value) == tuple or type(value) == list:
			for at in value:
				result.append(self.to_string(at,tf,after_part,role=role,add_role=add_role,first_layer=False))
		elif value != None:
			result = [self.to_string(value,tf,after_part,role=role,add_role=add_role,first_layer=False)]
		
		return result
	
	#def to_string(self,value,tf=False,after_part=False,allow_actions=True,role=None,add_role=False):
	def to_string(self,value,tf=False,after_part=False,allow_actions=True,role=None,add_role=False,first_layer=True):
		#if first_layer: self.params_bound = [] #TODO: remove first_layer
		result = ''
		
		if type(value) == tuple:
			if value[0] == '-':
				if len(value) > 3:
					self.error('ERROR: Odd Negation '+str(value))
					return str(value)
				elif len(value) == 3:
					result = self.to_string(value[1],True,after_part,allow_actions)+value[0]+self.to_string(value[2],True,after_part,allow_actions,first_layer=False)
				elif not tf:
					if type(value[1]) == tuple and value[1][0] == '=':
						val = self.to_string(value[1][1],True,after_part,allow_actions,first_layer=False)
						equ = self.to_string(value[1][2],True,after_part,allow_actions,first_layer=False)
						at_type = self.get_atom_type(value[1][1], allow_actions)
						if at_type == "a":
							self.error("ERROR: Actions are not multivalued and cannot be negated! -"+val+"="+equ+" is not allowed!")
						elif at_type is None:
							if not self.ignore_undefined: self.error("ERROR: Fluent "+val+" was not declared before!!")
							#TODO: postdeclaration?
						return 'neg_val('+val+','+equ+')'
# 						if not self.is_fluent(value[1][1]):
# 							if allow_actions and self.is_action(value[1][1]):
# 								self.error("ERROR: Actions are not multivalued and cannot be negated! -"+val+"="+equ+" is not allowed!")
# 								#if self.negated_actions:
# 								#	return 'act('+val+',false)'
# 								#else:
# 								#	self.error("ERROR: Actions cannot be negated! -"+val+" is not allowed!")
# 							else:
# 								if not self.ignore_undefined: self.error("ERROR: Fluent "+val+" was not declared before!!")
# 								#TODO: postdeclaration?
# 								return 'neg_val('+val+','+equ+')'
# 						return 'neg_val('+val+','+equ+')'
					else:
						val = self.to_string(value[1],True,after_part,allow_actions,first_layer=False)
						is_vis = self.is_visible_fluent(value[1])
						at_type = self.get_atom_type(value[1], allow_actions)
						if at_type == "f":
							#return 'val('+val+',false)'
							if not role is None and not is_vis: return 'val(ag(_AGENT,'+val+'),false)'
							else: return 'val('+val+',false)'
						elif at_type == "a":
							if self.negated_actions:
								#return 'act('+val+',false)'
								if not role is None and not is_vis: return 'act(ag(_AGENT,'+val+'),false)'
								else: return 'act('+val+',false)'
							else:
								self.error("ERROR: Actions cannot be negated! -"+val+" is not allowed!")
								return 'val('+val+',false)'
						else:
							if not self.ignore_undefined: self.error("ERROR: Fluent "+val+" was not declared before!!")
							#return 'val('+val+',false)'
							if not role is None and not is_vis: return 'val(ag(_AGENT,'+val+'),false)'
							else: return 'val('+val+',false)'
							#TODO: postdeclaration?
# 						if not self.is_fluent(value[1]):
# 							if allow_actions and self.is_action(value[1]):
# 								if self.negated_actions:
# 									if not role is None and not is_vis: return 'act(ag(_AGENT,'+val+'),false)'
# 									else: return 'act('+val+',false)'
# 								else:
# 									self.error("ERROR: Actions cannot be negated! -"+val+" is not allowed!")
# 							else:
# 								if not self.ignore_undefined: self.error("ERROR: Fluent "+val+" was not declared before!!")
# 								if not role is None and not is_vis: return 'val(ag(_AGENT,'+val+'),false)'
# 								else: return 'val('+val+',false)'
# 								#TODO: postdeclaration?
# 						if not role is None and not is_vis: return 'val(ag(_AGENT,'+val+'),false)'
# 						else: return 'val('+val+',false)'
				else:
					result = '-'+self.to_string(value[1],True,after_part,allow_actions,add_role=add_role,first_layer=False)
			elif value[0] == 'fval' and len(value) == 3:
				if not tf:
					if not role is None and not self.is_visible_fluent(value[1]): 
						return 'val(ag(_AGENT,'+self.to_string(value[1], True,after_part,allow_actions,first_layer=False)+")," \
							+self.to_string(value[2], True,after_part,allow_actions,first_layer=False)+")"
					else: 
						return 'val('+self.to_string(value[1], True,after_part,allow_actions)+"," \
							+self.to_string(value[2], True,after_part,allow_actions,first_layer=False)+")"
				else:
					if not role is None and not self.is_visible_fluent(value[1]): 
						return 'ag(_AGENT,'+self.to_string(value[1], True,after_part,allow_actions,first_layer=False)+")"
					else: 
						return self.to_string(value[1], True,after_part,allow_actions)
				#	result = self.to_string(value[1],True,after_part,allow_actions,add_role=add_role,first_layer=False) \
				#		+value[0]+self.to_string(value[2],True,after_part,allow_actions,add_role=add_role,first_layer=False)
					#return self.to_string(value[1], True) # only return the fluent, not the equivalence
			elif value[0] == '_':
				result = 'not '+self.to_string(value[1],True,after_part,allow_actions,first_layer=False)
			elif len(value)==3 and value[0] in ('!=',"<=",">=","==","=",">","<","**","*","+","/"):
				result = self.to_string(value[1],True,after_part,allow_actions,first_layer=False)+value[0] + \
					self.to_string(value[2],True,after_part,allow_actions,first_layer=False)
			else:
				result = self.to_string(value[0],True,after_part,allow_actions,first_layer=False)+'('
				ind = 1
				for i in range(1,len(value)):
					if ind == 0:
						result += ','
					result += self.to_string(value[i],True,after_part,allow_actions,first_layer=False)
					ind = 0
				result += ')'
				if not tf:
					is_vis = self.is_visible_fluent(value)
					at_type = self.get_atom_type(value, allow_actions)
					if at_type == "f":
						#return 'val('+result+',true)'
						if not role is None and not is_vis: return 'val(ag(_AGENT,'+result+'),true)'
						else: return 'val('+result+',true)'
					elif at_type == "a":
						if self.negated_actions:
							if after_part:
								#return 'act('+result+',true)'
								if not role is None and not is_vis: return 'act(ag(_AGENT,'+result+'),true)'
								else: return 'act('+result+',true)'
							else:
								return str(result)
						else:
							#return 'act('+result+')'
							if not role is None and not is_vis: return 'act(ag(_AGENT,'+result+'))'
							else: return 'act('+result+')'
					else:
						if not self.ignore_undefined: self.error("ERROR: Fluent "+result+" was not declared!!")
						#return 'val('+result+',true)'
						if not role is None and not is_vis: return 'val(ag(_AGENT,'+result+'),true)'
						else: return 'val('+result+',true)'
						#TODO: postdeclaration?
# 					if self.is_fluent(value):
# 						if not role is None and not is_vis: return 'val(ag(_AGENT,'+result+'),true)'
# 						else: return 'val('+result+',true)'
# 					elif allow_actions and self.is_action(value):
# 						if self.negated_actions:
# 							if after_part:
# 								if not role is None and not is_vis: return 'act(ag(_AGENT,'+result+'),true)'
# 								else: return 'act('+result+',true)'
# 							else:
# 								return str(result)
# 						else:
# 							if not role is None and not is_vis: return 'act(ag(_AGENT,'+result+'))'
# 							else: return 'act('+result+')'
# 					else:
# 						if not self.ignore_undefined: self.error("ERROR: Fluent "+result+" was not declared!!")
# 						if not role is None and not is_vis: return 'val(ag(_AGENT,'+result+'),true)'
# 						else: return 'val('+result+',true)'
# 						#TODO: postdeclaration?
				elif add_role and not role is None:
					if self.is_fluent(value) and not self.is_visible_fluent(value):
						return 'ag(_AGENT,'+result+')'
				
		elif type(value) == list:
			mind = 1
			for el in value:
				if mind == 0:
					result += ','
				result += self.to_string(el,tf,after_part,first_layer=False)
				mind = 0
		elif type(value) == str and not tf: 
			at_type = self.get_atom_type(value, allow_actions)
			if at_type == "f":
				#return 'val('+value+',true)'
				is_vis = self.is_visible_fluent(value)
				if not role is None and not is_vis: return 'val(ag(_AGENT,'+value+'),true)'
				else: return 'val('+value+',true)'
			elif at_type == "a":
				if self.negated_actions:
					if after_part:
						return 'act('+value+',true)' #TODO: Roles + Negated
					else:
						return value
				else:
					#result = 'act('+value+')'
					if not role is None: result = 'act(ag(_AGENT,'+value+'))' 
					else: result = 'act('+value+')'
			else:
				if not self.ignore_undefined: self.error("ERROR: The fluent or other "+str(value)+" was not defined.")
				#return 'val('+value+',true)'
				if not role is None and not self.is_visible_fluent(value): return 'val(ag(_AGENT,'+value+'),true)'
				else: return 'val('+value+',true)'
			
# 			if self.is_fluent(value):
# 				is_vis = self.is_visible_fluent(value)
# 				if not role is None and not is_vis: return 'val(ag(_AGENT,'+value+'),true)'
# 				else: return 'val('+value+',true)'
# 			elif allow_actions and self.is_action(value):
# 				if self.negated_actions:
# 					if after_part:
# 						return 'act('+value+',true)'
# 					else:
# 						return value
# 				else:
# 					if not role is None: result = 'act(ag(_AGENT,'+value+'))' 
# 					else: result = 'act('+value+')'
# 			else: 
# 				if not self.ignore_undefined: self.error("ERROR: The fluent or other "+str(value)+" was not defined.")
# 				if not role is None and not self.is_visible_fluent(value): return 'val(ag(_AGENT,'+value+'),true)'
# 				else: return 'val('+value+',true)'
		elif type(value) == str:
			#if self.is_parameter(value):
			#	par = str(value)
			#	if not par in self.params_bound: self.params_bound.append(par)
			#	result = self.param_to_var(par)
			#el
			if add_role and not role is None and not self.is_visible_fluent(value):
				result = 'ag(_AGENT,'+str(value)+')'
			else:
				result = str(value)
		else:
			self.error("ERROR: Unexpected object type: "+str(type(value))+" of "+str(value))
			result = str(value)
		
		return result
	
	def extract_all(self,data,after=None,role=None):
		no_to_str = len(data) - 3
		result = []
		if type(data) == list:
			return [self.to_string(data,role=role)]
		self.current_vars = data[-1]
		if not role is None: self.current_vars.append("_AGENT")
		for i in range(len(data)):
			if no_to_str != None and no_to_str <= i: 
				result.append(data[i])
			elif after != None and after == i:
				result.append(self.to_string_array(data[i],after_part=True,role=role))
			else: 
				result.append(self.to_string_array(data[i],role=role))
		return result
	
	def compile(self,data,filenam):
		self.lawid = 1
		self.no_error = True
		self.there_were_roles = False
		self.roles = []
		self.compiled_domains = []
		self.string = ''
		
		self.actions = []
		self.fluents = []
		self.visibles = []
		
		self.filename = filenam   
		self.f = None
		#print "FLS: ",self.fluents
		
		self.reset_self()
		
		if self.tofile:
			try:
				self.f = open(self.filename,'w')
			except:
				print >> sys.stderr, "% Could not open file "+str(self.filename)
			
		self.read_errors(data['errors'])
		
		try:
			
			
			for tup in data['roles']:
				roledata = data['roles'][tup]
				if len(roledata) > 0:
					self.roles.append(tup)
					self.there_were_roles = True
				self.compile_data(data['roles'][tup],role=tup)
			
			self.compile_data(data)
			
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
	
	def compile_data(self,data,separators=True,role=None):
		
		if 'params' in data:
			self.params = data['params']
			self.compile_parameters(role)
			
		if self.ignore_roles_for_agents:
			role = None
			
		if 'params' in data:
			if len(self.params) > 0:
				data = self.apply_parameters(data,role)
			#self.compile_parameters(role)
			
		if not role is None:
			#print params
			self.compile_role(role)
			self.actions = data['actions']
			self.global_actions += self.actions
			self.fluents = self.clean_fluents(data['fluents']+data['defined_fluents']+data['visible_laws'])
			self.global_fluents += self.fluents
		else:
			self.global_actions += data['actions']
			self.global_fluents += self.clean_fluents(data['fluents']+data['defined_fluents']+data['visible_laws'])
			self.actions = self.global_actions
			self.fluents = self.global_fluents 
			#self.params = []
			#self.params_bound = []
			
		
		#self.actions += data['actions']
		#self.fluents += self.clean_fluents(data['fluents']+data['defined_fluents']+data['visible_laws'])
		self.visibles += self.clean_fluents(data['visible_laws'])
		
		self.compile_others(data['others'])
	
		self.compile_predicates(data['preds']) 
		self.compile_actions(data['actions'],role) 
		self.compile_fluents(data['fluents'],role)
		self.compile_defined_fluents(data['defined_fluents'],role)
		self.compile_visibles(data['visible_laws'],role)
		self.compile_domains(role)
			
		if separators: 
			if self.text_written:
				self.write('')
				self.text_written = False
			
		self.compile_static_laws(data['static_laws'],role)
			
		if separators: 
			if self.text_written:
				self.write('')
				self.text_written = False
		
		self.compile_dynamic_laws(data['dynamic_laws'],role)
			
		if separators: 
			if self.text_written:
				self.write('')
				self.text_written = False
		
		self.compile_impossible_laws(data['impossible_laws'],role)
		self.compile_nonexecutable_laws(data['nonexecutable_laws'],role)
		self.compile_default_laws(data['default_laws'],role)
		self.compile_inertial_laws(data['inertial_laws'],role)
			
		if separators: 
			if self.text_written:
				self.write('')
				self.text_written = False
			
		self.compile_initially_laws(data['initially_laws'],role)
		self.compile_goals(data['goals'],role)
		
		if data['killEncoding'][0] == 1 or data['killEncoding'][1] == 1:
			self.compile_kill(data['killEncoding'][0], data['killEncoding'][1],role)
		
	def compile_role(self,role):
		self.write('role(' + str(role) + ').')
		
	def compile_parameters(self,role):
		if not self.ignore_roles_for_agents: 
			agstr='AG,'
			agstr2=agstr
		else: 
			agstr=''
			agstr2='_,'
		length = len(self.params)
		if length > 0:
			for i in range(length):
				p = self.params[i]
				hlp = "_,"*i+'V'+",_"*(length-i-1)
				self.write('param('+agstr+str(p)+',V) :- agent('+agstr2+str(role)+'('+hlp+')).')
			self.write('agent('+agstr+str(role)+') :- agent('+agstr2+str(role)+'(_'+',_'*(length-1)+')).')
			####self.write('param_length('+str(role)+','+str(length)+').')
		# agent(X). role(X,role).
	
	def compile_actions(self,laws,role):
		for ac in laws:
			self.current_meta_info = ac[1]
			ac = ac[0]
			wherepart = self.return_compiled_where(ac[-3],ac[-2],ac[-1],role=role)
			for sac in ac[0]:
				act = self.to_string(sac,True)
				if len(ac[-1]) == 0:
					if act in self.actions_str:
						self.error("Warning: Action "+act+" was declared twice",fatal=False)
					self.actions_str.append(act)	
				if not role is None:
					act = "ag(_AGENT,"+act+")" 
				if self.negated_actions:
					self.write('action(' + act + ')'+wherepart+'.')
				else:
					self.write('action(act(' + act + '))'+wherepart+'.')
		self.current_meta_info = None
	
	def compile_fluents(self,laws,role):
		for ac in laws:
			self.current_meta_info = ac[1]
			ac = ac[0]
			wherepart = self.return_compiled_where(ac[-3],ac[-2],ac[-1],role=role)
			for sac in ac[0]:
				fl = self.to_string(sac,True,role=role)
				fl_full = self.to_string(sac,False,role=role)
				if not role is None:
					fl = 'ag(_AGENT,'+fl+')'
					fl_full = 'ag(_AGENT,'+fl_full+')'
				self.add_domain(sac,ac,fl)
				if len(ac[-1]) == 0:
					if fl_full in self.actions_str:
						self.error("Error: Fluent "+fl+" was declared as an Action before!")
						if not self.ignorance: return
					if fl_full in self.fluents_str:
						self.error("Warning: Fluent "+fl+" was declared twice",fatal=False)
						if not self.ignorance: return
					self.fluents_str.append(fl_full)
				#if not role is None: self.write('fluent(ag(_AGENT,' + fl + '))'+wherepart+'.') 
				#else: 
				self.write('fluent(' + fl + ')'+wherepart+'.')
		self.current_meta_info = None
	
	def compile_defined_fluents(self,laws,role):
		for ac in laws:
			self.current_meta_info = ac[1]
			ac = ac[0]
			wherepart = self.return_compiled_where(ac[-3],ac[-2],ac[-1],role=role)
			for sac in ac[0]:
				fl = self.to_string(sac,True,role=role)
				fl_full = self.to_string(sac,False,role=role)
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
		
	def compile_visibles(self,laws,role=None):
		for ac in laws:
			self.current_meta_info = ac[1]
			ac = ac[0]
			self.current_vars = ac[-1]
			for sac in ac[0]:
				if self.visibles_are_fluents:
					fl = self.to_string(sac,True,role=role,add_role=True)
				else:
					fl = self.to_string(sac,True)
				#fl = self.to_string(sac,False)
				###self.add_domain(sac,ac,fl)
			####data = self.extract_all(ac,1,role=role) #,3,1)
			#myidstr = self.make_id(data[-1])
			#wherepart = self.return_compiled_where(data[-3],data[-2],data[-1],role=role)
			wherepart = self.return_compiled_where(ac[-3],ac[-2],ac[-1])#,role=role)
			wherepart_role = self.return_compiled_where(ac[-3],ac[-2],ac[-1],role=role)
			if len(ac)== 7: # formula if after ifcons where bind
				#if self.decoupled: self.write('observes_law(law('+myidstr+'))'+wherepart+'.')
				#for p in data[0]: self.write('observes(law('+myidstr+'),'+p+')'+wherepart+'.')
				#for p in data[1]: self.write('if(law('+myidstr+'),'+p+')'+wherepart+'.')
				#for p in data[2]: self.write('after(law('+myidstr+'),'+p+')'+wherepart+'.')
				#for p in data[3]: self.write('ifcons(law('+myidstr+'),'+p+')'+wherepart+'.')
				if ac[1] is not None and len(ac[1]) > 0:
					if role is not None: myidstr = self.make_id(ac[-1]+['_AGENT'])
					else: myidstr = self.make_id(ac[-1])
					for p in ac[0]: 
						fl = self.to_string(p,True)
						
						if self.redefine_fluents_on_visible:
							if not role is None and self.visibles_are_fluents: self.write('fluent(ag(_AGENT,' + fl + '))'+wherepart_role+'.')
							else: self.write('fluent(' + fl + ')'+wherepart+'.')
						
						if not self.ignore_roles_for_agents: 
							if role is not None: self.write('visible(law('+myidstr+'),_AGENT,'+fl+')'+wherepart_role+'.')
							else: self.write('visible(law('+myidstr+'),_none,'+fl+')'+wherepart_role+'.')
						
					for p in ac[1]: 
						fl = self.to_string(p, False, True, True)
						if not self.ignore_roles_for_agents: 
							if role is not None: self.write('if(law('+myidstr+'),_AGENT,'+fl+')'+wherepart_role+'.')
							else: self.write('if(law('+myidstr+'),_none,'+fl+')'+wherepart_role+'.')
				else:
					for p in ac[0]: 
						fl = self.to_string(p,True)
						
						if self.redefine_fluents_on_visible:
							if not role is None and self.visibles_are_fluents: self.write('fluent(ag(_AGENT,' + fl + '))'+wherepart_role+'.')
							else: self.write('fluent(' + fl + ')'+wherepart+'.')
							
						if not self.ignore_roles_for_agents: 
							if role is not None: self.write('visible(_AGENT,'+fl+')'+wherepart_role+'.')
							else: self.write('visible(_none,'+fl+')'+wherepart_role+'.')
						
				
			else:
				#print len(ac)
				self.error("Error with size of dynamic law "+str(ac))
		self.current_meta_info = None
				
	def compile_domains(self,role):
		for fld in self.flu_domains:
			if fld in self.compiled_domains:
				continue
			self.compiled_domains.append(fld)	
			result = ""
			for data in self.flu_domains[fld]:
				if len(data) == 4:
					result+='domain('+fld+','+data[0][0]+')'+self.return_compiled_where(data[-3],data[-2],data[-1],role=role)+'. '
				else:
					self.error("Error with domain "+str(data))
			self.write(result)
	
	def compile_static_laws(self,laws,role):
		for ac in laws: #TODO error with negative heads!
			self.current_meta_info = ac[1]
			ac = ac[0]
			wherepart = self.return_compiled_where(ac[-3],ac[-2],ac[-1],role=role)
			data = self.extract_all(ac,role=role)#,3)
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
	
	def compile_dynamic_laws(self,laws,role):
		for ac in laws:
			self.current_meta_info = ac[1]
			ac = ac[0]
			wherepart = self.return_compiled_where(ac[-3],ac[-2],ac[-1],role=role)
			data = self.extract_all(ac,1,role=role) #3,1)
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
	
	def compile_impossible_laws(self,laws,role):
		for ac in laws:
			self.current_meta_info = ac[1]
			ac = ac[0]
			wherepart = self.return_compiled_where(ac[-3],ac[-2],ac[-1],role=role)
			data = self.extract_all(ac,role=role) #,2)
			myidstr = self.make_id(data[-1])
			#wherepart = self.return_compiled_where(data[-3],data[-2],data[-1])
			if len(data) == 5:
				for p in data[0]: self.write('impossible(law('+myidstr+'),'+p+')'+wherepart+'.')
				for p in data[1]: self.write(self.impossible_ifcons+'(law('+myidstr+'),'+p+')'+wherepart+'.')
			else:
				self.error("Error with size of impossible law "+str(ac))
		self.current_meta_info = None
	
	def compile_nonexecutable_laws(self,laws,role):
		for ac in laws:
			self.current_meta_info = ac[1]
			ac = ac[0]
			wherepart = self.return_compiled_where(ac[-3],ac[-2],ac[-1],role=role)
			data = self.extract_all(ac,0,role=role) #,3,0)
			myidstr = self.make_id(data[-1])
			#wherepart = self.return_compiled_where(data[-3],data[-2],data[-1])
			if len(data) == 6:
				for p in data[0]: self.write('nonexecutable(law('+myidstr+'),'+p+')'+wherepart+'.')
				for p in data[1]: self.write('nonexecutable(law('+myidstr+'),'+p+')'+wherepart+'.')
				for p in data[2]: self.write(self.nonexecutable_ifcons+'(law('+myidstr+'),'+p+')'+wherepart+'.') #TODO: Currently not supported
			else:
				self.error("Error with size of nonexecutable law "+str(ac))
		self.current_meta_info = None
	
	def compile_default_laws(self,laws,role):
		for ac in laws:
			self.current_meta_info = ac[1]
			ac = ac[0]
			wherepart = self.return_compiled_where(ac[-3],ac[-2],ac[-1],role=role)
			data = self.extract_all(ac,2,role=role) #,3,2)
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

	def compile_inertial_laws(self,laws,role):
		for ac in laws:
			self.current_meta_info = ac[1]
			ac = ac[0]
			wherepart = self.return_compiled_where(ac[-3],ac[-2],ac[-1],role=role)
			if len(ac) == 4:
				self.current_vars = ac[-1]
				head = self.to_string_array(ac[0],True,role=role,add_role=True)
				#head = self.to_string_array(ac[0],False,role=role)
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
	
	def compile_initially_laws(self,laws,role):
		for ac in laws:
			self.current_meta_info = ac[1]
			ac = ac[0]
			wherepart = self.return_compiled_where(ac[-3],ac[-2],ac[-1],role=role)
			self.current_vars = ac[-1]
			if type(ac[0]) == list:
				for p in ac[0]:
					self.write('initially('+self.to_string(p,allow_actions=False,role=role)+')'+wherepart+'.')
			else:self.write('initially('+self.to_string(ac[0],allow_actions=False,role=role)+')'+wherepart+'.')
		self.current_meta_info = None
	
	def compile_goals(self,laws,role):
		for ac in laws:
			self.current_meta_info = ac[1]
			ac = ac[0]
			wherepart = self.return_compiled_where(ac[-3],ac[-2],ac[-1],role=role)
			self.current_vars = ac[-1]
			if type(ac[0]) == list:
				for p in ac[0]:
					self.write('goal('+self.to_string(p,role=role)+')'+wherepart+'.')
			else:self.write('goal('+self.to_string(ac[0],role=role)+')'+wherepart+'.')
		self.current_meta_info = None
		
	def compile_kill(self,a,b,role):
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
			
			
	def return_compiled_where(self,wherepart,wherevar,var,optionals=None,check=True,role=None):
		if check:
			for a in var:
				if not a in wherevar:
					self.error("Warning: Variable "+str(a)+" not bound in "+str(wherevar)+"?",fatal=False)
		wherelist = []
		self.where_action_list = []
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
				if len(par[1]) == 3 and par[1][0] == 'fval':
					wherelist.append('domain('+self.to_string(par[1][1], tf=True)+','+self.to_string(par[1][2], tf=True)+')')
				else:
					wherelist.append('fluent('+self.to_string(par[1], tf=True)+')')
			else:
				self.error("Error: <where> "+str(par)+" unknown.")
				
		if not role is None and not "_AGENT" in wherevar:
			wherelist.append("agent(_AGENT,"+str(role)+")")
				
		if len(wherelist) > 0 or type(optionals) == list:
			result = ' :- '
			commatime = False
			if type(wherelist) != list: wherelist = []
			if type(optionals) != list: optionals = []
			for par in wherelist + optionals:
				if commatime: result += ','+par
				else: commatime = True; result += par
				
				
		return result