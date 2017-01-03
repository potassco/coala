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

	def __init__(self,ignorance=False,decoupled=False):
		#super(aspCom.AspCompiler,self).__init__(ignorance,decoupled)
		aspCom.AspCompiler.__init__(self, ignorance, decoupled)
		
		self.int_variables = []
		
			
	def compile(self,data,filenam):
		self.lawid = 1
		self.no_error = True
		self.string = ''
		
		self.filename = filenam   
		self.f = None
		
		self.reset_self()
		
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
			self.compile_integers(data['int'])
			self.compile_defined_fluents(data['defined_fluents'])
			self.compile_domains()
			
			print "f:",self.fluents
			data = self.get_integers_convert_data(data) # Needs to be done after fluents!
			print "f:",self.fluents
				
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
	
	def is_int_term(self,value):
		if type(value) == tuple and value[0] in ('fval','!=',"<=",">=","==","=",">","<","**","*","+","/"): #== '=':
			if self.is_int_term(value[1]): return True
			return self.is_int_term(value[2])
		elif type(value) == tuple and value[0] == '-':
			if len(value) > 2:
				self.error("Error with negation in "+str(value))
			value = value[1]
		#if value in self.current_vars and value in self.where_action_list:
		#	return False # It is an action instead
		for mint in self.int_variables:
			for sint in mint[0][0]:
				if self.is_fitting(value,sint,mint[0][-1]) >= 0:
					return True 
		return False
	
	def get_int_terms(self,value):
		if type(value) == tuple and value[0] in ('fval','!=',"<=",">=","==","=",">","<","**","*","+","/"): #== '=':
			ia = self.get_int_terms(value[1])
			ib = self.get_int_terms(value[2])
			return ia+ib
		for mint in self.int_variables:
			for sint in mint[0][0]:
				if self.is_fitting(value,sint,mint[0][-1]) >= 0:
					print "int term:",mint
					print "int term:",value
					return [value]
		return [] 	
			
	def get_integers_convert_data(self,data):
		res_var = []
		
		int_data = data['int']
		# Extract all Integer Variables...
		if type(int_data) == list:
			for sett in int_data:
				meta = sett[1]
				sett = sett[0]
				intret = None 
				if type(sett) == tuple:
					var = sett[0]
					vardom = sett[1]
					intall = []
					if type(var) == list:
						for fl in var:
							if type(fl) == tuple and fl[0] == '=':
								intall.append(fl[1])
							else:
								intall.append(fl)
					#flret = (flall,sett[1],sett[2],sett[3])
					intret = (intall,vardom,sett[-3],sett[-2],sett[-1])
					if not intret in res_var:
						res_var.append((intret,meta))
		
		self.int_variables = res_var
		
		# Transform all static and dynamic laws by replacing compairisons to ints by equations
			
		for ltype in ['static_laws','impossible_laws','nonexecutable_laws','goals']:
			replace = []
			for law in data[ltype]:
				
				law_int, changed_law = self.get_int_of_law(law,setting=True)
				if len(law_int) > 0:
					print law_int #TODO: here
					pass
				
				replace.append(changed_law)
				
			data[ltype] = replace
			
		
		for ltype in ['dynamic_laws','initially_laws']: # Laws that set something!
			replace = []
			for law in data[ltype]:
				
				law_int, changed_law = self.get_int_of_law(law,setting=False)
				if len(law_int) > 0:
					print law_int #TODO: here
					pass
				
				replace.append(changed_law)
				
			data[ltype] = replace
	
		return data
	
	def get_int_of_law(self,law,setting=False):
		data = law[0]
		meta = law[1]
		
		found_ints = []
		check = []
		for el in data[0]:
			print "el:",el,data
			ints = self.get_int_terms(el)
			print "ints:",ints
			
			if len(ints) > 0:
				for val in ints:
					vars = self.extract_vars(val)
					#TODO: Extract Variables
					myid = self.make_id(vars) 
					found_ints.append((val,myid))
					check.append("_math("+str(myid)+")")
			else:
				check.append(el)
		
		data_changed = [check]+list(data[1:])
		data_changed = tuple(data_changed)
		return found_ints, (data_changed,meta)
	
	def extract_vars(self,val):
		result = []
		if type(val) in [list,tuple]:
			for el in val:
				result += self.extract_vars(el)
		elif type(val) == str:
			if val[0].isupper():
				return [val[0]]
		return result
					
	def compile_integers(self,laws):	
		for ac in laws:
			self.current_meta_info = ac[1]
			ac = ac[0]
			domain = ac[1]
			wherepart = self.return_compiled_where(ac[-3],ac[-2],ac[-1])
			for sac in ac[0]:
				fl = self.to_string(sac,True)
				#fl_full = self.to_string(sac,False)
				#if len(ac[-1]) == 0:
					#if fl_full in self.actions_str:
					#	self.error("Error: Fluent "+fl+" was declared as an Action before!")
					#	if not self.ignorance: return
					#if fl_full in self.fluents_str:
					#	self.error("Warning: Fluent "+fl+" was declared twice",fatal=False)
					#	if not self.ignorance: return
					#self.fluents_str.append(fl_full)
				self.write('int(' + fl + ')'+wherepart+'.')
				if domain != None and type(domain) == tuple and len(domain) == 2:
					low = self.to_string(domain[0],True)
					high = self.to_string(domain[1],True)
					self.write('int_domain(' + fl + ',' + low + ',' + high + ')'+wherepart+'.')
		self.current_meta_info = None	
			
			
			
			
			
			
			
	# Some space for you to make notes.	
	
	