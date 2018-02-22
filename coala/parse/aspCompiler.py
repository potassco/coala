#
# Copyright (c) 2016, Christian Schulz-Hanke
#
import sys
import aspCompiler_legacy as aspCom
import os
import parse_objects

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

# Adds dictionary / list structures recursively
def combine_structures(struc,tocomb):
	result = struc
	if type(result) == dict and type(tocomb) == dict:
		for x in tocomb:
			if not x in result:
				result[x] = tocomb[x]
			else:
				result[x] = combine_structures(result[x], tocomb[x])
	elif type(result) == list:
		if type(tocomb) == list:
			for x in tocomb:
				if not x in result:
					result.append(x)
		else:
			result.append(tocomb)
	else:
		result = [result,tocomb]
	return result
		

class AspCompiler(aspCom.AspCompiler):

	def __init__(self,ignorance=False,decoupled=False):
		#super(aspCom.AspCompiler,self).__init__(ignorance,decoupled)
		aspCom.AspCompiler.__init__(self, ignorance, decoupled)
		
		self.int_variables = []
		self.arith_id = 1
		self.arith_helper_id = 1
		
	def next_arith_id(self):
		myid = self.arith_id
		self.arith_id += 1
		return myid
		
	def next_arith_helper_id(self):
		myid = self.arith_id
		self.arith_id += 1
		return myid
		
	def get_clean_fluents(self,data):
		result = []
		for el in data:
			result += el.get_fluents_domains()
		
		#print "Fluent Domains:"+",".join(x.__class__.__name__+":"+str(x) for x in result)
		
		all_dom = []
		dom = {"others":[]}
		full_fluents = []
		for d in result:
			text = d.print_facts()
			if text in all_dom: continue
			else: all_dom.append(text)
			fluent = d.get_domain_fluent()
			full_fluents.append(fluent)
			fluent_string = fluent.print_facts()
			variables = d.get_variables()
			
			if len(variables) == 0:
				if fluent_string in dom: dom[fluent_string].append(d)
				else: dom[fluent_string] = [d,]
			else:
				dom["others"].append(d)
			
		#for x in dom:
		#	if x in self.flu_domains:
		#		if type(x)==list:
		#			for y in x:
		#				)
		#		else:
		#			if not x in self.flu_domains[x]
		#	else:
		#		self.flu_domains[x] = dom[x]
		self.flu_domains = combine_structures(self.flu_domains,dom)
		self.fluents += full_fluents
		#self.flu_domains = dom
		#self.fluents = full_fluents
		#print "domains:",dom
	
	def get_clean_actions(self,data):
		result = []
		for el in data:
			result += el.get_actions()
		self.actions = result
	
	def get_clean_integers(self,data):
		result = []
		integer_ids = []
		for el in data:
			re = el.get_integers()
			result += re
			for x in re:
				integer_ids += x.get_bottom_elements()
		self.integers = result
		self.integer_ids = integer_ids
	
# 	def update_mark(self,data):
# 		for key in data:
# 			for a in data[key]:
# 				if key in ['static_laws',
# 					'dynamic_laws',
# 					'impossible_laws',
# 					'nonexecutable_laws',
# 					'default_laws',
# 					'inertial_laws']:
# 					result= a.mark_update_all(False)
# 					if result is not None:
# 						print "!!! marked:",result  #TODO: Remove
# 						pass
# 				#else:
# 				#	result= a.mark_all(True)
# 				#	if result is not None:
# 				#		print >> sys.stderr, "% Error! Arithmetic Part in non-law"
# 		return data
	
	def update_data(self, data):
		update_results = []
		for key in data:
			if key not in ["killEncoding","roles","errors"]:
				result = []
				for a in data[key]:
					upd_result = a.update(actions=self.actions,fluents=self.fluents,integers=self.integers, \
						integer_ids=self.integer_ids,idfunction=self.next_id,arith_idfunction=self.next_arith_id, \
						arith_helper_idfunction=self.next_arith_helper_id,law_type=key)
					update_results.append(upd_result)
					res = a.simplify(negation=False)
					if res is not None:
						result.append(res)
				data[key] = result
		data = self.update_evaluate_result(update_results,data)
		return data

	def update_evaluate_result(self,update,data):
		arith = []
		arith_helper = []
		for up in update:
			arith += up.arithmetic_laws
			x = up.get("arithmetic_divisions")
			if x is not None:
				arith_helper += x 
		#print arith
		data["arithmetic_laws"] = arith
		data["arithmetic_helper_laws"] = arith_helper
		
		changed_int_list = []
		for up in update:
			for changedint in up.integers_changed_to_fluents:
				changed_int_list.append(changedint)
		if len(changed_int_list) > 0:
			self.get_clean_fluents(changed_int_list)
		#		data["fluents"].append(changedint)
		
		return data
		
	
	def write(self,data):
		self.text_written = True
		if type(data) == list:
			content = os.linesep.join(data)+os.linesep
		else:
			content = str(data)+os.linesep
		if self.return_string:
			self.string += content
		if not self.tofile:
			if not self.silent and self.debug:
				if type(data) == list:
					print os.linesep.join(data)
				else:
					print str(data)
			return
		try:
			self.f.write(content)
		except:
			print >> sys.stderr, "% ERRRRRRR"
			if not self.ignorance:
				raise
			
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
			#self.actions = data['actions']
			self.get_clean_actions(data['actions'])
			self.get_clean_fluents(data['fluents']+data['defined_fluents'])
			self.get_clean_integers(data['integers'])
			#print "fluents:", "; ".join(str(x) for x in self.fluents)
			#print "actions:","; ".join(str(x) for x in self.actions)
			self.compile_others(data['others'])
			
			###data = self.update_mark(data)
			data = self.update_data(data)
			
			if self.debug: self.print_data(data)
		
			#print "Construction Zone"
		
			self.compile_predicates(data['preds']) 
			self.compile_actions(data['actions']) 
			self.compile_fluents(data['fluents'])
			self.compile_integers(data['integers'])
			self.compile_defined_fluents(data['defined_fluents'])
			
			#### translationb counter
			#print "Uncharted Territory"
			
			self.compile_domains()
			
			data = self.get_integers_convert_data(data) # Needs to be done after fluents!
				
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
				
			if "arithmetic_laws" in data:
				self.compile_simple(data['arithmetic_laws'])
				if self.text_written:
					self.write('')
					self.text_written = False
					
			if "arithmetic_helper_laws" in data:
				self.compile_simple(data['arithmetic_helper_laws'])
				if self.text_written:
					self.write('')
					self.text_written = False
				
			self.compile_visibles(data['visible_laws'])
			self.compile_initially_laws(data['initially_laws'])
			self.compile_goals(data['goals'])
			
			self.compile_kill(data['killEncoding'])
			#if data['killEncoding'][0] == 1 or data['killEncoding'][1] == 1:
			#	self.compile_kill(data['killEncoding'][0], data['killEncoding'][1])
			
		except Exception as e:
			if not self.ignorance:
				raise
			if not self.silent:
				print str(e)
			self.close()
			return None

		self.close()
		
		#try:
		#	parse_objects.errout.print_errors()
		#except:
		#	pass
		
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
		return data
			
	def get_integers_convert_data_old(self,data):
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
		self.compile_simple(laws)
		
	def compile_simple(self,laws):
		for la in laws:
			self.current_meta_info = la.get_meta()
			data = la.print_facts()
			self.write(data)
		self.current_meta_info = None
		
	def compile_non_repitetive(self,laws):
		occured = []
		for la in laws:
			self.current_meta_info = la.get_meta()
			data = la.print_facts()
			if type(data) == list:
				for el in data:
					if not el in occured:
						self.write(el)
						occured.append(el)
			elif not data in occured:
				self.write(data)
				occured.append(data)
		self.current_meta_info = None
			
	def compile_predicates(self,laws):
		self.compile_simple(laws)
	
	def compile_actions(self,laws):
		self.compile_non_repitetive(laws)
	
	def compile_fluents(self,laws):
		self.compile_non_repitetive(laws)
	
	def compile_defined_fluents(self,laws):
		self.compile_simple(laws)
				
	def compile_domains(self):
		for fld in self.flu_domains:
			result = []
			for data in self.flu_domains[fld]:
				text = data.print_facts()
				if type(text) == str: result.append(text)
				else: result.append(" ".join(data.print_facts()))
			if len(result) == 0: continue
			self.write(result)
	
	def compile_static_laws(self,laws):
		self.compile_simple(laws)
	
	def compile_dynamic_laws(self,laws):
		self.compile_simple(laws)
	
	def compile_impossible_laws(self,laws):
		self.compile_simple(laws)
	
	def compile_nonexecutable_laws(self,laws):
		self.compile_simple(laws)
	
	def compile_default_laws(self,laws):
		self.compile_simple(laws)

	def compile_inertial_laws(self,laws):
		self.compile_simple(laws)
	
	def compile_initially_laws(self,laws):
		self.compile_simple(laws)
	
	def compile_goals(self,laws):
		self.compile_simple(laws)
			
	def compile_visibles(self,laws):
		self.compile_simple(laws)
		
	#def compile_kill(self,a,b):
	def compile_kill(self,laws):
		dynamic = False
		static = False
		if len(laws) < 1: return
		for x in laws:
			if x.dynamic: dynamic = True
			else: static = True
			
		my_flu = None
		if len(self.fluents) > 0: 
			for flu in self.fluents:#get one Fluent!
				if flu.get_where() is None:
					my_flu = flu
					break
			if my_flu is None:
				my_flu = self.fluents[0]
		else:
			self.error("Error: No fluents known")
			return
		text = my_flu.print_facts()
		
		if static:
			self.write('impossible(-1,val('+text+',false)). impossible(-1,val('+text+',true)).')
		if dynamic:
			self.write('nonexecutable(-1,val('+text+',false)). nonexecutable(-1,val('+text+',true)).')
			
			
	def print_data(self,data):
		
		#if True:
		#	print "-------------------"
		#	print "Keys:\n\t","\n\t".join(data.keys())
		
		if False:
			print "-------------------"
			if len(data['preds']) > 0: print "ASP Stuff: ","; ".join(str(x) for x in data['preds'])
			if len(data['actions']) > 0: print "Actions: ","; ".join(str(x) for x in data['actions'])
			if len(data['fluents']) > 0: print "Fluents: ","; ".join(str(x) for x in data['fluents'])
			if len(data['integers']) > 0: print "Integers: ","; ".join(str(x) for x in data['integers'])
			if len(data['defined_fluents']) > 0: print "defined_fluents: ","; ".join(str(x) for x in data['defined_fluents'])
			if len(data['static_laws']) > 0: print "static_laws: ","; ".join(str(x) for x in data['static_laws'])
			if len(data['dynamic_laws']) > 0: print "dynamic_laws: ","; ".join(str(x) for x in data['dynamic_laws'])
			if len(data['impossible_laws']) > 0: print "impossible_laws: ","; ".join(str(x) for x in data['impossible_laws'])
			if len(data['default_laws']) > 0: print "default_laws: ","; ".join(str(x) for x in data['default_laws'])
			if len(data['nonexecutable_laws']) > 0: print "nonexecutable_laws: ","; ".join(str(x) for x in data['nonexecutable_laws'])
			if len(data['inertial_laws']) > 0: print "inertial_laws: ","; ".join(str(x) for x in data['inertial_laws'])
			if len(data['initially_laws']) > 0: print "initially_laws: ","; ".join(str(x) for x in data['initially_laws'])
			if len(data['goals']) > 0: print "goals: ","; ".join(str(x) for x in data['goals'])
			if len(data['roles']) > 0: print "roles: ","; ".join(str(x) for x in data['roles'])
			if len(data['arithmetic_laws']) > 0: print "arith_law: ","; ".join(str(x) for x in data['arithmetic_laws'])
			if len(data['arithmetic_helper_laws']) > 0: print "arith_hlp_law: ","; ".join(str(x) for x in data['arithmetic_helper_laws'])
			
		if True:
			
			print "-------------------"
			
			if len(data['preds']) > 0: print "ASP Stuff: ","; ".join(x.typestr() for x in data['preds'])
			if len(data['actions']) > 0: print "Actions: ","; ".join(x.typestr() for x in data['actions'])
			if len(data['fluents']) > 0: print "Fluents: ","; ".join(x.typestr() for x in data['fluents'])
			if len(data['integers']) > 0: print "Integers: ","; ".join(x.typestr() for x in data['integers'])
			if len(data['defined_fluents']) > 0: print "defined_fluents: ","; ".join(x.typestr() for x in data['defined_fluents'])
			if len(data['static_laws']) > 0: print "static_laws: ","; ".join(x.typestr() for x in data['static_laws'])
			if len(data['dynamic_laws']) > 0: print "dynamic_laws: ","; ".join(x.typestr() for x in data['dynamic_laws'])
			if len(data['impossible_laws']) > 0: print "impossible_laws: ","; ".join(x.typestr() for x in data['impossible_laws'])
			if len(data['default_laws']) > 0: print "default_laws: ","; ".join(x.typestr() for x in data['default_laws'])
			if len(data['nonexecutable_laws']) > 0: print "nonexecutable_laws: ","; ".join(x.typestr() for x in data['nonexecutable_laws'])
			if len(data['inertial_laws']) > 0: print "inertial_laws: ","; ".join(x.typestr() for x in data['inertial_laws'])
			if len(data['initially_laws']) > 0: print "initially_laws: ","; ".join(x.typestr() for x in data['initially_laws'])
			if len(data['goals']) > 0: print "goals: ","; ".join(x.typestr() for x in data['goals'])
			if len(data['roles']) > 0: print "roles: ","; ".join(str(x) for x in data['roles']) # x.typestr()
			if len(data['arithmetic_laws']) > 0: print "arith_law: ","; ".join(str(x) for x in data['arithmetic_laws'])
			if len(data['arithmetic_helper_laws']) > 0: print "arith_hlp_law: ","; ".join(str(x) for x in data['arithmetic_helper_laws'])
			
		print "-------------------"
	# Some space for you to make notes.	
	
	