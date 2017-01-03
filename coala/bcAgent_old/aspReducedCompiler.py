#
# Copyright (c) 2016, Christian Schulz-Hanke
#
import aspCompiler
import copy

class AspReducedCompiler(aspCompiler.AspCompiler):
	
	# OVERWRITE SOME RULES!
	
	def copy_rename(self,stuff):
		stuff2 = self.rename_depth(copy.deepcopy(stuff))
		return stuff2
	
	def rename_depth(self,stuff):
		if type(stuff) == list:
			for i in range(len(stuff)):
				stuff[i] = self.rename_depth(stuff[i])
			return stuff
		elif type(stuff) == tuple:
			arr = []
			for i in range(len(stuff)):
				arr.append(self.rename_depth(stuff[i]))
			return tuple(arr)
		elif type(stuff) == str:
			if stuff[0].istitle():
				return "_"+stuff
			else:
				return stuff
		else:
			print stuff
			return str
			
	
	def compile_impossible_laws(self,laws):
		if len(self.fluents) == 0:
			self.error("Error, there are no fluents!")
			return
		#fluent = self.copy_rename(self.fluents[0])
		#fluent_value = self.to_string(fluent[0][0],tf=True)
		for ac in laws:
			self.current_meta_info = ac[1]
			ac = ac[0]
			data = self.extract_all(ac) #,2)
			myidstr = self.make_id(data[-1])
			if len(data) == 5:
				wherepart = self.return_compiled_where(data[-3],data[-2],data[-1])
				#wherepart = self.return_compiled_where(data[-3]+fluent[-3],data[-2]+fluent[-2],data[-1]+fluent[-1])
				if self.decoupled: self.write('static_law(law('+myidstr+'))'+wherepart+'.')
				#self.write(self.static_law+'(law('+myidstr+'),val('+fluent_value+',true))'+wherepart+'.')
				#self.write(self.static_law+'(law('+myidstr+'),val('+fluent_value+',false))'+wherepart+'.')
				self.write(self.static_law+'(law('+myidstr+'),_false)'+wherepart+'.')
				for p in data[0]: self.write('if(law('+myidstr+'),'+p+')'+wherepart+'.')
				for p in data[1]: self.write('ifcons(law('+myidstr+'),'+p+')'+wherepart+'.')
			else:
				self.error("Error with size of impossible law "+str(ac))
		self.current_meta_info = None
	
	def compile_nonexecutable_laws(self,laws):
		if len(self.fluents) == 0:
			self.error("Error, there are no fluents!")
			return
		#fluent = self.copy_rename(self.fluents[0])
		#fluent_value = self.to_string(fluent[0][0],tf=True)
		for ac in laws:
			self.current_meta_info = ac[1]
			ac = ac[0]
			data = self.extract_all(ac,0) #,3,0)
			myidstr = self.make_id(data[-1])
			if len(data) == 6:
				wherepart = self.return_compiled_where(data[-3],data[-2],data[-1])
				#wherepart = self.return_compiled_where(data[-3]+fluent[-3],data[-2]+fluent[-2],data[-1]+fluent[-1])
				if self.decoupled: self.write('dynamic_law(law('+myidstr+'))'+wherepart+'.')
				#self.write(self.dynamic_law+'(law('+myidstr+'),val('+fluent_value+',true))'+wherepart+'.')
				#self.write(self.dynamic_law+'(law('+myidstr+'),val('+fluent_value+',false))'+wherepart+'.')
				self.write(self.dynamic_law+'(law('+myidstr+'),_false)'+wherepart+'.')
				for p in data[0]: self.write('after(law('+myidstr+'),'+p+')'+wherepart+'.')
				for p in data[1]: self.write('after(law('+myidstr+'),'+p+')'+wherepart+'.')
				for p in data[2]: self.write(self.difcons+'(law('+myidstr+'),'+p+')'+wherepart+'.') 
			else:
				self.error("Error with size of nonexecutable law "+str(ac))
		self.current_meta_info = None
				
	def compile_default_laws(self,laws):
		for ac in laws:
			self.current_meta_info = ac[1]
			ac = ac[0]
			data = self.extract_all(ac,2) #,3,2)
			myidstr = self.make_id(data[-1])
			wherepart = self.return_compiled_where(data[-3],data[-2],data[-1])
			if len(data) == 4:
					for p in data[0]: 
						myidstr = self.make_id(data[-1])
						if self.decoupled: self.write('static_law(law('+myidstr+'))'+wherepart+'.')
						self.write(self.static_law+'(law('+myidstr+'),'+p+')'+wherepart+'.')
						self.write('ifcons(law('+myidstr+'),'+p+')'+wherepart+'.')
			elif len(data) == 6:
				if len(data[1]) == 0 and len(data[2]) == 0:
					for p in data[0]: 
						myidstr = self.make_id(data[-1])
						if self.decoupled: self.write('static_law(law('+myidstr+'))'+wherepart+'.')
						self.write(self.static_law+'(law('+myidstr+'),'+p+')'+wherepart+'.')
						self.write('ifcons(law('+myidstr+'),'+p+')'+wherepart+'.')
						#self.write('default('+p+')'+wherepart+'.')
				else:
					if len(data[2]) == 0:
						for p in data[0]: 
							if self.decoupled: self.write('static_law(law('+myidstr+'))'+wherepart+'.')
							self.write(self.static_law+'(law('+myidstr+'),'+p+')'+wherepart+'.')
							self.write('ifcons(law('+myidstr+'),'+p+')'+wherepart+'.')
						for p in data[1]: self.write('if(law('+myidstr+'),'+p+')'+wherepart+'.')
					elif len(data[1]) == 0:
						for p in data[0]: 
							if self.decoupled: self.write('dynamic_law(law('+myidstr+'))'+wherepart+'.')
							self.write(self.dynamic_law+'(law('+myidstr+'),'+p+')'+wherepart+'.')
							self.write(self.difcons+'(law('+myidstr+'),'+p+')'+wherepart+'.')
						for p in data[2]: self.write('after(law('+myidstr+'),'+p+')'+wherepart+'.')
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
			if len(ac) == 4:
				self.current_vars = ac[-1]
				head = self.to_string_array(ac[0],True)
				if len(head) > 0:
					for p in head: 
						wherepart = self.return_compiled_where(ac[-3],ac[-2],ac[-1],optionals=["domain("+p+",_DOMAIN_ELEMENT)"])
						variables = ac[-1]
						myidstr = self.make_id(variables+["_DOMAIN_ELEMENT"])
						if self.decoupled: self.write('dynamic_law(law('+myidstr+'))'+wherepart+'.')
						self.write(self.dynamic_law+'(law('+myidstr+'),val('+p+',_DOMAIN_ELEMENT))'+wherepart+'.')
						self.write('after(law('+myidstr+'),val('+p+',_DOMAIN_ELEMENT))'+wherepart+'.')
						self.write(self.difcons+'(law('+myidstr+'),val('+p+',_DOMAIN_ELEMENT))'+wherepart+'.')
			else:
				self.error("Error with inertial "+str(ac))
		self.current_meta_info = None

		
