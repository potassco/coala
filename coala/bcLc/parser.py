#
# Copyright (c) 2016, Christian Schulz-Hanke
#
import ply.yacc as yacc
import lexer
import os
		
# Parsing rules

def nfalse(t):
	try:
		return not '<false>' in t
	except:
		return True

# Pack combines a structure (a) and a list of variables (b) into one structure.
# e.g.: val = a(b(d,c),e(f,g)); var = [a,b,c,d,e,f,g]
def pack(a,b):
	return {'val':a,'var':b}

# Unpack gets the original structure and variable list from a packed structure
def unpack(a):
	if type(a) == dict:
		return a['val'], a['var']
	else:
		return a, []

##class Parser(bcParse):
class Parser(object):

	tokens = lexer.Lexer.tokens
	
	#precedence = (
	#	('left','PLUS','MINUS'),
	#	('left','TIMES','DIVIDE'),
	#	('right','UMINUS'),
	#	)
	
	# dictionary of names
	data = { 'actions' : [] ,
	'fluents' : [] ,
	'defined_fluents' : [],
	'preds' : [] ,
	'static_laws' : [] ,
	'dynamic_laws' : [] ,
	'impossible_laws' : [] ,
	'nonexecutable_laws' : [] ,
	'default_laws' : [] ,
	'inertial_laws' : [] ,
	'initially_laws' : [] ,
	'goals' : [],
	'killEncoding' : [0,0],
	'errors' : [],
	'others' : [],
	'roles' : {},
	'visible_laws' : [] }
	lawid = 1
	
	# will be filled with the lines to parse
	my_lines = []
	meta_info = None
	debug = False
	
	start = 'program'
	
	def p_program(self,t):
		'''program :
					| program rule DOT
					| program ESCAPE_ASP
					| program ROLE_BEGIN role ROLE_END'''
		if len(t) == 3:
			self.data['others'].append(str(t[2])[5:-6])
		elif len(t) == 4:
			if not t[2] is None:
				self.data[t[2][0]].append(t[2][1])
		elif len(t) == 5: 
			name = str(t[2])[5:-1].lstrip()
			index = name.find("(")
			end_ind = name.find(")")
			params = []
			if index > 0 and end_ind > index:
				name_real = name[:index]
				subs = name[index+1:end_ind]
				index = subs.find(",")
				while index >= 0:
					params.append(subs[:index])
					subs = subs[index+1:]
					index = subs.find(",")
				params.append(subs)
				t[3]['params'] = params
				name = name_real
			self.data['roles'][name]=t[3]
	
	def p_role(self,t):
		'''role :
				| role rule DOT
				| role ESCAPE_ASP'''
		if len(t) == 1:
			t[0] = { 'actions' : [] ,
				'fluents' : [] ,
				'defined_fluents' : [],
				'preds' : [] ,
				'int' : [], # Integer facts
				'static_laws' : [] ,
				'dynamic_laws' : [] ,
				'impossible_laws' : [] ,
				'nonexecutable_laws' : [] ,
				'default_laws' : [] ,
				'inertial_laws' : [] ,
				'initially_laws' : [] ,
				'goals' : [],
				'killEncoding' : [0,0],
				'others' : [],
				'visible_laws' : [],
				'params' : [] }
		if len(t) == 3:
			t[0] = t[1]
			t[0]['others'].append(str(t[2])[5:-6])
		elif len(t) == 4:
			t[0] = t[1]
			t[0][t[2][0]].append(t[2][1])
	
	def p_rule(self,t):
		'''rule : fact 
				| law 
				| query '''
		t[0] = t[1]
	
	def p_fact(self,t):
		''' fact : pred_fact
				| act_fact 
				| int_fact
				| flu_fact '''
		t[0] = t[1]		

	def p_law(self,t):
		''' law : static_law 
				| dynamic_law 
				| inertial_law 
				| default_law
				| imposs_law
				| nonexe_law 
				| visible_law'''
		t[0] = t[1]
	
	def p_visible_law(self,t):
		''' visible_law : VISIBLE fluent_formula if_part where_part '''
#				| VISIBLE fluent_formula after_part where_part '''
		if len(t[2]) > 0:
			if nfalse(t[2]):
				if nfalse(t[3]) and nfalse(t[4]):
					t[2], var2 = unpack(t[2])
					t[3], var3 = unpack(t[3])
					t[4], var4 = unpack(t[4])
					t[0] = ('visible_laws',self.add_meta((t[2],t[3],None,None,t[4],var4,var2+var3),t.lineno(1)))
					#if len(t) == 5:
					#	#self.data['visible_laws'].append((t[2],t[3],None,None,t[4],var4,var2+var3))
					#	t[0] = ('visible_laws',self.add_meta((t[2],t[3],None,None,t[4],var4,var2+var3),t.lineno(1)))
					#else:
					#	t[5], var5 = unpack(t[5])
					#	#self.data['visible_laws'].append((t[2],None,t[3],t[4],t[5],var5,var2+var3+var4))
					#	t[0] = ('visible_laws',self.add_meta((t[2],None,t[3],t[4],t[5],var5,var2+var3+var4),t.lineno(1)))
						
	
		
	def p_query(self,t):
		''' query : init_rule 
				| goal_query '''
		t[0] = t[1]
		
	def p_pred_fact(self,t): # <action> a_1,...,a_n <where> bla.
#		''' pred_fact : asp_formula where_part''' 
#		''' pred_fact : PRED formula where_part''' 
		''' pred_fact : formula where_part'''
		t[1], var1 = unpack(t[1])
		t[2], var2 = unpack(t[2])
		#self.data['preds'].append((t[1],t[2],var2,var1))
		t[0] = ('preds',self.add_meta((t[1],t[2],var2,var1),t.lineno(1)))
		
	def p_act_fact(self,t): # <action> a_1,...,a_n <where> bla.
		''' act_fact :  ACT fluent_formula where_part'''
		#if type(t[2]) == list:
			#self.data['actions'] += t[2]
		#else:
			#self.data['actions'].append((t[2],t[3]))
		t[2], var2 = unpack(t[2])
		t[3], var3 = unpack(t[3])
		#self.data['actions'].append((t[2],t[3],var3,var2))
		t[0] = ('actions',self.add_meta((t[2],t[3],var3,var2),t.lineno(1)))
		
	def p_int_fact(self,t): # <action> a_1,...,a_n <where> bla.
		''' int_fact :  INT fluent_formula int_domain where_part'''
		#if type(t[2]) == list:
			#self.data['actions'] += t[2]
		#else:
			#self.data['actions'].append((t[2],t[3]))
		t[2], var2 = unpack(t[2])
		t[3], var3 = unpack(t[3])
		t[4], var4 = unpack(t[4])
		#self.data['actions'].append((t[2],t[3],var3,var2))
		t[0] = ('int',self.add_meta((t[2],t[3],t[4],var4,var2+var3),t.lineno(1)))
		
	def p_flu_fact(self,t): # <fluent> f_1,...,f_n <where> bla.
		''' flu_fact : FLU fluent_formula where_part
					| DFLU fluent_formula where_part '''
		#if type(t[2]) == list:
		#	self.data['fluents'] += t[2]
		#else:
		#	self.data['fluents'].append((t[2]))
		if t[1] != '<fluent>':
			t[2], var2 = unpack(t[2])
			t[3], var3 = unpack(t[3])
			#self.data['defined_fluents'].append((t[2],t[3],var3,var2))
			t[0] = ('defined_fluents',self.add_meta((t[2],t[3],var3,var2),t.lineno(1)))
		else:
			t[2], var2 = unpack(t[2])
			t[3], var3 = unpack(t[3])
			#self.data['fluents'].append((t[2],t[3],var3,var2))
			t[0] = ('fluents',self.add_meta((t[2],t[3],var3,var2),t.lineno(1)))
		
	def p_static_law(self,t): # f_1,...,f_n <if> g_1,...,g_m <where> bla.
#		''' static_law : formula if_part ifcons_part where_part'''
		''' static_law : formula IF formula ifcons_part where_part
						| formula IFCONS formula where_part'''
#		''' static_law : formula IF formula ifcons_part where_part
#						| formula IFCONS formula where_part'''
		if len(t) == 6:
			t[1], var1 = unpack(t[1])
			t[3], var3 = unpack(t[3])
			t[4], var4 = unpack(t[4])
			t[5], var5 = unpack(t[5])
			head = t[1]; ifpart = t[3]; ifcons = t[4]; wherepart = t[5]
			wheriab = var5; variab = var1+var3+var4
		else:
			t[1], var1 = unpack(t[1])
			t[3], var3 = unpack(t[3])
			t[4], var4 = unpack(t[4])
			head = t[1]; ifpart = None; ifcons = t[3]; wherepart = t[4]
			wheriab = var4; variab = var1+var3
		if len(head) > 0:
			if nfalse(head):
				if nfalse(ifpart) and nfalse(ifcons):
					#self.data['static_laws'].append((head,ifpart,ifcons,wherepart,wheriab,variab))
					t[0] = ('static_laws',self.add_meta((head,ifpart,ifcons,wherepart,wheriab,variab),t.lineno(1)))
			else:
				if nfalse(ifpart) and nfalse(ifcons):
					#self.data['impossible_laws'].append((ifpart,ifcons,wherepart,wheriab,variab))
					t[0] = ('impossible_laws',self.add_meta((ifpart,ifcons,wherepart,wheriab,variab),t.lineno(1)))
					#self.data['static_laws'].append((t[1],t[2],t[3],self.variables))

	def p_dynamic_law(self,t): # a <causes> f_1,...,f_n <if> g_1,...,g_m <where> bla.
		''' dynamic_law : formula after_part ifcons_part where_part
					| formula CAUSES formula where_part
					| formula CAUSES formula IF formula where_part'''
#		 ''' dynamic_law : formula after_part ifcons_part where_part
#					 | formula CAUSES formula where_part
#					 | formula CAUSES formula IF formula where_part'''
		if t[2] == '<causes>':
			if len(t) == 5: 
				if len(t[3]) > 0:
					if nfalse(t[3]):
						if nfalse(t[1]):
							t[1], var1 = unpack(t[1])
							t[3], var3 = unpack(t[3])
							t[4], var4 = unpack(t[4])
							#self.data['dynamic_laws'].append((t[3],t[1],None,t[4],var4,var3+var1))
							t[0] = ('dynamic_laws',self.add_meta((t[3],t[1],None,t[4],var4,var3+var1),t.lineno(1)))
				else:
					t[1], var1 = unpack(t[1])
					t[4], var4 = unpack(t[4])
					#self.data['nonexecutable_laws'].append((t[1],None,None,t[4],var4,var1))
					t[0] = ('nonexecutable_laws',self.add_meta((t[1],None,None,t[4],var4,var1),t.lineno(1)))
			else: 
				if len(t[3]) > 0:
					if nfalse(t[3]):
						if nfalse(t[1]) and nfalse(t[5]):
							t[1], var1 = unpack(t[1])
							t[3], var3 = unpack(t[3])
							t[5], var5 = unpack(t[5])
							t[6], var6 = unpack(t[6])
							#self.data['dynamic_laws'].append((t[3],t[1]+t[5],None,t[6],var6,var1+var3+var5))
							t[0] = ('dynamic_laws',self.add_meta((t[3],t[1]+t[5],None,t[6],var6,var1+var3+var5),t.lineno(1)))
				else:
					t[1], var1 = unpack(t[1])
					t[5], var5 = unpack(t[5])
					t[6], var6 = unpack(t[6])
					#self.data['nonexecutable_laws'].append((t[1]+t[5],None,None,t[6],var6,var1+var5))
					t[0] = ('nonexecutable_laws',self.add_meta((t[1]+t[5],None,None,t[6],var6,var1+var5),t.lineno(1)))
		else:
			if len(t[1]) > 0:
				if nfalse(t[1]):
					if nfalse(t[2]) and nfalse(t[3]):
						t[1], var1 = unpack(t[1])
						t[2], var2 = unpack(t[2])
						t[3], var3 = unpack(t[3])
						t[4], var4 = unpack(t[4])
						#self.data['dynamic_laws'].append((t[1],t[2],t[3],t[4],var4,var1+var2+var3))
						t[0] = ('dynamic_laws',self.add_meta((t[1],t[2],t[3],t[4],var4,var1+var2+var3),t.lineno(1)))
				else:
					t[2], var2 = unpack(t[2])
					t[3], var3 = unpack(t[3])
					t[4], var4 = unpack(t[4])
					#self.data['nonexecutable_laws'].append((t[2],None,t[3],t[4],var4,var2+var3))
					t[0] = ('nonexecutable_laws',self.add_meta((t[2],None,t[3],t[4],var4,var2+var3),t.lineno(1)))
					
		
	def p_inertial_law(self,t):
		''' inertial_law : INERTIAL fluent_formula where_part'''
		t[2], var2 = unpack(t[2])
		t[3], var3 = unpack(t[3])
		#self.data['inertial_laws'].append((t[2],t[3],var3,var2))
		t[0] = ('inertial_laws',self.add_meta((t[2],t[3],var3,var2),t.lineno(1)))
		
	def p_default_law(self,t):
		''' default_law : DEFAULT formula where_part
					| DEFAULT formula IF formula where_part
					| DEFAULT formula AFTER formula where_part''' #TODO: default ifcons??
		if len(t[2]) > 0:
			if nfalse(t[2]):
				if len(t) == 4: 
					t[2], var2 = unpack(t[2])
					t[3], var3 = unpack(t[3])
					#self.data['default_laws'].append((t[2],None,None,t[3],var3,var2))
					t[0] = ('default_laws',self.add_meta((t[2],None,None,t[3],var3,var2),t.lineno(1)))
				elif t[3] == '<if>': 
					if nfalse(t[4]):
						t[2], var2 = unpack(t[2])
						t[4], var4 = unpack(t[4])
						t[5], var5 = unpack(t[5])
						#self.data['default_laws'].append((t[2],t[4],None,t[5],var5,var2+var4))
						t[0] = ('default_laws',self.add_meta((t[2],t[4],None,t[5],var5,var2+var4),t.lineno(1)))
				else: 
					if nfalse(t[4]):
						t[2], var2 = unpack(t[2])
						t[4], var4 = unpack(t[4])
						t[5], var5 = unpack(t[5])
						#self.data['default_laws'].append((t[2],None,t[4],t[5],var5,var2+var4))
						t[0] = ('default_laws',self.add_meta((t[2],None,t[4],t[5],var5,var2+var4),t.lineno(1)))
		
	def p_imposs_law(self,t):
		''' imposs_law : IMPOSSIBLE formula ifcons_part where_part'''
		if len(t[2]) > 0:
			if nfalse(t[2]):
				if nfalse(t[3]):
					t[2], var2 = unpack(t[2])
					t[3], var3 = unpack(t[3])
					t[4], var4 = unpack(t[4])
					#self.data['impossible_laws'].append((t[2],t[3],t[4],var4,var2+var3))
					t[0] = ('impossible_laws',self.add_meta((t[2],t[3],t[4],var4,var2+var3),t.lineno(1)))
		else:
			self.data['killEncoding'][0] = 1
		
		
	def p_nonexe_law(self,t): # NONEXECUTABLE <impossible> a_1,..., a_n <if> f_1,..., f_m <where> bla.	=	<caused> <false> <after> a_1,...,a_n,f_1,...,f_m <where> bla.
		''' nonexe_law : NONEXE formula if_part ifcons_part where_part'''
		if len(t[2]) > 0:
			if nfalse(t[2]):
				if nfalse(t[3]) and nfalse(t[4]):
					t[2], var2 = unpack(t[2])
					t[3], var3 = unpack(t[3])
					t[4], var4 = unpack(t[4])
					t[5], var5 = unpack(t[5])
					#self.data['nonexecutable_laws'].append((t[2],t[3],t[4],t[5],var5,var2+var3+var4))
					t[0] = ('nonexecutable_laws',self.add_meta((t[2],t[3],t[4],t[5],var5,var2+var3+var4),t.lineno(1)))
		else:
			self.data['killEncoding'][1] = 1
			
##########################
	
	def p_init_rule(self,t): # <initially> f_1,..., f_n <where> bla.	=	f_1,...,f_n <holds at> 0 <where> bla.
		''' init_rule : INIT formula where_part'''
		if len(t[2]) > 0:
			t[2], var2 = unpack(t[2])
			t[3], var3 = unpack(t[3])
			#self.data['initially_laws'].append((t[2],t[3],var3,var2))
			t[0] = ('initially_laws',self.add_meta((t[2],t[3],var3,var2),t.lineno(1)))
		
	def p_goal_query(self,t): # <goal> f_1,...,f_n <where> bla.
		''' goal_query : GOAL formula where_part'''
		if len(t[2]) > 0:
			t[2], var2 = unpack(t[2])
			t[3], var3 = unpack(t[3])
			#self.data['goals'].append((t[2],t[3],var3,var2))
			t[0] = ('goals',self.add_meta((t[2],t[3],var3,var2),t.lineno(1)))
		
##########################

	def p_if_part(self,t):
		''' if_part : 
					| IF formula '''
		if len(t) == 3:
			if len(t[2]) == 0: t[0] = None 
			else: t[0] = t[2]
		else: t[0] = None

	def p_after_part(self,t):
		''' after_part : AFTER formula '''
		if len(t[2]) == 0: t[0] = None
		else: t[0] = t[2]

	def p_ifcons_part(self,t):
		''' ifcons_part : 
					| IFCONS formula '''
		if len(t) == 3: 
			if len(t[2]) == 0: t[0] = None 
			else: t[0] = t[2]
		else: t[0] = None

	def p_where_part(self,t):
		''' where_part : 
					| WHERE bindings '''
		if len(t) == 3: t[0] = t[2]
		else: t[0] = []
		
	def p_bindings(self,t):
		''' bindings : binding
					| bindings COMMA binding'''
		if len(t) == 2: 
			t[1], var1 = unpack(t[1])
			t[0] = pack([ t[1] ],var1)
		else: 
			t[1], var1 = unpack(t[1])
			t[3], var3 = unpack(t[3])
			t[0] = pack(t[1]+[ t[3] ],var1+var3)
		
	def p_binding(self,t):
		''' binding : ACT fluent
					| FLU fluent equalpart
					| NOT asp_term
					| asp_term 
					| MINUS fluent'''
		#			| MINUS asp_term # Some things should not happen - 1==1
		if len(t) == 2: 
			t[1], var1 = unpack(t[1])
			t[0] = pack(('#pred',t[1]),var1)
		elif t[1] == '<action>':
			t[2], var2 = unpack(t[2])
			t[0] = pack(('#act',t[2]),var2)
		elif t[1] in ('not','-'):
			t[2], var2 = unpack(t[2])
			t[0] = pack(('#pred',('_',t[2])),[])
		else:
			if t[3] == None: 
				t[2], var2 = unpack(t[2])
				t[0] = pack(('#flu',t[2]),var2)
			else:  
				t[2], var2 = unpack(t[2])
				t[3], var3 = unpack(t[3])
				t[0] = pack(('#flu',('fval',t[2],t[3])),var2+var3)
			
##########################

	def p_formula(self,t): # f_1,...,f_n
		''' formula : tfa 
					| formula COMMA tfa '''
		if len(t) == 4: 
			t[1], var1 = unpack(t[1])
			t[3], var3 = unpack(t[3])
			t[0] = pack(t[1]+t[3],var1+var3)
		else: 
			t[0] = t[1]
		
	def p_tfa(self,t):
		''' tfa : atom 
				| TRUE 
				| FALSE '''
		if t[1] == '<true>': 
			t[0] = [] # True does not lead to anything... t[0] = t[1]
		else: 
			t[1], var1 = unpack(t[1])
			t[0] = pack([ t[1] ],var1)
		
	def p_atom(self,t):
		''' atom : fluent equalpart
				| NOT fluent equalpart
				| MINUS fluent equalpart '''
		if len(t) == 3: 
			if t[2] == None: 
				t[0] = t[1]
			else: 
				t[1], var1 = unpack(t[1])
				t[2], var2 = unpack(t[2])
				t[0] = pack(('fval',t[1],t[2]),var1+var2)
		else: 
			if t[3] == None: 
				t[2], var2 = unpack(t[2])
				t[0] = pack(('-',t[2]),var2)
			else: 
				t[2], var2 = unpack(t[2])
				t[3], var3 = unpack(t[3])
				t[0] = pack(('-',('fval',t[2],t[3])),var2+var3)

	def p_fluent_formula(self,t): # f_1,...,f_n
		''' fluent_formula : fluent equalpart
					| fluent_formula COMMA fluent equalpart '''
		if len(t) == 5: 
			t[1], var1 = unpack(t[1])
			t[3], var3 = unpack(t[3])
			t[4], var4 = unpack(t[4])
			if t[4] == None: t[1].append(t[3]); t[0] = pack(t[1],var1+var3)
			else: t[1].append(('fval',t[3],t[4])); t[0] = pack(t[1],var1+var3+var4)
		else: 
			if t[2] == None: 
				t[1], var1 = unpack(t[1])
				t[0] = pack([ t[1] ],var1)
			else: 
				t[1], var1 = unpack(t[1])
				t[2], var2 = unpack(t[2])
				t[0] = pack([ ('fval',t[1],t[2]) ],var1+var2)
		
	def p_equalpart(self,t):
		''' equalpart : 
					| EQ term'''
		if len(t) == 3: t[0] = t[2]
		else: t[0] = None
		
	def p_fluent(self,t):
		''' fluent : IDENTIFIER 
					| var_term
					| IDENTIFIER LBRAC term_list RBRAC '''
		if len(t) == 2: 
			t[0] = t[1]
		else: 
			t[1], var1 = unpack(t[1])
			t[3], var3 = unpack(t[3])
			t[0] = pack((t[1], t[3]),var1+var3) #TODO Add class for predicate?
		
	def p_term_list(self,t):
		''' term_list : term
					| term COMMA term_list '''
		if len(t) == 2: 
			t[1], var1 = unpack(t[1])
			t[0] = pack([ t[1] ],var1)
		else: 
			t[1], var1 = unpack(t[1])
			t[3], var3 = unpack(t[3])
			t[0] = pack([ t[1] ] + t[3],var1+var3)
		
	def p_term(self,t): # X, a, 3, X;Y, 1..Z
		''' term : var_term 
					| IDENTIFIER 
					| NUMBER 
					| MINUS NUMBER 
					| IDENTIFIER LBRAC term_list RBRAC '''
		if len(t) == 2: 
			t[0] = t[1]
		elif len(t) == 3: 
			t[0] = t[1]+t[2]
		else: 
			t[1], var1 = unpack(t[1])
			t[3], var3 = unpack(t[3])
			t[0] = pack((t[1], t[3]),var1+var3)
		
	def p_var_term(self,t):
		''' var_term : VARIABLE '''
		t[0] = pack(t[1],[t[1]])
		
	def p_int_domain(self,t):
		''' int_domain : 
				| COLON term DDOT term '''
		#		| COLON term
		#if len(t) == 3:
		#	t[0] = t[2]
		#el
		if len(t) == 5:
			t[2], var2 = unpack(t[2])
			t[4], var4 = unpack(t[4])
			t[0] = pack((t[2],t[4]),var2+var4)
		else: 
			t[0] = None
		
#################

	def p_asp_term(self,t):
		''' asp_term : asp_operation
					| asp_operation asp_eqoperator asp_operation'''
#					| asp_tfa COLON asp_tfa
		if len(t) == 4:
			t[1], var1 = unpack(t[1])
			t[3], var3 = unpack(t[3])
			t[0] = pack((t[2],t[1],t[3]),var1+var3)
		else:
			t[0] = t[1]

	def p_asp_operation(self,t):
		''' asp_operation : term
						| asp_operation asp_operator term '''
		if len(t) == 2:
			t[0] = t[1]
		else: 
			t[1], var1 = unpack(t[1])
			t[3], var3 = unpack(t[3])
			t[0] = pack((t[2],t[1],t[3]),var1+var3)
				

	def p_asp_eqoperator(self,t):
		''' asp_eqoperator : EQQ
							| EQ
							| NEQ 
							| LT 
							| GT 
							| LE 
							| GE '''
		t[0] = t[1]

	def p_asp_operator(self,t):
		''' asp_operator : PLUS
						| MINUS
						| POWER
						| TIMES
						| DIV '''
		t[0] = t[1]
		
#################

	def p_error(self,t):
		if len(self.my_lines) >= t.lineno:
			if not self.meta_info is None:
				r = None
				f = 0
				for y in self.meta_info:
					if y[0] < t.lineno and y[1]+y[0] >= t.lineno-1:
						r = y[-1]
						f = y[0]
						break
				if not r is None:
					erro = "ERROR: "+str(r)+" Line "+str(t.lineno-f)+": '"+self.my_lines[t.lineno-1]+"'\n\tSyntax error at Token '"+str(t.value)+"'"
				else:
					erro = "ERROR: Line "+str(t.lineno)+": '"+self.my_lines[t.lineno-1]+"'\n\tSyntax error at Token '"+str(t.value)+"'"
			else:
				erro = "ERROR: Line "+str(t.lineno)+": '"+self.my_lines[t.lineno-1]+"'\n\tSyntax error at Token '"+str(t.value)+"'"
		else:
			erro = "ERROR: Line "+str(t.lineno)+": Syntax error at Token '"+str(t.value)+"'"
		#print "% Line "+str(t.lineno)+": Syntax error at Token '"+str(t.value)+"'"
		self.data['errors'].append(erro)
		
	
	def add_meta(self,data,lineno):
		filename = ""
		my_lineno = lineno
		if not self.meta_info is None:
			for x in self.meta_info:
				#y = self.meta_info[x]
				if x[0] < lineno and x[1]+x[0] >= lineno:
					filename = x[2]
					my_lineno = lineno-x[0]
					break
		return (data,{ 'name':'meta', 'line':my_lineno, 'file':filename })
		

	#def build(self,alexer,**kwargs):
	def build(self,**kwargs):
		#print self.tokens
		mypath = os.path.dirname(os.path.realpath(__file__))
		self.reset_data()
		
		if self.debug:
			self.parser = yacc.yacc(module=self, debug=False, outputdir=mypath, **kwargs) # SILENT MODE!
		else:
			self.parser = yacc.yacc(module=self, debug=False, optimize=False, outputdir=mypath, write_tables=False, **kwargs) # SILENT MODE!
		#self.parser = yacc.yacc(module=self, **kwargs)
		
	def reset_data(self):
		self.data = { 'actions' : [] ,
		'fluents' : [] ,
		'defined_fluents' : [],
		'preds' : [] ,
		'int' : [], # Integer facts
		'static_laws' : [] ,
		'dynamic_laws' : [] ,
		'impossible_laws' : [] ,
		'nonexecutable_laws' : [] ,
		'default_laws' : [] ,
		'inertial_laws' : [] ,
		'initially_laws' : [] ,
		'goals' : [],
		'killEncoding' : [0,0],
		'errors' : [],
		'others' : [],
		'roles' : {},
		'visible_laws' : [] }
		self.lawid = 1
		self.my_lines = []
		self.meta_info = None
		
	def submit_text(self,text,meta):
		self.my_lines = text.split("\n")
		self.meta_info = meta 
		
	def debug_output(self):
		
		print "-------------------"
		
		print "ASP Stuff: ",self.data['preds']
		print "Actions: ",self.data['actions']
		print "Fluents: ",self.data['fluents']
		print "Integers: ",self.data['int']
		print "defined_fluents: ",self.data['defined_fluents']
		print "static_laws: ",self.data['static_laws']
		print "dynamic_laws: ",self.data['dynamic_laws']
		print "impossible_laws: ",self.data['impossible_laws']
		print "default_laws: ",self.data['default_laws']
		print "nonexecutable_laws: ",self.data['nonexecutable_laws']
		print "inertial_laws: ",self.data['inertial_laws']
		print "initially_laws: ",self.data['initially_laws']
		print "goals: ",self.data['goals']
		print "roles: ",self.data['roles']
		
		print "-------------------"
