#
# Copyright (c) 2016, Christian Schulz-Hanke
#
import ply.lex as lex

class Lexer(object):
	
	tokens = ( 
		#'ESCAPE_BRACELETS',
		'ESCAPE_ASP',
		'NOT',
		'IDENTIFIER',
		###'NEG_IDENTI',
		'NUMBER',
		'VARIABLE',
		'ACT',
		'FLU',
		'DFLU',
		'CAUSES',
		'IF',
		'IFCONS',
		'AFTER',
		'DEFAULT',
		'INERTIAL',
		'NONEXE',
		'IMPOSSIBLE',
		'INIT',
#		'SFLU',
#		'CAUS',
#		'EXE',
#		'PRED',
#		'OC_AT',
#		'HO_AT',
		'GOAL',
		'WHERE',
		'TRUE',
		'FALSE',
		'COMMA',
		'MINUS','DOT','LBRAC','RBRAC',
#		'MOD',
#		'SEMIC','COLON','DDOT',,
		'NEQ','EQQ','GT','LT','LE','GE','PLUS','POWER','TIMES','DIV',
		'EQ',
#		'AND','OR','XOR','LTLNOT','LTLOR','IMPL','EQUIV',
#		'LTL','X','G','F','U','R',
	) # Tokens 
	
	reserved = {'not':'NOT'}
		
	#t_ESCAPE_BRACELETS = r'{[^}]*}'
	t_ESCAPE_ASP = r'<asp>(.*?\n)*?.*?</asp>'
	t_ignore_COMMENT = r'%[^\n]*' #r'%[^\n]*'
			
	t_NOT = r'not'
	
	def t_IDENTIFIER(self,t): 
		r'[a-z][a-zA-Z0-9_]*'
		if t.value in self.reserved.keys():
			t.type = self.reserved[t.value]
		return t
		
	###t_NEG_IDENTI = r'\-[a-z][a-zA-Z0-9_]*'
	t_VARIABLE = r'(_|[A-Z][a-zA-Z0-9_]*)'
	t_ACT = r'<action>'
	t_FLU = r'<fluent>'
#		t_SFLU = r'<static(\ )?fluent>'
	t_DFLU = r'<defined(\ )?fluent>'
	t_CAUSES = r'<causes>'
	t_IF = r'<if>'
	t_IFCONS = r'<ifcons>'
	t_AFTER = r'<after>'
	t_DEFAULT = r'<default>'
	t_INERTIAL = r'<inertial>'
	t_NONEXE = r'<nonexecutable>'
	t_IMPOSSIBLE = r'<impossible>'
	t_INIT = r'<initially>'
	t_GOAL = r'<finally>'
	t_WHERE = r'<where>'
	t_TRUE = r'<true>'
	t_FALSE = r'<false>'
#		t_PRED = r'<pred>'
#		t_CAUS = r'<caused>'
#		t_EXE = r'<executable>'
#		t_OC_AT = r' <occurs\ at>'
#		t_HO_AT = r'<holds\ at>'
		
	t_COMMA = r','
	
#		t_MOD = r'mod'
#		t_SEMIC = r';'
#		t_COLON = r':'
#		t_DDOT = r'\.\.'

	t_DOT = r'\.'
	t_LBRAC = r'\('
	t_RBRAC = r'\)'
	
	t_MINUS = r'-'
	
	#t_NUMBER = r'[0-9]+'
	t_EQQ = r'=='
	t_EQ = r'=' 
	t_NEQ = r'!='
	t_LT = r'<'
	t_GT = r'>'
	t_LE = r'<='
	t_GE = r'>='
	t_PLUS = r'\+'
	t_POWER = r'\*\*'
	t_TIMES = r'\*'
	t_DIV = r'/'
	
#		t_AND = r'&'
#		t_OR = r'\?'
#		t_XOR = r'\^'
#		t_LTLNOT = r'!'
#		t_LTLOR = r'\|'
#		t_IMPL = r'->'
#		t_EQUIV = r'<->'
	
#		t_LTL = r'LTL:'
#		t_X = r'<ltl>X'
#		t_G = r'<ltl>G'
#		t_F = r'<ltl>F'
#		t_U = r'<ltl>U'
#		t_R = r'<ltl>R'

	
#		 def t_NUMBER(self,t): 
#				 r'\d+' 
#				 try: 
#						 t.value = int(t.value) 
#				 except ValueError: 
#						 print("Integer value too large %d", t.value) 
#						 t.value = 0 
#				 return t 
	#t_NUMBER = r'-?\d+' # We dont care about the actual value!
	t_NUMBER = r'\d+'
	
#		def t_COMMENT(self,t):
#				r'%[^\n]*'
#				pass
	
	# Ignored characters 
	t_ignore = " \t" 
			
	def t_newline(self,t): 
		r'\n+' 
		t.lexer.lineno += t.value.count("\n") 
			
	def t_error(self,t): 
		try:
			print("% Illegal character '%s'" % t.value[0]) 
		except:
			pass
		t.lexer.skip(1) # Build the lexer 
			
	def build(self,**kwargs):
		self.lexer = lex.lex(module=self, **kwargs)
			
	def test(self,data):
		self.lexer.input(data)
		while True:
			tok = self.lexer.token()
			if not tok: 
				break
			print(tok)
	
#lexer = lex.lex()