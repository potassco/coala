#
# Copyright (c) 2016, Christian Schulz-Hanke
#
import lexer
import parser
import aspCompiler
import aspReducedCompiler

import time
import sys
import coala.bc.translator as tra

class Translator(tra.Translator):

	def __init__(self,compiler='aspCompiler',silent=False,decoupled=False,agent=False):
		
		self.silent = silent
		self.debug = False
		self.ignore_errors = False
		self.ignore_undefined = False
		self.there_were_roles = False
		self.roles = []
		
		self.lex = lexer.Lexer()
		self.lex.build()
		self.par = parser.Parser()
		self.par.build()
		
		if compiler == 'aspCompiler':
			self.comp = aspCompiler.AspCompiler(decoupled=decoupled,agent=agent)
		elif compiler == 'aspReducedCompiler':
			self.comp = aspReducedCompiler.AspReducedCompiler(decoupled=decoupled,agent=agent)
		else:
			if not self.silent:
				print >> sys.stderr, "Could not find Compiler ",compiler,". Sticking to aspCompiler."
			self.comp = aspCompiler.AspCompiler(decoupled=decoupled,agent=agent)
			
		
		self.default_output_path = "./" #"../temp/"
		
	def post_compile(self):
		self.there_were_roles = self.comp.there_were_roles
		self.roles = self.comp.roles
		