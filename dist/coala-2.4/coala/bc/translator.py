#
# Copyright (c) 2016, Christian Schulz-Hanke
#
import sys

#import aspCompiler
#import lexer
#import parser
import coala.parse.aspCompiler as aspCompiler
import coala.parse.lexer as lexer
import coala.parse.parser as parser
import coala.bc_legacy.translator as tra


class Translator(tra.Translator):

	def __init__(self,compiler='aspCompiler',silent=False,decoupled=False):
		
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
			self.comp = aspCompiler.AspCompiler(decoupled=decoupled)
		else:
			if not self.silent:
				print >> sys.stderr, "Could not find Compiler ",compiler,". Sticking to aspCompiler."
			self.comp = aspCompiler.AspCompiler(decoupled=decoupled)
			
		
		self.default_output_path = "./" #"../temp/"