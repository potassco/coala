#
# Copyright (c) 2016, Christian Schulz-Hanke
#
import lexer
import parser
import aspCompiler

import time
import sys

class Translator(object):

	def __init__(self,compiler='aspCompiler',silent=False,decoupled=False):
		
		self.silent = silent
		self.debug = False
		self.ignore_errors = False
		self.ignore_undefined = False
		
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
		
	def read_files(self,inputfile):
		meta = []
		pos = 0
		if type(inputfile) == list:
			text =  ""
			for fi in inputfile:
				try:
					fil = open(fi)
					nt = fil.read() #.replace('\n','')
					
					linecount = len(nt.split('\n'))
					meta.append((pos,linecount,fi))
					pos += linecount
					
					text += nt
					fil.close()
				except:
					if not self.silent:
						print >> sys.stderr, "Could not find File ",fi
					if not self.ignore_errors:
						raise
		else:
			fil = open(inputfile)
			if not fil:
				return None, None
			text = fil.read() #.replace('\n','')
			linecount = len(text.split('\n'))
			meta = [(0,linecount,inputfile)]
			fil.close()
		return text, meta
		
		
	def translate_file(self,inputfile,outputfile=None,write_file=True,ignore_errors=False, \
		debug=False,return_string=False,beta=False,tau=False,negated_actions=False,ignore_undefined=False):
		
		self.comp.ignorance = ignore_errors
		self.comp.tofile = write_file
		self.comp.silent = self.silent
		self.comp.debug = debug
		self.comp.return_string = return_string
		self.comp.negated_actions = negated_actions
		self.comp.ignore_undefined = ignore_undefined
		self.ignore_errors = ignore_errors
		self.ignore_undefined = ignore_undefined
		self.debug = debug
		
		text, meta_info = self.read_files(inputfile)
		if text == None:
			return
		
		self.par.reset_data()
		self.par.submit_text(text, meta_info)
		self.par.parser.parse(input=text, lexer=self.lex.lexer)
		
		if self.debug:
			self.par.debug_output()
		
		if outputfile == None:
			outputfile = self.default_output_path+"output_"+str(time.time())+"_facts.lp"
		
		self.comp.submit_text(text, meta_info)
		outp = self.comp.compile(self.par.data,outputfile)
		
		if (not self.silent or self.debug) and len(self.comp.errors) > 0:
			for errr in self.comp.errors:
				print >> sys.stderr, "Error : ", errr
		
		if return_string:
			return outp
		
		if write_file:
			if not self.silent:
				if outp == None:
					print >> sys.stderr, "There was an Error while translating!"
					return None
				if outputfile != None and outp != outputfile:
					print >> sys.stderr, "Warning, wrong File written"
				
			return outp
		return None
