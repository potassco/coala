#
# Copyright (c) 2016, Christian Schulz-Hanke
#
import lexer
import parser
import aspCompiler
import aspReducedCompiler

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
		elif compiler == 'aspReducedCompiler':
			self.comp = aspReducedCompiler.AspReducedCompiler(decoupled=decoupled)
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
					
					linecount = len(nt.split('\n'))-1
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
		self.par.parser.parse(input=text, lexer=self.lex.lexer, tracking=True)
		
		if self.debug:
			self.par.debug_output()
		
		if outputfile == None:
			outputfile = self.default_output_path+"output_"+str(time.time())+"_facts.lp"
			
		data = self.par.data
		
		if beta:
			data = self.beta(data)
		if tau:
			data = self.tau(data)
		
		self.comp.submit_text(text, meta_info)
		outp = self.comp.compile(data,outputfile)
		self.post_compile()
		
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

	def translate_combine(self,inputfile,input_detection=None,input_resolve=None,outputfile=None,write_file=True,ignore_errors=False, \
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
		self.par.parser.parse(input=text, lexer=self.lex.lexer)
		data = self.par.data
		if self.debug:
			self.par.debug_output()
		
		if input_detection:
			text_detect, meta_info_det = self.read_files(input_detection)
			if text_detect == None:
				return
			self.par.reset_data()
			self.par.parser.parse(input=text_detect, lexer=self.lex.lexer)
			data_detect = self.par.data
			if self.debug:
				self.par.debug_output()
		else:
			data_detect = {}
			
		if input_resolve:
			text_resolve, meta_info_res = self.read_files(input_resolve)
			if text_resolve == None:
				return
			self.par.reset_data()
			self.par.parser.parse(input=text_resolve, lexer=self.lex.lexer)
			data_resolve = self.par.data
			if self.debug:
				self.par.debug_output()
		else:
			data_resolve = {}
		
		if outputfile == None:
			outputfile = self.default_output_path+"output_"+str(time.time())+"_facts.lp"
			
		data = self.beta(self.tau(data))
		data_detect = self.beta(data_detect)
		#if self.debug:
		#	print data
		#	print data_detect
		#data_resolve
		
		#combine
		combined = {}
		for key in data:
			a = data[key]
			b = []
			c = []
			try: b = data_detect[key] 
			except: pass
			try: c = data_resolve[key]
			except: pass
			combined[key] = a+b+c
		
		outp = self.comp.compile(combined,outputfile)
		self.post_compile()
		
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
	
	def post_compile(self):
		# This function is overwritten by the bcAgent.Translator.
		pass

	def beta(self,data):
		new_fluents = []
		new_defaults = []
		new_flu_short = []
		laws = []
		if "dynamic_laws" in data:
			for law in data["dynamic_laws"]:
				flu = ('-',('_ab',law[0]))
				if type(law[2]) == list:
					law[2].append(flu)
				else: law = law[:2] + ([flu],) + law[3:] #Python is stupid, ([flu]) would be a list, therefore ','
				if not law[0] in new_flu_short:
					new_fluents.append(([('_ab',law[0])],law[-3],law[-2],law[-1]))
					new_flu_short.append(law[0])
					new_defaults.append(([('-',('_ab',law[0]))],None,None,law[-3],law[-2],law[-1]))
				laws.append(law)
			data["dynamic_laws"] = laws
		laws = []
		if "nonexecutable_laws" in data:
			for law in data["nonexecutable_laws"]:
				flu = ('-',('_ab',law[0]))
				if type(law[2]) == list:
					law[2].append(flu)
				else: law = law[:2] + ([flu],) + law[3:] #Python is stupid, ([flu]) would be a list, therefore ','
				if not law[0] in new_flu_short:
					new_fluents.append(([('_ab',law[0])],law[-3],law[-2],law[-1]))
					new_flu_short.append(law[0])
					new_defaults.append(([('-',('_ab',law[0]))],None,None,law[-3],law[-2],law[-1]))
				laws.append(law)
			data["nonexecutable_laws"] = laws
		#if "inertial_laws" in data:
		#	for law in data["inertial_laws"]:
		#		flu = ('-',('ab',law[0]))
		#		if type(law[2]) == list:
		#			law[2].append(flu)
		#		else: law = law[:2] + ([flu],) + law[3:] #Python is stupid, ([flu]) would be a list, therefore ','
		#		if not law[0] in new_flu_short:
		#			new_fluents.append(([('ab',law[0])],law[-3],law[-2],law[-1]))
		#			new_flu_short.append(law[0])
		#			new_defaults.append(([('-',('ab',law[0]))],law[-3],law[-2],law[-1]))
		#While some default laws are actually dynamic_laws, we can ignore that, since they are al
		#if "default_laws" in data: #***
		#	for law in data["default_laws"]:
		#		pass
		if len(new_fluents) > 0:
			data["fluents"] += new_fluents
			data["default_laws"] += new_defaults
		
		return data
	
	def tau(self,data):
		new_fluents = []
		new_defaults = []
		new_flu_short = []
		laws = []
		if "static_laws" in data:
			for law in data["static_laws"]:
				flu = ('-',('_ab',law[0]))
				if type(law[2]) == list:
					law[2].append(flu)
				else: law = law[:2] + ([flu],) + law[3:] #Python is stupid, ([flu]) would be a list, therefore ','
				if not law[0] in new_flu_short:
					new_fluents.append(([('_ab',law[0])],law[-3],law[-2],law[-1]))
					new_flu_short.append(law[0])
					new_defaults.append(([('-',('_ab',law[0]))],None,None,law[-3],law[-2],law[-1]))
				laws.append(law)
			data["static_laws"] = laws
		laws = []
		if "impossible_laws" in data:
			for law in data["impossible_laws"]:
				flu = ('-',('_ab',law[0]))
				if type(law[1]) == list:
					law[1].append(flu)
				else: law = law[:1] + ([flu],) + law[2:] #Python is stupid, ([flu]) would be a list, therefore ','
				if not law[0] in new_flu_short:
					new_fluents.append(([('_ab',law[0])],law[-3],law[-2],law[-1]))
					new_flu_short.append(law[0])
					new_defaults.append(([('-',('_ab',law[0]))],None,None,law[-3],law[-2],law[-1]))
				laws.append(law)
			data["impossible_laws"] = laws
		#if "inertial_laws" in data:
		#	for law in data["inertial_laws"]:
		#		flu = ('-',('ab',law[0]))
		#		if type(law[2]) == list:
		#			law[2].append(flu)
		#		else: law = law[:2] + ([flu],) + law[3:] #Python is stupid, ([flu]) would be a list, therefore ','
		#		if not law[0] in new_flu_short:
		#			new_fluents.append(([('ab',law[0])],law[-3],law[-2],law[-1]))
		#			new_flu_short.append(law[0])
		#			new_defaults.append(([('-',('ab',law[0]))],law[-3],law[-2],law[-1]))
		#While some default laws are actually dynamic_laws, we can ignore that, since they are al
		#if "default_laws" in data: #***
		#	for law in data["default_laws"]:
		#		pass
		if len(new_fluents) > 0:
			data["defined_fluents"] += new_fluents
			data["default_laws"] += new_defaults
		return data
	
	