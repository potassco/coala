#
# Copyright (c) 2016, Christian Schulz-Hanke
#
import clingo
import os


class SolverIterative(object):

	def __init__(self,encoding = None,debug=False,silent=False,max_horizon=0,only_positive=False):
		mypath = os.path.dirname(os.path.dirname(os.path.realpath(__file__)))+"/"
		if encoding == None:
			encoding = mypath+"encodings/internal/iterative.lp"
		else:
			self.encoding = encoding
		self.silent = silent
		self.debug = debug
		self.holds = []
		self.solution = []
		self.transitions = []
		self.optimize = False
		self.max_horizon = max_horizon
		self.horizon = 0
		self.control = None
		self.print_negative = not only_positive
		
	def clean(self,atoms):#,stid=0):
		self.holds = []
		result = []
		for a in atoms:
			if a.name == 'holds':
				st = a.arguments
				while st[-1].number >= len(self.holds):
					self.holds.append([])
				if st[0].name == 'val':
					content = st[0].arguments
					if content[1].type is clingo.SymbolType.Function:
						if content[1].name == 'false':
							if self.print_negative:
								self.holds[st[-1].number].append('-'+str(content[0]))
						elif content[1].name == 'true':
							self.holds[st[-1].number].append(str(content[0]))
						else:
							self.holds[st[-1].number].append(str(content[0])+"="+str(content[1]))
					else:
						self.holds[st[-1].number].append(str(content[0])+"="+str(content[1]))
				elif st[0].name == 'neg_val':
					content = st[0].arguments
					print type(content[1])
					print dir(content[1])
					if content[1].type is clingo.SymbolType.Function:
						if content[1].name == 'false':
							self.holds[st[-1].number].append(str(content[0]))
						elif content[1].name == 'true':
							if self.print_negative:
								self.holds[st[-1].number].append('-'+str(content[0]))
						else:
							self.holds[st[-1].number].append("-"+str(content[0])+"="+str(content[1]))
					else:
						self.holds[st[-1].number].append("-"+str(content[0])+"="+str(content[1]))
				#self.holds[st[-1]].append(str(st[0]))
			elif a.name == 'occurs':
				st = a.arguments
				if len(st) > 0 and st[0].name == 'act': 
					actt = st[0].arguments
				while st[-1].number >= len(result):
					result.append([])
				result[st[-1].number].append(str(actt[0]))
		return result	
	
	def setStep(self,index):
		if self.debug:
			print "Setting horizon to ",index
		
		oldqu = self.horizon
		
		if self.optimize:
			self.control.assign_external(clingo.Function("utility",[oldqu]),False)
			if not index in self.transitions:
				if self.debug:
					print "Grounding transition and utility ",index
				self.control.ground([("transition",[index]),("utility",[index])])
				self.transitions.append(index)
			self.control.assign_external(clingo.Function("utility",[index]),True)
		else:
			self.control.assign_external(clingo.Function("query",[oldqu]),False)
			if not index in self.transitions:
				if self.debug:
					print "Grounding transition and query ",index
				self.control.ground([("transition",[index]),("query",[index])])
				self.transitions.append(index)
			self.control.assign_external(clingo.Function("query",[index]),True)
			
		self.horizon = index
		
	def onmodel(self,model):
		atoms = model.symbols(atoms=True) #atoms(clingo.Model.ATOMS)
		self.solution = atoms
	
	def solve(self,inputText):
		self.solution = []
		self.control = clingo.Control(['-W','no-atom-undefined'])
		self.control.configuration.solve.models = 0
		self.control.load(self.encoding)
		self.control.add("base", [], inputText)
		if self.optimize:
			self.control.ground([("base",[]),("initialbase",[]),("utility",[0])])
		else:
			self.control.ground([("base",[]),("initialbase",[]),("query",[0])])
		
		state = self.control.solve(on_model=self.onmodel,assumptions=[])
		if state.unsatisfiable:
			if self.debug:
				print "Base is ",state
			return [], [], False
		elif self.debug:
			self.clean(self.solution)
			print "Base is ",state," : ",self.holds
		
		if self.optimize:
			self.control.assign_external(clingo.Function("utility",[0]),True)
		else:
			self.control.assign_external(clingo.Function("query",[0]),True)
		self.transitions = [0]
		self.horizon = 0
		
		state = self.control.solve(on_model=self.onmodel,assumptions=[])
		if self.debug:
			print "Solving result: ",state
		while (state.unsatisfiable or (self.optimize and self.horizon < 5)):
			self.setStep(self.horizon+1)
			if self.debug: print "solving"
			state = self.control.solve(on_model=self.onmodel,assumptions=[])
			if self.max_horizon>0 and self.max_horizon <= self.horizon:
				break
			if self.debug:
				print "Solving result: ",state
		
		result = self.clean(self.solution)
		if self.debug:
			print "Holds: ",self.holds
	
		return result, self.holds, state.satisfiable
