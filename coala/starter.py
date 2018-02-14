#!/usr/bin/env python
#
# Copyright (c) 2016, Christian Schulz-Hanke
#
import getopt
import os
import sys
import traceback

global mypath
mypath = os.path.dirname(os.path.dirname(os.path.realpath(__file__)))+"/"
sys.path.append(mypath)

import coala.parse.parse_objects
import coala.b.translator
import coala.bc.translator
import coala.bcAgent.translator
import coala.bcLc.translator
import coala.bc_legacy.translator
import coala.bcAgent_legacy.translator


global no_clingo_library
no_clingo_library = False

global version
version = "2.456"


try:
	import coala.solverFixed
	import coala.solverIterative
	import coala.stateBuilder
except:
	no_clingo_library = True


def setDefaults():
	global silent
	global input_fi
	global output
	global mode
	global language
	global write_file
	global ignore_errors
	global ignore_undefined
	global debug
	global encoding_s
	global encoding_t
	global encoding_c
	global encoding_i
	global encoding_f
	global max_horizon
	global decoupled
	global only_positive
	global beta
	global tau
	global encoding_non_internal
	global encoding_non_internal_transl
	global negated_actions
	global mypath
	global readmefile
	global exampledirectory
	#global no_clingo_library
	
	#no_clingo_library = False
	silent = False
	input_fi = None
	output = None
	decoupled = True
	
	only_positive = False
	beta = False
	tau = False
	
	ignore_errors = False
	ignore_undefined = False
	write_file = False
	debug = False
	readmefile = mypath+"coala/README_BC.txt"
	exampledirectory = mypath+"examples/"
	encoding_s = mypath+"coala/internal/states.lp"
	encoding_t = mypath+"coala/internal/transitions.lp"
	encoding_c = mypath+"coala/internal/conflicts.lp"
	encoding_i = mypath+"coala/internal/iterative.lp"
	encoding_f = mypath+"coala/internal/fixed.lp"
	encoding_non_internal=mypath+"coala/base.lp"
	encoding_non_internal_transl=mypath+"coala/base_translation.lp"
	mode = "translate"
	language = "bc"
	max_horizon = 10
	negated_actions = False

def usage():
	global silent
	global input_fi
	global output
	global mode
	global language
	global write_file
	global ignore_errors
	global debug
	global encoding_s
	global encoding_t
	global encoding_i
	global encoding_f
	global max_horizon
	global no_clingo_library
	global version
	if silent:
		return
	
	print ""
	print "\tcoala "+version+" - Action Language Translation Tool"
	if no_clingo_library: print "\tWithout clingo library (solving modes will not be available this way)"
	print ""
	print "Usage:"
	print "\tcoala [Arguments] Inputfiles"
	print ""
	print "Arguments:"
	
	print "\t--help, -h\tPrints the usage and some addition help for people to lazy to search"
	if not no_clingo_library:
		print "\t--mode <arg>, -m <arg>\tStates what Coala will do. Default = ",mode
		print "\t\ttranslate, t\tTranslate all Input into ASP Facts"
		print "\t\tsolveIterative, s\tTranslate and try to find a solution"
		print "\t\tsolveFixed, f\tTranslate and try to find a solution with a fixed step length"
		print "\t\tprintStates, ps\tTranslate and display all States"
		print "\t\tprintTransitions, pt\tTranslate and display all Transitions"
		print "\t\tprintStatesAndTransitions, pst\tTranslate and display all States and Transitions"
		print "\t\tconflicts, c\tCheck an encoding for conflicts given a partial state and actions"
	else:
		print "\t--mode translate, -m translate\tInput will be translated into ASP Facts, more options are available if the clingo python library is installed"
		
	
	print "\t--language <arg>, -l <arg>\tDefines the input language. Default = ",language
	print "\t\tbc\tSet input language to BC"
	print "\t\tbc_legacy\tUse an older parser for the input language BC"
	#print "\t\tbc_base\tSet input language to BC but only write static and dynamic laws"
	#print "\t\tb\tSet input language to B"
	###print "\t\tasp\tUse ASP facts as input"
	
	print "Output arguments\tBy default, results are printed to the terminal"
	print "\t--output_file <arg>, -o <arg>\tOutput will be written to the file <arg>"
	print "\t--write_file\tWill write into a temporary file"
	#print "\t--not_decoupled\tStatic and Dynamic laws will not have seperate heads"
	
	print "Translator arguments"
	print "\t--ignore_errors, -i\tTranslation will try to continue even if there are Errors"
	print "\t--ignore_undefined, -u\tTranslation ignore Errors due to undefined fluents or actions"
	print "\t--verbose\tPrint some additional output"
	print "\t--silent, -s\tPrint no output"
	print "\t--arith, -a\tPrint no output"
	#print "\t--tau, -y\tUse tau function; This adds abnormalities to each static law"
	#print "\t--beta, -b\tUse beta function; This adds abnormalities to each dynamic law"
	
	
	if not no_clingo_library:
		print "StateBuilder arguments"
		print "\t--encoding_s <arg>\tSet the encoding for States"
		print "\t--encoding_t <arg>\tSet the encoding for Transitions"
		print "\t--only_positive, -p\tDo not output fluents that hold the value false"
		
		print "Solve arguments"
		print "\t--max_horizon <arg>, -z <arg>\tSet the maximal horizon. 0 equals no horizon; Default = ",max_horizon
		print "\t--encoding_i <arg>\tSet the encoding for solving iteratively; Default = ",encoding_i
		print "\t--encoding_f <arg>\tSet the encoding for solving with fixed horizon; Default = ",encoding_f
		
	print ""
	print "\tCopyright (c) 2016, Christian Schulz-Hanke"
	
def additional_help():
	global readmefile
	global mypath
	print "____________________________________________"
	print ""
	print "Since you were using the -h or --help option: Here is some additional help."
	try:
		fil = open(readmefile)
		nt = fil.read()
		fil.close()
		content = nt.split('\n')
		print ""
		print "Content of the Readme "+readmefile+" for writing BC instances"
		print ""
		print "\t"+"\n\t".join(content)
		print ""
	except:
		print ""
		print "We tried, but could not open the readmefile "+readmefile
		print ""
	print ""
	print "If you are trying to debug, the base path of coala is recognized as:"
	print "\t"+mypath
	print ""
	print "If setup correctly, this script (starter.py) should be located at:"
	print "\t"+mypath+"coala/starter.py"
	print ""
	print "Encodings should be copied to:"
	print "\t"+mypath+"encodings"
	print ""
	print "____________________________________________"
	print ""
	print "Advanced Usage:"
	print ""
	print "1. Just Translate from BC to ASP facts."
	print ""
	print "\tcoala examples/medical.bc examples/medical_instance.bc"
	print ""
	print "This will take the both .bc files and generate ASP facts as output"
	print "If you want to write the output in a file, use a pipe"
	print ""
	print "\tcoala examples/medical.bc examples/medical_instance.bc > output.lp"
	print ""
	print "Or the -o parameter (must be placed in front of the files.)"
	print ""
	print "\tcoala -o output.lp examples/medical.bc examples/medical_instance.bc"
	print ""
	print ""
	print ""
	print "2. Translate and generate States"
	print ""
	print "2.a. Using the gringo library"
	print "\tcoala -m printStates examples/medical.bc examples/medical_instance.bc"
	print ""
	print "2.b. Using clingo and an encoding"
	print "\tcoala examples/medical.bc examples/medical_instance.bc | clingo - encodings/base_translation.lp 0 -c k=0"
	print ""
	print "Note that you must add an encoding in order to get states, the base_translation encoding.lp build on top of the base.lp encoding."
	print "The parameter - of clingo allows it to access the output of coala"
	print "The parameter -c k=0 sets the final step to 0 therefor no transitions are calculated"
	print ""
	print ""
	print ""
	print "3. Translate and generate Transitions"
	print ""
	print "3.a. Using the gringo library"
	print "\tcoala -m printTransitions examples/medical.bc examples/medical_instance.bc"
	print ""
	print "3.b. Using clingo and an encoding"
	print "\tcoala examples/medical.bc examples/medical_instance.bc | clingo - encodings/base_translation.lp 0 -c k=1"
	print ""
	print ""
	print ""
	print "4. Translate and solve given a goal"
	print ""
	print "4.a. Using the gringo library"
	print "\tcoala -m solveIterative examples/medical.bc examples/medical_instance.bc"
	print ""
	print "4.b. Using clingo and an encoding"
	print "\tcoala examples/medical.bc examples/medical_instance.bc | clingo - encodings/base_translation.lp encodings/base_initial.lp encodings/base_goal.lp -c k=2"
	print ""
	print "Note that if you use clingo, you need to explicitly state the horizon -c k=2 which length plans should have."
	print ""
	print "____________________________________________"
	print ""
	print "Please also take a look at the example files available in the downloaded package"
	print ""
	print "New Versions are available at: http://www.cs.uni-potsdam.de/wv/coala/"
	print "If you have questions or feedback, you can also write an email to christian.schulz-hanke( at )cs.uni-potsdam.de"
	print ""

def test_this(trans_obj, statebu_obj, test, test_type, test_transitions=True):
	global output
	global mode
	global language
	global write_file
	global ignore_errors
	global ignore_undefined
	global debug
	global tau
	global beta
	global negated_actions
	global errorcount
	input_fi = test[0]
	statenum = test[1]
	statenum_t = test[2]
	
	try:
		text = trans_obj.translate_file(input_fi, outputfile=output, return_string=True, \
			write_file=write_file,ignore_errors=ignore_errors,debug=debug,beta=beta,tau=tau,\
			negated_actions=negated_actions,ignore_undefined=ignore_undefined)
	except Exception as e:
		print >> sys.stderr, "ERROR: "+test_type+" Testcase "+str(test)+" : Translator error!";
		if debug: print >> sys.stderr, str(e)
		print traceback.format_exc()
		errorcount += 1
		return
	
	if text == None and not silent: 
		print >> sys.stderr, "ERROR: "+test_type+" Testcase "+str(test)+" : Translator error!";
		errorcount += 1
		return
		
	try:
		state_text, states = statebu_obj.get_states(text)
	except Exception as e:
		print >> sys.stderr, "ERROR: "+test_type+" Testcase "+str(test)+" : Solving error!";
		if debug: print >> sys.stderr, str(e)
		print traceback.format_exc()
		errorcount += 1
		return
	
	
	if statenum == len(states):
		if not silent:
			print "OK: "+test_type+" Testcase "+str(test)
		if debug:
			print "States: ",state_text
	else:
		errorcount += 1
		if not silent:
			print "ERROR: "+test_type+" Testcase "+str(test)+" : "+str(len(states))+" instead of "+str(statenum)
			print "States: ",state_text
		else:
			print >> sys.stderr, "ERROR: "+test_type+" Testcase "+str(test)+" : "+str(len(states))+" instead of "+str(statenum)
	
	if test_transitions:
		try:
			state_text_t, states_t = statebu_obj.get_states_transitions(text)
		except:
			print >> sys.stderr, "ERROR: "+test_type+" Testcase "+str(test)+" Transition : Solving error!";
			errorcount += 1
			return
		
		if statenum_t == len(states_t):
			if not silent:
				print "OK: "+test_type+" Testcase "+str(test)+" Transition"
			if debug:
				print "States: ",state_text_t
		else:
			errorcount += 1
			if not silent:
				print "ERROR: "+test_type+" Testcase "+str(test)+" Transition : "+str(len(states_t))+" instead of "+str(statenum_t)
				print "States: ",state_text_t
			else:
				print >> sys.stderr, "ERROR: "+test_type+" Testcase "+str(test)+" Transition : "+str(len(states_t))+" instead of "+str(statenum_t)

def main(argv):
	global silent
	global input_fi
	global output
	global mode
	global language
	global write_file
	global ignore_errors
	global ignore_undefined
	global debug
	global decoupled
	global encoding_s
	global encoding_t
	global encoding_i
	global encoding_f
	global encoding_c
	global max_horizon
	global only_positive
	global beta
	global tau
	global encoding_non_internal
	global encoding_non_internal_transl
	global negated_actions
	global mypath
	setDefaults()
	
	if len(argv) < 1:
		usage()
		sys.exit(0)
	try:                                
		opts, args = getopt.getopt(argv, "hsm:l:o:iuz:dpbynr:c:xa", ["help", "mode=", "language=", \
			"output_file=","outputfile=","debug", "not_decoupled", "not_decouple", \
			"write_file=","ignore_errors","verbose","silent","ignore_undefined" \
			"encoding_s=","encoding_t=","encoding_i=","encoding_f=","max_horizon=", \
			"beta","tau","encoding_non_internal=","eni=","encoding_non_internal_transl=", \
			"enit=","old_arithmetics","arith"])
	except getopt.GetoptError:          
		usage()                         
		sys.exit(2)
		
	changed_encoding_s = False    
	changed_encoding_t = False
	changed_encoding_i = False
	changed_encoding_f = False
	description_resolve = None
	description_detect = None
			
	for opt, arg in opts:
		if opt in ("-h", "--help"):
			usage()           
			additional_help()          
			sys.exit()              
		elif opt in ("-s","--silent"):
			silent = True
		elif opt in ("-d", "--debug"):
			debug = True
		elif opt in ("--not_decoupled", "--not_decouple"):
			decoupled = True
			if not changed_encoding_s: encoding_s = mypath+"encodings/internal/states_not_decoupled.lp"  
			if not changed_encoding_t: encoding_t = mypath+"encodings/internal/transitions_not_decoupled.lp"  
			if not changed_encoding_i: encoding_i = mypath+"encodings/internal/iterative_not_decoupled.lp"   
			if not changed_encoding_f: encoding_f = mypath+"encodings/internal/fixed_not_decoupled.lp"  
		elif opt in ("-m", "--mode"):
			mode = arg.lower()
		elif opt in ("-l", "--language"):
			language = arg.lower()
		elif opt in ("--write_file"):
			write_file = True
			if arg:
				output = arg
		elif opt in ("-o","--output_file","--outputfile"):
			write_file = True
			if arg:
				output = arg
		elif opt in ("-i","--ignore_errors"):
			ignore_errors = True
		elif opt in ("-u","--ignore_undefined"):
			ignore_undefined = True
		elif opt == "--verbose":
			debug = True
		elif opt in ("--encoding_s"):
			changed_encoding_s = True
			encoding_s = arg
		elif opt in ("--encoding_t"):
			changed_encoding_t = True
			encoding_t = arg
		elif opt in ("--encoding"):
			changed_encoding_i = True
			encoding_i = arg
		elif opt in ("--only_positive","-p"):
			only_positive = True
		elif opt in ("-z","--max_horizon"):
			max_horizon = int(arg)
		elif opt in ("-y","--tau"):
			tau = True
		elif opt in ("-b","--beta"):
			beta = True
		elif opt in ("--encoding_non_internal","--eni"):
			encoding_non_internal = arg
		elif opt in ("--encoding_non_internal_transl","--enit"):
			encoding_non_internal_transl = arg
		elif opt in ("-n"): #TODO: negated actions is experimental
			negated_actions = True
			#encoding_s = "encodings/internal/states.lp"
			encoding_t = mypath+"encodings/internal/transitions_neg_act.lp"
			#encoding_c = "encodings/internal/conflicts.lp"
			encoding_i = mypath+"encodings/internal/iterative_neg_act.lp"
			#encoding_f = "encodings/internal/fixed.lp"
			encoding_non_internal=mypath+"encodings/base_neg_act.lp"
			encoding_non_internal_transl=mypath+"encodings/base_translation_neg_act.lp"
		elif opt in ("-r"):
			description_resolve = arg
		elif opt in ("-c"):
			description_detect = arg
		elif opt == "old_arithmetics":
			coala.parse.parse_objects.old_arithmetics = True
		elif opt == "-x":
			coala.parse.parse_objects.additional_ifcons_facts = True
		elif opt in ("-a","--arith"):
			coala.parse.parse_objects.clingcon_arithmetic = True
			
	if len(args) > 0:
		input_fi = args
	elif mode not in ("testcases","test","testencodings"):
		usage()
		exit(2)
	
	testcases = [ (mypath+"coala/testcases/test1.bc",1,0),
				(mypath+"coala/testcases/test2.bc",5,6),
				(mypath+"coala/testcases/test3.bc",8,64),
				(mypath+"coala/testcases/test4.bc",2,0),
				(mypath+"coala/testcases/test5.bc",4,10),
				(mypath+"coala/testcases/test6.bc",2,1),
				(mypath+"coala/testcases/test7.bc",2,1),
				(mypath+"coala/testcases/test8.bc",2,2),
				(mypath+"coala/testcases/test9.bc",2,3),
				(mypath+"coala/testcases/test10.bc",1,7),
				(mypath+"coala/testcases/test_false.bc",4,0),
				(mypath+"coala/testcases/test_true.bc",3,0),
				(mypath+"coala/testcases/test_true_2.bc",4,0),
				(mypath+"coala/testcases/test_true_false.bc",2,0),
				(mypath+"coala/testcases/test_where.bc",12,0),
				(mypath+"coala/testcases/test_where_2.bc",106,212),
				(mypath+"coala/testcases/test_where_3.bc",106,212),
				(mypath+"coala/testcases/test_where_4.bc",133,266),
				(mypath+"coala/testcases/test_where_5.bc",21,0),
				(mypath+"coala/testcases/test_where_6.bc",12,12),
				(mypath+"coala/testcases/test_where_dot.bc",5,4),
				(mypath+"coala/testcases/test_evil.bc",31,47),
				(mypath+"coala/testcases/test_nex.bc",4,0),
				(mypath+"coala/testcases/test_benjamin.bc",1,2),
				(mypath+"coala/testcases/test_benjamin2.bc",0,0),
				(mypath+"coala/testcases/test_benjamin3.bc",1,1),
				(mypath+"coala/testcases/greedy.bc",2,0),
				(mypath+"coala/testcases/flu.bc",4,0),
				(mypath+"coala/testcases/neg.bc",512,0),
				(mypath+"coala/testcases/dom_1.bc",25,0),
				(mypath+"coala/testcases/dom_2.bc",15,27),
				(mypath+"coala/testcases/dom_3.bc",120,0),
				(mypath+"coala/testcases/dom_4.bc",3,0),
				(mypath+"coala/testcases/dom_5.bc",96,0),
				(mypath+"coala/testcases/dom_6.bc",4,8),#4),
				(mypath+"coala/testcases/test_domain_var.bc",5,10),
				(mypath+"coala/testcases/binding_1.bc",25,50),
				(mypath+"coala/testcases/binding_2.bc",25,50), #45),
				(mypath+"coala/testcases/binding_3.bc",25,20),
				(mypath+"coala/testcases/var_bug_1.bc",4,0),
				(mypath+"coala/testcases/var_bug_2.bc",16,0),
				(mypath+"coala/testcases/test_bound.bc",32,1),
				(mypath+"coala/testcases/test_bound_2.bc",27,3)]
	
	if negated_actions:
		testcases.append((mypath+"coala/testcases/test_neg_act.bc",1,4))
	
	testcasesB = [ (mypath+"coala/testcases/test1.b",1,0),
				(mypath+"coala/testcases/test_where.b",12,0),
				(mypath+"coala/testcases/bug.b",30,0),
				(mypath+"coala/testcases/bug2.b",30,0)]
				
	testcases_bc_multi = [(mypath+"coala/testcases/role_1.bc",6,12),
						(mypath+"coala/testcases/role_2.bc",36,144),#18,72), # visible is replicated for each agent
						(mypath+"coala/testcases/role_3.bc",256,64),#128,32),
						(mypath+"coala/testcases/role_4.bc",1024,0),
						(mypath+"coala/testcases/role_5.bc",56,112),
						(mypath+"coala/testcases/role_5b.bc",2688,10752),
						(mypath+"coala/testcases/role_6.bc",16,16)]
	
	testcases_bc_multi_single = [(mypath+"coala/testcases/role_1.bc",6,12),
						(mypath+"coala/testcases/role_2.bc",6,12),
						(mypath+"coala/testcases/role_3.bc",16,8),
						(mypath+"coala/testcases/role_4.bc",2,0),
						(mypath+"coala/testcases/role_5.bc",56,112),
						(mypath+"coala/testcases/role_6.bc",2,2)]
				
	global translator
	translator = None
	
	#LANGUAGE
	if language == "bc":
		translator = coala.bc.translator.Translator(silent=silent,decoupled=decoupled)
	elif language in ("bc_reduced","bc_base"):
		translator = coala.bc.translator.Translator(silent=silent,decoupled=decoupled,compiler="aspReducedCompiler")
	elif language == "b":
		translator = coala.b.translator.Translator(silent=silent,decoupled=decoupled)
	elif language == "bca":
		translator = coala.bcAgent.translator.Translator(silent=silent,decoupled=decoupled,agent=True)
	elif language == "bce":
		translator = coala.bcAgent.translator.Translator(silent=silent,decoupled=decoupled)
	elif language == "bclc":
		translator = coala.bcLc.translator.Translator(silent=silent,decoupled=decoupled)
	elif language == "bc_legacy":
		translator = coala.bc_legacy.translator.Translator(silent=silent,decoupled=decoupled)
	elif language == "bca_legacy":
		translator = coala.bcAgent_legacy.translator.Translator(silent=silent,decoupled=decoupled,agent=True)
	elif language == "bce_legacy":
		translator = coala.bcAgent_legacy.translator.Translator(silent=silent,decoupled=decoupled)
	# ASP Facts???
		
	global result
	result = ""
	
	
			
	global errorcount #for testcases
	errorcount = 0;
	
	try:
	
		if mode in ("translate","t"):
			
			if not silent and debug:
				print >> sys.stderr, "Translate"
			
			result = translator.translate_file(input_fi, outputfile=output, \
				write_file=write_file,ignore_errors=ignore_errors,debug=debug, \
				return_string=not write_file,beta=beta,tau=tau,\
				negated_actions=negated_actions,ignore_undefined=ignore_undefined)
			
		elif mode in ("mas","multiagentsystem"):
			
			if not silent and debug:
				print >> sys.stderr, "Translate"
			
			result = translator.translate_combine(input_fi, description_detect, description_resolve, outputfile=output, \
				write_file=write_file,ignore_errors=ignore_errors,debug=debug, \
				return_string=not write_file,beta=beta,tau=tau,\
				negated_actions=negated_actions,ignore_undefined=ignore_undefined)
			
		elif mode in ("printstates","ps"):
			
			if no_clingo_library:
				print >> sys.stderr, "Feature cannot not be used without clingo library. Exiting."
				sys.exit(1)
			
			if not silent and debug:
				print >> sys.stderr, "States"
			
			statebu = coala.stateBuilder.StateBuilder(silent=silent,encoding_s=encoding_s,encoding_t=encoding_t,only_positive=only_positive,debug=debug)
			#statebu.setTranslator(translator) 
			translator.silent = not debug
			#translator.silent = True
			text = translator.translate_file(input_fi, outputfile=output, return_string=True, \
				write_file=write_file,ignore_errors=ignore_errors,debug=debug,beta=beta,tau=tau,\
				negated_actions=negated_actions,ignore_undefined=ignore_undefined)
			if text == None and not silent: print "Translator error!";return
			if not silent:
				print "__________________"
			state_text, states = statebu.get_states(text)
			result += state_text
			
			
		elif mode in ("printtransitions","pt"):
			
			if no_clingo_library:
				print >> sys.stderr, "Feature cannot not be used without clingo library. Exiting."
				sys.exit(1)
			
			if not silent and debug:
				print >> sys.stderr, "Transitions"
			
			statebu = coala.stateBuilder.StateBuilder(silent=silent,encoding_s=encoding_s,encoding_t=encoding_t,only_positive=only_positive,debug=debug)
			#statebu.setTranslator(translator) 
			translator.silent = not debug
			#translator.silent = True
			text = translator.translate_file(input_fi, outputfile=output, return_string=True, \
				write_file=write_file,ignore_errors=ignore_errors,debug=debug,beta=beta,tau=tau,\
				negated_actions=negated_actions,ignore_undefined=ignore_undefined)
			if text == None and not silent: print "Translator error!";return
			result = "__________________"
			transition_text, states = statebu.get_states_transitions(text)
			result += transition_text
			
			
		elif mode in ("printstatesandtransitions","pst","pts"):
			
			if no_clingo_library:
				print >> sys.stderr, "Feature cannot not be used without clingo library. Exiting."
				sys.exit(1)
			
			if not silent and debug:
				print >> sys.stderr, "States and Transitions"
			
			statebu = coala.stateBuilder.StateBuilder(silent=silent,encoding_s=encoding_s,encoding_t=encoding_t,only_positive=only_positive,debug=debug)
			#statebu.setTranslator(translator) 
			translator.silent = not debug
			#translator.silent = True
			text = translator.translate_file(input_fi,outputfile=output, return_string=True, \
				write_file=write_file,ignore_errors=ignore_errors,debug=debug,beta=beta,tau=tau,\
				negated_actions=negated_actions,ignore_undefined=ignore_undefined)
			if text == None and not silent: print "Translator error!";return
			if not silent:
				print "__________________"
			state_text, states = statebu.get_states(text)
			result += state_text
			result += "_________________\r\n"
			transition_text, states = statebu.get_states_transitions(text)
			result += transition_text
			
			
		elif mode in ("printstatesandtransitionsininitially","psti","ptsi"):
			
			if no_clingo_library:
				print >> sys.stderr, "Feature cannot not be used without clingo library. Exiting."
				sys.exit(1)
			
			if not silent and debug:
				print >> sys.stderr, "Initial State(s) and Transitions"
			
			statebu = coala.stateBuilder.StateBuilder(silent=silent,encoding_s=mypath+"encodings/internal/states_initially.lp",encoding_t=encoding_t,only_positive=only_positive,debug=debug)
			#statebu.setTranslator(translator) 
			translator.silent = not debug
			#translator.silent = True
			text = translator.translate_file(input_fi,outputfile=output, return_string=True, \
				write_file=write_file,ignore_errors=ignore_errors,debug=debug,beta=beta,tau=tau,\
				negated_actions=negated_actions,ignore_undefined=ignore_undefined)
			if text == None and not silent: print "Translator error!";return
			if not silent:
				print "__________________"
			state_text, states = statebu.get_states(text)
			result += state_text
			result += "_________________\r\n"
			transition_text, states = statebu.get_states_transitions(text)
			result += transition_text
			
			
		elif mode in ("solveiterative","s"):
			
			if no_clingo_library:
				print >> sys.stderr, "Feature cannot not be used without clingo library. Exiting."
				sys.exit(1)
			
			if not silent and debug:
				print >> sys.stderr, "Solve Iterative"
			
			solv = coala.solverIterative.SolverIterative(silent=silent,max_horizon=max_horizon,debug=debug,encoding=encoding_i,only_positive=only_positive)
			translator.silent = not debug
			#translator.silent = True
			text = translator.translate_file(input_fi, outputfile=output, return_string=True, \
				write_file=write_file,ignore_errors=ignore_errors,debug=debug,beta=beta,tau=tau,\
				negated_actions=negated_actions,ignore_undefined=ignore_undefined)
			if text == None and not silent: print "Translator error!";return
			actions, holds, state = solv.solve(text)
			
			if not state:
				if not silent:
					print >> sys.stderr, "Could not find a result within "+str(solv.max_horizon)+" time steps"
				result = "Could not find a solution."
			else:
				if not silent:
					print ""
					print "Plan:"
					print ""
					for i in range(len(holds)):
						if i > 0:
							if len(actions) > i-1:
								print "Actions :",actions[i-1]
							else:
								print "Actions : []"
						print "Step ",i,":",holds[i]
			
			
		elif mode in ("solvefixed","f"):
			
			if no_clingo_library:
				print >> sys.stderr, "Feature cannot not be used without clingo library. Exiting."
				sys.exit(1)
			
			if not silent and debug:
				print >> sys.stderr, "Solve Fixed"
			
			solv = coala.solverFixed.SolverFixed(silent=silent,max_horizon=max_horizon,debug=debug,encoding=encoding_f,only_positive=only_positive)
			translator.silent = not debug
			#translator.silent = True
			text = translator.translate_file(input_fi, outputfile=output, return_string=True, \
				write_file=write_file,ignore_errors=ignore_errors,debug=debug,beta=beta,tau=tau,\
				negated_actions=negated_actions,ignore_undefined=ignore_undefined)
			if text == None and not silent: print "Translator error!";return
			actions, holds, state = solv.solve(text)
			
			if not state:
				if not silent:
					print >> sys.stderr, "Could not find a result within "+str(solv.max_horizon)+" time steps"
				result = "Could not find a solution."
			else:
				if not silent:
					print ""
					print "Plan:"
					print ""
					for i in range(len(holds)):
						if i > 0:
							if len(actions) > i-1:
								print "Actions :",actions[i-1]
							else:
								print "Actions : []"
						print "Step ",i,":",holds[i]
						
		elif mode in ("conflicts","c"):
			
			if no_clingo_library:
				print >> sys.stderr, "Feature cannot not be used without clingo library. Exiting."
				sys.exit(1)
			
			if not silent and debug:
				print >> sys.stderr, "Get Conflicts"
			
			statebu = coala.stateBuilder.StateBuilder(silent=silent,encoding_c=encoding_c,encoding_s=encoding_s,encoding_t=encoding_t,only_positive=only_positive,debug=debug)
			translator.silent = not debug
			text = translator.translate_file(input_fi,outputfile=output, return_string=True, \
				write_file=write_file,ignore_errors=ignore_errors,debug=debug,beta=beta,tau=tau, \
				ignore_undefined=ignore_undefined)
			
			if text == None and not silent: print "Translator error!";return
			
			print "Ready!"
			print "Write partial states in one line with a ';' separator: fluent;-otherfluent"
			print "Write actions in one line with a ';' separator: action;otheraction"
			print "(Leave input empty to exit)\r\n"
			state = raw_input("Enter a state:\t")
			while state:
				act = raw_input("Enter an action set:\t")
				print ""
				
				helper = state.split(";")
				state = ""
				for s in helper:
					if len(s) > 0:
						if s[0] == '-':
							state += "holds(val("+s[1:]+",false),0)."
						else:
							state += "holds(val("+s+",true),0)."
				helper = act.split(";")
				act = ""
				for s in helper:
					if len(s) > 0:
						act += "occurs(act("+s+"),0)."
				
				#if debug: 
				#	print "State: "+str(state)
				#	print "Act: "+str(act)
				
				has_states = statebu.has_states(text+state)
				if not has_states: 
					print "This is not a state of the encoding: "+str(state)
				else:
					conflict, states = statebu.has_conflict(text+state+act)
					if conflict: print "=> CONFLICT (there was no state)"
					else: print "=> NO CONFLICT (could find a state)"
				print ""
				state = raw_input("Enter a state:\t")
			print "Closing program."
						
		elif mode in ("testcases","test"):
			
			if no_clingo_library:
				print >> sys.stderr, "Feature cannot not be used without clingo library. Exiting."
				sys.exit(1)
			
			if not silent: 
				print "Testing Coala. (Something is wrong if there are errors, completeness is not guaranteed; Warnings are quite normal)"
				print ""
			
			statebu = coala.stateBuilder.StateBuilder(silent=True,encoding_s=encoding_s,encoding_t=encoding_t,only_positive=True)
			#translator.silent = False
			
			translator = coala.bc.translator.Translator(silent=silent,decoupled=decoupled)
			for test in testcases:
				
				test_this(translator, statebu, test, "BC", True)
				
			
			print >> sys.stderr, "BC REDUCED NOT IMPLEMENTED! Skipping Tests!"
			if False:
				translator = coala.bc.translator.Translator(silent=silent,decoupled=decoupled,compiler="aspReducedCompiler")
				for test in testcases:
					
					test_this(translator, statebu, test, "BC_REDUCED", True)

			print >> sys.stderr, "B NOT IMPLEMENTED! Skipping Tests!"
			if False:
				translator = coala.b.translator.Translator(silent=silent,decoupled=decoupled)
				for test in testcasesB:
					
					test_this(translator, statebu, test, "B", True)
				
			print >> sys.stderr, "ROLES NOT IMPLEMENTED! Skipping Tests!"
			if False:
				translator = coala.bcAgent.translator.Translator(silent=silent,decoupled=decoupled)
				for test in testcases:
					test_this(translator, statebu, test, "BC_AGENT_BASE", True)
				for test in testcases_bc_multi:
					test_this(translator, statebu, test, "BC_AGENT", True)
					
				translator = coala.bcAgent.translator.Translator(silent=silent,decoupled=decoupled,agent=True)
				for test in testcases:
					test_this(translator, statebu, test, "BC_AGENT_SINGLE_BASE", True)
				for test in testcases_bc_multi_single:
					test_this(translator, statebu, test, "BC_AGENT_SINGLE", True)
		
			if not silent:
				print ""
				if errorcount == 0:
					print "Success - No errors."
				else:
					print "There were ",errorcount," Errors."
					
			#---
						
		elif mode == "testencodings":
			
			if no_clingo_library:
				print >> sys.stderr, "Feature cannot not be used without clingo library. Exiting."
				sys.exit(1)
			
			if not silent: 
				print "Testing the encodings base.lp and base_translated in the encodings/ directory."
				print "(Something is wrong if there are errors, completeness is not guaranteed)"
				print ""
			
			errorcount = 0;
			
			statebu = coala.stateBuilder.StateBuilder(silent=True,encoding_s=encoding_s,encoding_t=encoding_t,only_positive=True, \
				encoding_non_internal=encoding_non_internal,encoding_non_internal_transl=encoding_non_internal_transl)
			#translator.silent = False
			
			
			translator = coala.bc.translator.Translator(silent=silent,decoupled=decoupled)
			for test in testcases:
				input_fi = test[0]
				#test[1]
				statenum = test[2]
				
				try:
					text = translator.translate_file(input_fi, outputfile=output, return_string=True, \
						write_file=write_file,ignore_errors=ignore_errors,debug=debug,beta=beta,tau=tau,
						negated_actions=negated_actions,ignore_undefined=ignore_undefined)
				except:
					print >> sys.stderr, "ERROR: BC encodings/base.lp Testcase "+str(test)+" : Translator error!";
					errorcount += 1
					continue
				
				if text == None and not silent: 
					print >> sys.stderr, "ERROR: BC encodings/base.lp Testcase "+str(test)+" : Translator error!";
					errorcount += 1
					continue
					
				try:
					state_text, states = statebu.get_states_use_non_internal(text)
				except:
					print >> sys.stderr, "ERROR: BC encodings/base.lp Testcase "+str(test)+" : Solving error!";
					errorcount += 1
					continue
				
				
				if statenum == len(states):
					if not silent:
						print "OK: BC encodings/base.lp Testcase "+str(test)
					if debug:
						print "States: ",state_text
				else:
					errorcount += 1
					if not silent:
						print "ERROR: BC encodings/base.lp Testcase "+str(test)+" : "+str(len(states))+" instead of "+str(statenum)
						print "States: ",state_text
					else:
						print >> sys.stderr, "ERROR: BC encodings/base.lp Testcase "+str(test)+" : "+str(len(states))+" instead of "+str(statenum)
			
			translator = coala.bc.translator.Translator(silent=silent,decoupled=decoupled,compiler="aspReducedCompiler")
			for test in testcases:
				input_fi = test[0]
				statenum = test[2]
				
				try:
					text = translator.translate_file(input_fi, outputfile=output, return_string=True, \
						write_file=write_file,ignore_errors=ignore_errors,debug=debug,beta=beta,tau=tau,negated_actions=negated_actions)
				except:
					print >> sys.stderr, "ERROR: BC_REDUCED encodings/base.lp Testcase "+str(test)+" : Translator error!";
					errorcount += 1
					continue
				
				if text == None and not silent: 
					print >> sys.stderr, "ERROR: BC_REDUCED encodings/base.lp Testcase "+str(test)+" : Translator error!";
					errorcount += 1
					continue
					
				try:
					state_text, states = statebu.get_states_use_non_internal(text,True)
				except:
					print >> sys.stderr, "ERROR: BC_REDUCED encodings/base.lp Testcase "+str(test)+" : Solving error!";
					errorcount += 1
					continue
				
				
				if statenum == len(states):
					if not silent:
						print "OK: BC_REDUCED encodings/base.lp Testcase "+str(test)
					if debug:
						print "States: ",state_text
				else:
					errorcount += 1
					if not silent:
						print "ERROR: BC_REDUCED encodings/base.lp Testcase "+str(test)+" : "+str(len(states))+" instead of "+str(statenum)
						print "States: ",state_text
					else:
						print >> sys.stderr, "ERROR: BC_REDUCED encodings/base.lp Testcase "+str(test)+" : "+str(len(states))+" instead of "+str(statenum)
			
			if not silent:
				print ""
				if errorcount == 0:
					print "Success - No errors."
				else:
					print "There were ",errorcount," Errors."
		else:
			if not silent:
				print >> sys.stderr, "Error: Unknown mode "+mode
				usage()
				sys.exit(2)
	except Exception as e:
		print >> sys.stderr, "Well, that went wrong : ",str(e)
		if not ignore_errors and debug:
			raise
			
	if debug and not silent:
		print "___________Main Output___________"
	if not silent:
		print result
	

if __name__ == "__main__":
	main(sys.argv[1:])

def start():
	main(sys.argv[1:])
