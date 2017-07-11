# coala - Action Language Translation Tool

Copyright (c) 2016, Christian Schulz-Hanke<br>
christian.schulz-hanke( at )cs.uni-potsdam.de

https://github.com/potassco/coala

Coala is a translator from BC to an ASP fact format.
In combination with clingo or the clingo python library,
it can be used to generate states and transitions
or calculate plans given an initial state and a goal.

This project can be used from directories or
packed and be installed using python distutils.

Credit goes to Sergio Tessaris for his valuable feedback on installation and compatibility.

### Using without installing

Coala can be used without installation.<br>
It can be run calling

	python coala/coala examples/medical.bc

### Installing using pip

Coala can be installed using pip without downloading (examples will not be available)

    pip install https://github.com/potassco/coala/archive/master.zip

Note that installing coala as a command line tool may require

    sudo pip install https://github.com/potassco/coala/archive/master.zip

### Installing using python distutils

After downloading and unpacking coala,
an installation can be done calling

    sudo python setup.py install


### Example and Usage:

For the Input language, there is an "coala-Version/examples" folder with 3 small examples.<br>
(additionally, there are more files in the "coala-Version/testcases" directory)<br>
A translation from BC to ASP facts can be done using:

	coala examples/medical.bc

Generating plans can be done using:

    coala --mode solveIterative examples/medical.bc examples/medical_instance.bc

or short:

    coala -m s examples/medical*

Note that coala does not include solving options if it cannot find the clingo python library.<br>
If you want to use clingo instead, you will have to run a translated instance together with an encoding instead.<br>
Using clingo may look as follows

    coala examples/medical* | clingo - encodings/incremental_clingo.lp | outputformatclingocoala

PLEASE refer to page/index.html for further details, examples and more.


```
Usage:
	coala [Arguments] Inputfiles
	
Arguments:
	--mode <arg>, -m <arg>	States what Coala will do. Default =  translate
		translate, t	Translate all Input into ASP Facts
		solveIterative, s	Translate and try to find a solution
		solveFixed, f	Translate and try to find a solution with a fixed step length
		printStates, ps	Translate and display all States
		printTransitions, pt	Translate and display all Transitions
		printStatesAndTransitions, pst	Translate and display all States and Transitions
		conflicts, c	Check an encoding for conflicts given a partial state and actions
	--language <arg>, -l <arg>	Defines the input language. Default =  bc
		bc	Set input language to BC
		bc_base	Set input language to BC but only write static and dynamic laws
		b	Set input language to B
Output arguments	By default, results are printed to the terminal
	--output_file <arg>, -o <arg>	Output will be written to the file <arg>
	--write_file	Will write into a temporary file
	--not_decoupled	Static and Dynamic laws will not have seperate heads
Translator arguments
	--ignore_errors, -i	Translation will try to continue even if there are Errors
	--ignore_undefined, -i	Translation ignore Errors due to undefined fluents or actions
	--verbose	Print some additional output
	--silent, -s	Print no output
	--tau, -y	Use tau function; This adds abnormalities to each static law
	--beta, -b	Use beta function; This adds abnormalities to each dynamic law
StateBuilder arguments
	--encoding_s <arg>	Set the encoding for States
	--encoding_t <arg>	Set the encoding for Transitions
	--only_positive, -p	Do not output fluents that hold the value false
Solve arguments
	--max_horizon <arg>, -z <arg>	Set the maximal horizon. 0 equals no horizon; Default =  10
	--encoding_i <arg>	Set the encoding for solving iteratively
	--encoding_f <arg>	Set the encoding for solving with fixed horizon
```
