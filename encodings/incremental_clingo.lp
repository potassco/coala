%%%

#include <incmode>. 
% <incmode> uses a clingo internal way of solving a problem incrementally.
% There are three parameters for incmode that clingo can be called with
%    imin   = get(prg.get_const("imin"), clingo.Number(0))
%       the minimal number of steps to add before the iteration stops
%    imax   = prg.get_const("imax")
%       the maximal number of steps to add before the iteration stops
%    istop  = get(prg.get_const("istop"), clingo.String("SAT"))
%       the stopping criteria, SAT, UNSAT or UNKNOWN; The program will successfully stop if the
%       given criteria is reached between imin and imax steps.
%
% Example:
%   coala examples/monkey/monkey.bc examples/monkey/monkey_instance.bc | clingo - encodings/incremental_clingo.lp -c imin=10 -c imax=15 | outputformatclingobc2aso


%%% Base
fluent(X) :- defined_fluent(X).
atom(val(F,B)) :- domain(F,B).

% Initial choice
{ holds(val(F,B),0) : domain(F,B) } = 1 :- fluent(F), not defined_fluent(F).

% Static laws
holds(H,0) :- static_law(I), head(I,H), 
        holds(F,0) : if(I,F), atom(F); 
        #false : if(I,F), not atom(F);
        not not holds(F,0) : ifcons(I,F).

% Fluent domain restriction
:- { holds(val(X,_),0) } != 1, fluent(X).


% Inertials
dynamic_law(id(inertial,F,V)) :- inertial(F), domain(F,V).
head(id(inertial,F,V),val(F,V)) :- inertial(F), domain(F,V).
after(id(inertial,F,V),val(F,V)) :- inertial(F), domain(F,V).
ifcons(id(inertial,F,V),val(F,V)) :- inertial(F), domain(F,V).

% Defaults
static_law(id(default,F)) :- default(F).
head(id(default,F),F) :- default(F).
ifcons(id(default,F),F) :- default(F).

static_law(id(default,law(L))) :- default(L,_).
head(id(default,law(L)),F) :- default(L,F).
ifcons(id(default,law(L)),F) :- default(L,F).

% Impossible laws
static_law(id(impossible,I)) :- impossible(I,_). 
head(id(impossible,I),_false) :- impossible(I,_). 
if(id(impossible,I),F) :- impossible(I,F). 


% Nonexecutable laws
dynamic_law(id(nonexecutable,I)) :- nonexecutable(I,_).
head(id(nonexecutable,I),_false) :- nonexecutable(I,_).
after(id(nonexecutable,I),F) :- nonexecutable(I,F).

%%% Set initial state
holds(F,0) :- initially(F).

:- holds(_false,0).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%% Transitions
#program step(t).

% Action choice
{ occurs(A,t-1) : action(A) }.

% Static laws
holds(H,t) :- static_law(I), head(I,H), 
        holds(F,t) : if(I,F), atom(F); 
        #false : if(I,F), not atom(F);
        not not holds(F,t) : ifcons(I,F).

% Dynamic laws
holds(H,t) :- dynamic_law(I), head(I,H), 
        holds(F,t-1) : after(I,F), atom(F); 
        occurs(A,t-1) : after(I,A), action(A); 
        #false : after(I,F), not atom(F), not action(F);
        not not holds(F,t) : ifcons(I,F).

% Fluent domain restriction
:- { holds(val(X,_),t) } != 1, fluent(X). 

% Simplification for impossible and nonexecutable laws
:- holds(_false,t).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%% Query: Check finallys
#program check(t).

%%%#external query(t).% Done by the internal encoding

% Goals for planning
:- not holds(val(G,GV),t), finally(val(G,GV)), query(t).


