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
:- { holds(val(X,A),0):domain(X,A) } != 1, fluent(X).

% Defaults
{holds(H,0)} :- default(H).
{holds(H,0)} :- default(I,H), 
    holds(F,0) : if(I,F), atom(F); 
    #false : if(I,F), not atom(F);
    #false : after(I,A).

:- impossible(I,_), 
    holds(F,0) : impossible(I,F);
    #false : impossible(I,F), not atom(F); 
    not not holds(F,0) : ifcons(I,F);
    #false : ifcons(I,F), not atom(F).

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
:- { holds(val(X,A),t):domain(X,A) } != 1, fluent(X). 

% Simplification for impossible and nonexecutable laws
:- holds(_false,t).

% Inertials
{holds(val(F,V),t)} :- inertial(F), holds(val(F,V),t-1).

% Defaults
{holds(H,t)} :- default(H).
{holds(H,t)} :- default(I,H), 
    holds(F,t) : if(I,F), atom(F); 
    #false : if(I,F), not atom(F);
    occurs(A,t-1) : after(I,A), action(A); 
    holds(F,t-1) : after(I,F), atom(F);
    #false : after(I,F), not atom(F), not action(F).

% Impossible laws
:- impossible(I,_), 
    holds(F,t) : impossible(I,F);
    #false : impossible(I,F), not atom(F); 
    not not holds(F,t) : ifcons(I,F);
    #false : ifcons(I,F), not atom(F).

% Nonexecutable laws
:- nonexecutable(I,_), 
    occurs(A,t-1) : nonexecutable(I,A), action(A);
    holds(F,t-1) : nonexecutable(I,F), atom(F); 
    #false : nonexecutable(I,F), not atom(F), not action(F);
    not not holds(F,t) : ifcons(I,F); 
    #false : ifcons(I,F), not atom(F).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%% Query: Check finallys
#program check(t).

%%%#external query(t).% Done by the internal encoding

% Goals for planning
:- not holds(val(G,GV),t), finally(val(G,GV)), query(t).


