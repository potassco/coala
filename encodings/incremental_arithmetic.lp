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

% Theory
#include "csp.lp".


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

%% Math

% Simplification
arithmetic_law(L) :- arithmetic(L,_).
% arithmetic_laws are atoms, therefore they can hold at time steps.
atom(_arithmetic(L)) :- arithmetic_law(L).

% Domains of integers
&dom {L..U : integer_domain(V,L,U)} = val(V,0) :- integer_domain(V,_,_). % only for ints with domain!

% Include integers in answer sets.
&show {val(I,0) : integer(I)}.

%Divisions!
arithmetic_division(V,L,F*R,X) :- arithmetic_helper_division(V,L,F,R,X).

assigned(V,0) :- integer(V).

arithmetic(L,V,K,I,M):- arithmetic(L,_unknown,V,K,I,M), integer(V).
arithmetic(L,K,V,I,M):- arithmetic(L,_unknown,V,K,I,M), not integer(V), integer(K).
arithmetic(L,V,K*U,I,M):- arithmetic(L,_unknown,V,U,K,I,M), integer(V), not integer(U).
arithmetic(L,U,K*V,I,M):- arithmetic(L,_unknown,V,U,K,I,M), not integer(V), integer(U).
arithmetic(L,_sum,V,K,I,M):- arithmetic(L,_unknown,V,K,I,M), not integer(V), not integer(K).

:- initially(val(V,X)), integer(V), not &sum{val(V,0)} = X.

allassigned(L,0) :- arithmetic_law(L,_).
allassigned_head(L,0) :- arithmetic_law(L,_).
arithmetic_fulfilled(L,0) :- &sum {K*val(X,0),I:arithmetic(L,X,K,I,0);K*val(X,0),I:arithmetic_head(L,X,K,I);K*X,I:arithmetic(L,_sum,X,K,I,_)} = C, not arithmetic_assignment_dynamic(L), arithmetic_law(L,eq), arithmetic(L,C).
arithmetic_fulfilled(L,0) :- &sum {K*val(X,0),I:arithmetic(L,X,K,I,0);K*val(X,0),I:arithmetic_head(L,X,K,I);K*X,I:arithmetic(L,_sum,X,K,I,_)} < C, not arithmetic_assignment_dynamic(L), arithmetic_law(L,lt), arithmetic(L,C).
arithmetic_fulfilled(L,0) :- &sum {K*val(X,0),I:arithmetic(L,X,K,I,0);K*val(X,0),I:arithmetic_head(L,X,K,I);K*X,I:arithmetic(L,_sum,X,K,I,_)} <= C, not arithmetic_assignment_dynamic(L), arithmetic_law(L,le), arithmetic(L,C).
arithmetic_fulfilled(L,0) :- &sum {K*val(X,0),I:arithmetic(L,X,K,I,0);K*val(X,0),I:arithmetic_head(L,X,K,I);K*X,I:arithmetic(L,_sum,X,K,I,_)} > C, not arithmetic_assignment_dynamic(L), arithmetic_law(L,gt), arithmetic(L,C).
arithmetic_fulfilled(L,0) :- &sum {K*val(X,0),I:arithmetic(L,X,K,I,0);K*val(X,0),I:arithmetic_head(L,X,K,I);K*X,I:arithmetic(L,_sum,X,K,I,_)} >= C, not arithmetic_assignment_dynamic(L), arithmetic_law(L,ge), arithmetic(L,C).
arithmetic_fulfilled(L,0) :- &sum {K*val(X,0),I:arithmetic(L,X,K,I,0);K*val(X,0),I:arithmetic_head(L,X,K,I);K*X,I:arithmetic(L,_sum,X,K,I,_)} != C, not arithmetic_assignment_dynamic(L), arithmetic_law(L,ne), arithmetic(L,C).

% Handle arithmetics!
% Assignments
% ^-- static
:- holds(_arithmetic(L),0), arithmetic_assignment(L), not arithmetic_fulfilled(L,0).

% Non-Assignments which appear in bodys:
holds(_arithmetic(L),0) :- not arithmetic_assignment(L), not arithmetic_assignment_dynamic(L), arithmetic_fulfilled(L,0).


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

%% Math

% Domains of integers
&dom {L..U : integer_domain(V,L,U)} = val(V,t) :- integer_domain(V,_,_). % only for ints with domain!

% Include integers in answer sets.
&show {val(I,t) : integer(I)}.

% All integers must be assigned at any step.
:- not assigned(V,t), integer(V).

% Handle inertial laws. (won't be handled in the base_translation.lp part as there is no domain/2 for integers)
assigned(V,t) :- integer(V), inertial(V), &sum{val(V,t)} = val(V,t-1).

% An integer is assigned if there is a dynamic law assigning it.
assigned(V,t) :- integer(V), arithmetic_head(L,V,_,_), 
    holds(_arithmetic(L),t), 
    allassigned(L,t-1), % This is required for dynamic laws to prevent loops
    arithmetic_assignment_dynamic(L).

%Division, Truncate
:- arithmetic_division(V,L,R,X), not &sum {R*val(X,t); -L*val(V,t)} <= 0.
:- arithmetic_division(V,L,R,X), not &sum {R*val(X,t); -L*val(V,t)} > -R.
%Ceil
%:- arithmetic_helper_division(V,L,R,X), not &sum {R*val(X,t); -L*val(V,t)} < R.
%:- arithmetic_helper_division(V,L,R,X), not &sum {R*val(X,t); -L*val(V,t)} >= 0.
%Round
%:- arithmetic_helper_division(V,L,R,X), not &sum {2*R*val(X,t); -2*L*val(V,t)} < R.
%:- arithmetic_helper_division(V,L,R,X), not &sum {2*R*val(X,t); -2*L*val(V,t)} >= -R.

% Workaround concerning a bug; Arithmetic laws are only used if all integers in it are assigned!
allassigned(L,t) :- assigned(V,t) : arithmetic(L,V,_,_,_), integer(V); arithmetic_law(L,_).
allassigned_head(L,t) :- assigned(V,t) : arithmetic_head(L,V,_,_), integer(V); arithmetic_law(L,_).


arithmetic_fulfilled(L,t) :- &sum {K*val(X,t-M),I:arithmetic(L,X,K,I,M);K*val(X,t),I:arithmetic_head(L,X,K,I);K*X,I:arithmetic(L,_sum,X,K,I,_)} = C, arithmetic_assignment_dynamic(L), arithmetic_law(L,eq), arithmetic(L,C).
arithmetic_fulfilled(L,t) :- &sum {K*val(X,t-M),I:arithmetic(L,X,K,I,M);K*val(X,t),I:arithmetic_head(L,X,K,I);K*X,I:arithmetic(L,_sum,X,K,I,_)} < C, arithmetic_assignment_dynamic(L), arithmetic_law(L,lt), arithmetic(L,C).
arithmetic_fulfilled(L,t) :- &sum {K*val(X,t-M),I:arithmetic(L,X,K,I,M);K*val(X,t),I:arithmetic_head(L,X,K,I);K*X,I:arithmetic(L,_sum,X,K,I,_)} <= C, arithmetic_assignment_dynamic(L), arithmetic_law(L,le), arithmetic(L,C).
arithmetic_fulfilled(L,t) :- &sum {K*val(X,t-M),I:arithmetic(L,X,K,I,M);K*val(X,t),I:arithmetic_head(L,X,K,I);K*X,I:arithmetic(L,_sum,X,K,I,_)} > C, arithmetic_assignment_dynamic(L), arithmetic_law(L,gt), arithmetic(L,C).
arithmetic_fulfilled(L,t) :- &sum {K*val(X,t-M),I:arithmetic(L,X,K,I,M);K*val(X,t),I:arithmetic_head(L,X,K,I);K*X,I:arithmetic(L,_sum,X,K,I,_)} >= C, arithmetic_assignment_dynamic(L), arithmetic_law(L,ge), arithmetic(L,C).
arithmetic_fulfilled(L,t) :- &sum {K*val(X,t-M),I:arithmetic(L,X,K,I,M);K*val(X,t),I:arithmetic_head(L,X,K,I);K*X,I:arithmetic(L,_sum,X,K,I,_)} != C, arithmetic_assignment_dynamic(L), arithmetic_law(L,ne), arithmetic(L,C).

% Handle arithmetics!
% Assignments
% ^-- dynamic
:- holds(_arithmetic(L),t), allassigned(L,t-1), arithmetic_assignment_dynamic(L), t>0, not arithmetic_fulfilled(L,t).

% ^-- static
:- holds(_arithmetic(L),t), allassigned(L,t), arithmetic_assignment(L), not arithmetic_fulfilled(L,t).

% Non-Assignments which appear in bodys:
holds(_arithmetic(L),t) :- allassigned(L,t), allassigned_head(L,t), not arithmetic_assignment(L), not arithmetic_assignment_dynamic(L), arithmetic_fulfilled(L,t).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%% Query: Check finallys
#program check(t).

%%%#external query(t).% Done by the internal encoding

% Goals for planning
:- not holds(val(G,GV),t), finally(val(G,GV)), query(t).
:- not holds(_arithmetic(L),t), finally(_arithmetic(L)), query(t).
%:- t == 0, query(t).

