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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Math

% Domains of integers
&dom {L..U : integer_domain(V,L,U)} = val(V,0) :- integer_domain(V,_,_).

% Include integers in answer sets.
&show {val(I,0) : integer(I)}.

%---------------------------------------------------------

% arithmetic_laws are atoms, therefore they can hold at time steps.
atom(_arithmetic(L)) :- arithmetic_law(L,_).

% Enforces arithmetics to hold when laws do.
:- holds(_arithmetic(L),0), allassigned(L,0), not arithmetic_fulfilled(L,0), not arithmetic_illegal(L,0).
%:- holds(_arithmetic(L),T), not arithmetic_fulfilled(L,T).

% Non-Assignments which appear in bodys:
holds(_arithmetic(L),0) :- allassigned(L,0), not ifcons(_,_arithmetic(L)),
    allassigned_head(L,0), arithmetic_fulfilled(L,0), 
    not arithmetic_assignment(L),
    not arithmetic_assignment_dynamic(L).

% Handling ifcons parts
holds(_arithmetic(L),0) :- arithmetic_fulfilled(L,0), ifcons(_,_arithmetic(L)).

%---------------------------------------------------------
% Handle equations

arithmetic_fulfilled(L,0) :- arithmetic_law(L,eq),
    &sum {K*val(X,0),I:arith_law_atom(K,X,I,L,0);K*X,I:arith_law_atom(K,X,I,L)} = C, 
    arithmetic(L,C).
%arithmetic_fulfilled(L,0) :- arithmetic_law(L,eq),
%    &sum {K*val(X,0+M),I:arith_law_atom(K,X,I,L,M);K*X,I:arith_law_atom(K,X,I,L)} = C, 
%    arithmetic(L,C).


arithmetic_fulfilled(L,0) :- arithmetic_law(L,ne),
    &sum {K*val(X,0),I:arith_law_atom(K,X,I,L,0);K*X,I:arith_law_atom(K,X,I,L)} != C,
    arithmetic(L,C).
%arithmetic_fulfilled(L,0) :- arithmetic_law(L,ne),
%    &sum {K*val(X,0+M),I:arith_law_atom(K,X,I,L,M);K*X,I:arith_law_atom(K,X,I,L)} != C,
%    arithmetic(L,C).

arithmetic_fulfilled(L,0) :- arith_law_simp(L,C,F),
    &sum {F*K*val(X,0),I:arith_law_atom(K,X,I,L,0);F*K*X,I:arith_law_atom(K,X,I,L)} < C.
%arithmetic_fulfilled(L,0) :- arith_law_simp(L,C,F),
%    &sum {F*K*val(X,0+M),I:arith_law_atom(K,X,I,L,M);F*K*X,I:arith_law_atom(K,X,I,L)} < C.

%---------------------------------------------------------
% An assignment is legal if the value of the head would be inside it's domain

arithmetic_illegal(L,0) :- arithmetic_head(L,V,_,_), arithmetic_assignment(L), arithmetic(L,C), integer_domain(V,LD,UD), &sum {K*val(X,0),I:arith_law_atom(K,X,I,L,0),not arithmetic_head(L,X,K,I);K*X,I:arith_law_atom(K,X,I,L)} < C-UD.

arithmetic_illegal(L,0) :- arithmetic_head(L,V,_,_), arithmetic_assignment(L), arithmetic(L,C), integer_domain(V,LD,UD), &sum {K*val(X,0),I:arith_law_atom(K,X,I,L,0),not arithmetic_head(L,X,K,I);K*X,I:arith_law_atom(K,X,I,L)} > C-LD.

arithmetic_illegal(L,0) :- arithmetic_head(L,V,_,_), arithmetic_assignment_dynamic(L), arithmetic(L,C), integer_domain(V,LD,UD), &sum {K*val(X,0),I:arith_law_atom(K,X,I,L,0),not arithmetic_head(L,X,K,I);K*X,I:arith_law_atom(K,X,I,L)} < C-UD.

arithmetic_illegal(L,0) :- arithmetic_head(L,V,_,_), arithmetic_assignment_dynamic(L), arithmetic(L,C), integer_domain(V,LD,UD), &sum {K*val(X,0),I:arith_law_atom(K,X,I,L,0),not arithmetic_head(L,X,K,I);K*X,I:arith_law_atom(K,X,I,L)} > C-LD.
%---------------------------------------------------------
% SMT to HTC encoding
% (Integers must be assigned at each step.)

% Initial values are assumed to be assigned for the initial step
assigned(V,0) :- integer(V).

% An integer is assigned if there is a static law assigning it.
assigned(V,0) :- integer(V), arithmetic_head(L,V,_,_), 
    holds(_arithmetic(L),0), 
    allassigned(L,0),
    arithmetic_assignment(L).

% All integers must be assigned at any step.
:- not assigned(V,0), integer(V).

%---------------------------------------------------------
% Simplifications

% Collect assigned atoms
allassigned(L,0) :- arithmetic_law(L,_),
    assigned(V,0) : arithmetic(L,V,_,_,_), integer(V).

allassigned_head(L,0) :- arithmetic_law(L,_),
    assigned(V,0) : arithmetic_head(L,V,_,_), integer(V).

allassigned(L,0) :- arithmetic_law(L,_), ifcons(_,_arithmetic(L)), 
    not not assigned(V,0) : arithmetic(L,V,_,_,_), integer(V).

allassigned_head(L,0) :- arithmetic_law(L,_), ifcons(_,_arithmetic(L)), 
    not not assigned(V,0) : allassigned_head(L,V,_,_), integer(V).

% Handle Atoms that are unknown during the translation process
arithmetic(L,V,K,I,M):-       arithmetic(L,_unknown,V,K,I,M),   integer(V).
arithmetic(L,K,V,I,M):-       arithmetic(L,_unknown,V,K,I,M),   not integer(V), integer(K).
arithmetic(L,_sum,V,K,I,M):-  arithmetic(L,_unknown,V,K,I,M),   not integer(V), not integer(K).

arithmetic(L,V,K*U,I,M):-     arithmetic(L,_unknown,V,U,K,I,M), integer(V),     not integer(U).
arithmetic(L,U,K*V,I,M):-     arithmetic(L,_unknown,V,U,K,I,M), not integer(V), integer(U).

% Collect atoms for the sum construct
%arith_law_atom(K,X,I,L,-1) :- arithmetic(L,X,K,I), 
%    arithmetic_assignment_dynamic(L), 
%    arithmetic(L,C).
%
%arith_law_atom(K,X,I,L,0) :- arithmetic(L,X,K,I), 
%    not arithmetic_assignment_dynamic(L), 
%    arithmetic(L,C).
arith_law_atom(K,X,I,L,M) :- arithmetic(L,X,K,I,M).

arith_law_atom(K,X,I,L,0) :- arithmetic_head(L,X,K,I), 
    arithmetic(L,C).

arith_law_atom(K,X,I,L) :- arithmetic(L,_sum,X,K,I,_), 
    arithmetic(L,C).

% Convert laws to "lower than"
arith_law_simp(L,C,1) :-     arithmetic_law(L,lt), arithmetic(L,C). 
arith_law_simp(L,C+1,1) :-   arithmetic_law(L,le), arithmetic(L,C).
arith_law_simp(L,-C,-1) :-   arithmetic_law(L,gt), arithmetic(L,C).
arith_law_simp(L,-C+1,-1) :- arithmetic_law(L,ge), arithmetic(L,C).

%---------------------------------------------------------
% Divisions
arithmetic_division(V,L,F*R,X) :- arithmetic_helper_division(V,L,F,R,X).

%Trunc  
:- arithmetic_division(V,L,R,X), not &sum {R*val(X,0); -L*val(V,0)} <= 0.
:- arithmetic_division(V,L,R,X), not &sum {R*val(X,0); -L*val(V,0)} > -R.

%---------------------------------------------------------
% Helpers for additive statements
% Displays values of helpers for additive statements
%&show {val(X,0) : arithmetic_additive_law(L), arithmetic_head(L,X,_,_)}.

% Notes if the helper is set to the result of the additive statement
arithmetic_fulfilled(L,0) :- arithmetic_additive_law(L),
    &sum {K*val(X,0+M),I:arith_law_atom(K,X,I,L,M),step(0+M);K*X,I:arith_law_atom(K,X,I,L)} = C, 
    arithmetic(L,C).

% Requires the additive helper to be 0 otherwise
:- not holds(_arithmetic(L),0), arithmetic_additive_law(L),
    arithmetic_head(L,C,K,_),
    not &sum {val(C,0)} = 0.

% There is no allassigned for additive laws.
:- arithmetic_additive_law(L), holds(_arithmetic(L),0), not arithmetic_fulfilled(L,0).

%---------------------------------------------------------
% What do additive statements mean?
% The following two laws modify each (!) assignment of to-be-increased fluent by adding the additive helpers! 
arith_law_atom(-1,additive_helper(L,X),additive_helper(L,X),L2,0) :-
    arithmetic_additive_fluent(L,X),
    arithmetic_assignment(L2), arithmetic_head(L2,X,_,_).

arith_law_atom(-1,additive_helper(L,X),additive_helper(L,X),L2,0) :-
    arithmetic_additive_fluent(L,X),
    arithmetic_assignment_dynamic(L2), arithmetic_head(L2,X,_,_).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Math

% Domains of integers
&dom {L..U : integer_domain(V,L,U)} = val(V,t) :- integer_domain(V,_,_).

% Include integers in answer sets.
&show {val(I,t) : integer(I)}.

%---------------------------------------------------------

% Enforces arithmetics to hold when laws do.
:- holds(_arithmetic(L),t), allassigned(L,t), not arithmetic_fulfilled(L,t), not arithmetic_illegal(L,t).
%:- holds(_arithmetic(L),t), not arithmetic_fulfilled(L,t).

% Non-Assignments which appear in bodys:
holds(_arithmetic(L),t) :- allassigned(L,t), not ifcons(_,_arithmetic(L)),
    allassigned_head(L,t), arithmetic_fulfilled(L,t), 
    not arithmetic_assignment(L),
    not arithmetic_assignment_dynamic(L).

% Handling ifcons parts
holds(_arithmetic(L),t) :- arithmetic_fulfilled(L,t), ifcons(_,_arithmetic(L)).

%---------------------------------------------------------
% Handle equations

arithmetic_fulfilled(L,t) :- arithmetic_law(L,eq),
    &sum {K*val(X,t+M),I:arith_law_atom(K,X,I,L,M);K*X,I:arith_law_atom(K,X,I,L)} = C, 
    arithmetic(L,C).

arithmetic_fulfilled(L,t) :- arithmetic_law(L,ne),
    &sum {K*val(X,t+M),I:arith_law_atom(K,X,I,L,M);K*X,I:arith_law_atom(K,X,I,L)} != C,
    arithmetic(L,C).

arithmetic_fulfilled(L,t) :- arith_law_simp(L,C,F),
    &sum {F*K*val(X,t+M),I:arith_law_atom(K,X,I,L,M);F*K*X,I:arith_law_atom(K,X,I,L)} < C.

%---------------------------------------------------------
% An assignment is legal if the value of the head would be inside it's domain

arithmetic_illegal(L,t) :- arithmetic_head(L,V,_,_), arithmetic_assignment(L), arithmetic(L,C), integer_domain(V,LD,UD), &sum {K*val(X,t+M),I:arith_law_atom(K,X,I,L,M),not arithmetic_head(L,X,K,I);K*X,I:arith_law_atom(K,X,I,L)} < C-UD.

arithmetic_illegal(L,t) :- arithmetic_head(L,V,_,_), arithmetic_assignment(L), arithmetic(L,C), integer_domain(V,LD,UD), &sum {K*val(X,t+M),I:arith_law_atom(K,X,I,L,M),not arithmetic_head(L,X,K,I);K*X,I:arith_law_atom(K,X,I,L)} > C-LD.

arithmetic_illegal(L,t) :- arithmetic_head(L,V,_,_), arithmetic_assignment_dynamic(L), arithmetic(L,C), integer_domain(V,LD,UD), &sum {K*val(X,t+M),I:arith_law_atom(K,X,I,L,M),not arithmetic_head(L,X,K,I);K*X,I:arith_law_atom(K,X,I,L)} < C-UD.

arithmetic_illegal(L,t) :- arithmetic_head(L,V,_,_), arithmetic_assignment_dynamic(L), arithmetic(L,C), integer_domain(V,LD,UD), &sum {K*val(X,t+M),I:arith_law_atom(K,X,I,L,M),not arithmetic_head(L,X,K,I);K*X,I:arith_law_atom(K,X,I,L)} > C-LD.
%---------------------------------------------------------
% SMT to HTC encoding
% (Integers must be assigned at each step.)

% Handle inertial laws (domain/2 doesn't exist integers)
assigned(V,t) :- integer(V), inertial(V),
    &sum{val(V,t); -K*val(C,t):arithmetic_head(I,C,K,_),arithmetic_additive_fluent(I,V)} = val(V,t-1). % Includes increment helpers!

% An integer is assigned if there is a dynamic law assigning it.
assigned(V,t) :- integer(V), arithmetic_head(L,V,_,_), 
    holds(_arithmetic(L),t), not arithmetic_illegal(L,t),
    allassigned(L,t-1),
    arithmetic_assignment_dynamic(L).

% An integer is assigned if there is a static law assigning it.
assigned(V,t) :- integer(V), arithmetic_head(L,V,_,_), 
    holds(_arithmetic(L),t), not arithmetic_illegal(L,t),
    allassigned(L,t),
    arithmetic_assignment(L).

% All integers must be assigned at any step.
:- not assigned(V,t), integer(V).

%---------------------------------------------------------
% Simplifications

% Collect assigned atoms
allassigned(L,t) :- arithmetic_law(L,_),
    assigned(V,t) : arithmetic(L,V,_,_,_), integer(V).

allassigned_head(L,t) :- arithmetic_law(L,_),
    assigned(V,t) : arithmetic_head(L,V,_,_), integer(V).

allassigned(L,t) :- arithmetic_law(L,_), ifcons(_,_arithmetic(L)), 
    not not assigned(V,t) : arithmetic(L,V,_,_,_), integer(V).

allassigned_head(L,t) :- arithmetic_law(L,_), ifcons(_,_arithmetic(L)), 
    not not assigned(V,t) : allassigned_head(L,V,_,_), integer(V).

%---------------------------------------------------------
% Divisions

%Trunc  
:- arithmetic_division(V,L,R,X), not &sum {R*val(X,t); -L*val(V,t)} <= 0.
:- arithmetic_division(V,L,R,X), not &sum {R*val(X,t); -L*val(V,t)} > -R.

%---------------------------------------------------------
% Helpers for additive statements
% Displays values of helpers for additive statements
%&show {val(X,t) : arithmetic_additive_law(L), arithmetic_head(L,X,_,_)}.

% Notes if the helper is set to the result of the additive statement
arithmetic_fulfilled(L,t) :- arithmetic_additive_law(L),
    &sum {K*val(X,t+M),I:arith_law_atom(K,X,I,L,M);K*X,I:arith_law_atom(K,X,I,L)} = C, 
    arithmetic(L,C).

% Requires the additive helper to be 0 otherwise
:- not holds(_arithmetic(L),t), arithmetic_additive_law(L),
    arithmetic_head(L,C,K,_),
    not &sum {val(C,t)} = 0.

% There is no allassigned for additive laws.
:- arithmetic_additive_law(L), holds(_arithmetic(L),t), not arithmetic_fulfilled(L,t).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%% Query: Check finallys
#program check(t).

%%%#external query(t).% Done by the internal encoding

% Goals for planning
:- not holds(val(G,GV),t), finally(val(G,GV)), query(t).
:- not holds(_arithmetic(L),t), finally(_arithmetic(L)), query(t).
%:- t < 2, query(t).
%:- t == 0, query(t).

