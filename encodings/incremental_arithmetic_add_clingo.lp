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
%:- { holds(val(X,D),0):domain(X,D) } != 1, fluent(X).

% Set initial state
%holds(F,0) :- initially(F).
:- not holds(F,0), initially(F).

:- holds(_false,0).


%% Translation
% Inertials

dynamic_law(id(inertial,F,V)) :- inertial(F), domain(F,V), not integer(F).
head(id(inertial,F,V),val(F,V)) :- inertial(F), domain(F,V), not integer(F).
after(id(inertial,F,V),val(F,V)) :- inertial(F), domain(F,V), not integer(F).
ifcons(id(inertial,F,V),val(F,V)) :- inertial(F), domain(F,V), not integer(F).

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

%---------------------------------------------------------

%% Math

% Basic clingo version: We ground every domain
fluent(F) :- integer(F).
domain(F,L..U) :- integer_domain(F,L,U).

% arithmetic_laws are atoms, therefore they can hold at time steps.
atom(_arithmetic(L)) :- arithmetic_law(L,_).

%---------------------------------------------------------

% Calculations

holds(val(F,V),0) :- domain(F,V), arithmetic_assignment(L), holds(_arithmetic(L),0), arithmetic_law(L,eq), arithmetic_head(L,F,M,_), arithmetic(L,C), 
    holds(val(X,_),MD) : arithmetic(L,X,K,I,MD);
    V = (H+C)/M,
    #sum {-K*Z,I:arithmetic(L,X,K,I,MD),holds(val(X,Z),MD);-K*X,I:arithmetic(L,_sum,X,K,I,_)} = H.

holds(val(F,V),0) :- domain(F,V),arithmetic_assignment_dynamic(L), holds(_arithmetic(L),0), arithmetic_law(L,eq), arithmetic_head(L,F,M,_), arithmetic(L,C), 
    holds(val(X,_),MD) : arithmetic(L,X,K,I,MD);
    V = (H+C)/M,
    #sum {-K*Z,I:arithmetic(L,X,K,I,MD),holds(val(X,Z),MD);-K*X,I:arithmetic(L,_sum,X,K,I,_)} = H.

holds(_arithmetic(L),0) :- arithmetic_law(L,eq),
    holds(val(X,_),MD) : arith_law_atom(_,X,_,L,MD);
    #sum {K*V,I:arith_law_atom(K,X,I,L,MD),holds(val(X,V),MD);K*X,I:arith_law_atom(K,X,I,L)} = C,  
    arithmetic(L,C).

holds(_arithmetic(L),0) :- arithmetic_law(L,ne),
    holds(val(X,_),MD) : arith_law_atom(_,X,_,L,MD);
    #sum {K*V,I:arith_law_atom(K,X,I,L,MD),holds(val(X,V),MD);K*X,I:arith_law_atom(K,X,I,L)} != C,
    arithmetic(L,C).

holds(_arithmetic(L),0) :- arith_law_simp(L,C,_),
    holds(val(X,_),MD) : arith_law_atom(_,X,_,L,MD);
    #sum {F*K*V,I:arith_law_atom(K,X,I,L,MD),holds(val(X,V),MD),arith_law_simp(L,_,F);F*K*X,I:arith_law_atom(K,X,I,L),arith_law_simp(L,_,F)} < C.

% Divisions
holds(val(X,S),0):- S = (Z*L)/(F*R), holds(val(V,Z),0), arithmetic_helper_division(V,L,F,R,X). %trunc

%---------------------------------------------------------
% Simplifications

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

arith_law_atom(K,X,I,L,M) :- arithmetic(L,_sum,X,K,I,M), 
    arithmetic(L,C).

% Convert laws to "lower than"
arith_law_simp(L,C,1) :-     arithmetic_law(L,lt), arithmetic(L,C). 
arith_law_simp(L,C+1,1) :-   arithmetic_law(L,le), arithmetic(L,C).
arith_law_simp(L,-C,-1) :-   arithmetic_law(L,gt), arithmetic(L,C).
arith_law_simp(L,-C+1,-1) :- arithmetic_law(L,ge), arithmetic(L,C).


%---------------------------------------------------------
% Helpers for additive statements

{holds(val(F,0),0)} :- arithmetic_additive_law(L), arithmetic_head(L,F,_,_).
:- {holds(val(F,_),0)}!=1,arithmetic_additive_law(L), arithmetic_head(L,F,_,_).

holds(val(F,V),0) :- holds(_arithmetic(L),0), arithmetic_additive_law(L), arithmetic_head(L,F,M,_), arithmetic(L,C), 
    holds(val(X,_),MD) : arithmetic(L,X,K,I,MD);
    V = (H+C)/M,
    #sum {-K*Z,I:arithmetic(L,X,K,I,MD),holds(val(X,Z),MD);-K*X,I:arithmetic(L,_sum,X,K,I,_)} = H.

holds(val(F,V),0) :- arithmetic_additive_law(L), holds(_arithmetic(L),0), arithmetic_head(L,F,M,_), arithmetic(L,C), 
    holds(val(X,_),MD) : arithmetic(L,X,K,I,MD);
    V = (H+C)/M,
    #sum {-K*Z,I:arithmetic(L,X,K,I,MD),holds(val(X,Z),MD);-K*X,I:arithmetic(L,_sum,X,K,I,_)} = H.

% Notes if the helper is set to the result of the additive statement
arithmetic(L2,additive_helper(L,X),-1,additive_helper(L,X),0) :-
    arithmetic_additive_fluent(L,X),
    arithmetic_assignment(L2), arithmetic_head(L2,X,_,_).

arithmetic(L2,additive_helper(L,X),-1,additive_helper(L,X),0) :-
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
%:- { holds(val(X,D),t):domain(X,D) } != 1, fluent(X).  

% Simplification for impossible and nonexecutable laws
:- holds(_false,t).

%---------------------------------------------------------

%% Math

%Calculations

holds(val(F,V),t) :- domain(F,V), arithmetic_assignment(L), 
    holds(_arithmetic(L),t), arithmetic_law(L,eq), arithmetic_head(L,F,M,_), arithmetic(L,C), 
    holds(val(X,_),t+MD) : arithmetic(L,X,K,I,MD);
    V = (H+C)/M,
    #sum {-K*Z,I:arithmetic(L,X,K,I,MD),holds(val(X,Z),t+MD);-K*X,I:arithmetic(L,_sum,X,K,I,_)} = H.

holds(val(F,V),t) :- domain(F,V), arithmetic_assignment_dynamic(L), 
    holds(_arithmetic(L),t), arithmetic_law(L,eq), arithmetic_head(L,F,M,_), arithmetic(L,C), 
    holds(val(X,_),t+MD) : arithmetic(L,X,K,I,MD);
    V = (H+C)/M,
    #sum {-K*Z,I:arithmetic(L,X,K,I,MD),holds(val(X,Z),t+MD);-K*X,I:arithmetic(L,_sum,X,K,I)} = H.

holds(_arithmetic(L),t) :- arithmetic_law(L,eq),
    holds(val(X,_),t+M) : arith_law_atom(_,X,_,L,M);
    #sum {K*V,I:arith_law_atom(K,X,I,L,M),holds(val(X,V),t+M);K*X,I:arith_law_atom(K,X,I,L)} = C,  
    arithmetic(L,C).

holds(_arithmetic(L),t) :- arithmetic_law(L,ne),
    holds(val(X,_),t+M) : arith_law_atom(_,X,_,L,M);
    #sum {K*V,I:arith_law_atom(K,X,I,L,M),holds(val(X,V),t+M);K*X,I:arith_law_atom(K,X,I,L)} != C,
    arithmetic(L,C).

holds(_arithmetic(L),t) :- arith_law_simp(L,C,_),
    holds(val(X,_),t+M) : arith_law_atom(_,X,_,L,M);
    #sum {F*K*V,I:arith_law_atom(K,X,I,L,M),holds(val(X,V),t+M),arith_law_simp(L,_,F);
        F*K*X,I:arith_law_atom(K,X,I,L),arith_law_simp(L,_,F)} < C.

% Divisions
holds(val(X,S),t):- S = (Z*L)/(F*R), holds(val(V,Z),t), arithmetic_helper_division(V,L,F,R,X). %trunc

%---------------------------------------------------------
% Helpers for additive statements

{holds(val(F,0),t)} :- arithmetic_additive_law(L), arithmetic_head(L,F,_,_).
:- {holds(val(F,_),t)}!=1,arithmetic_additive_law(L), arithmetic_head(L,F,_,_).

{holds(val(F,R),t)} :- #sum{V2:holds(val(F,V2),t-1);K*V3,I:arithmetic_head(I,C,K,_),arithmetic_additive_fluent(I,F),holds(val(C,V3),t)} = R, inertial(F), integer(F).

holds(val(F,V),t) :- arithmetic_additive_law(L), 
    holds(_arithmetic(L),t), arithmetic_head(L,F,M,_), arithmetic(L,C), 
    holds(val(X,_),t+MD) : arithmetic(L,X,K,I,MD);
    V = (H+C)/M,
    #sum {-K*Z,I:arithmetic(L,X,K,I,MD),holds(val(X,Z),t+MD);-K*X,I:arithmetic(L,_sum,X,K,I,_)} = H.

holds(val(F,V),t) :- arithmetic_additive_law(L), 
    holds(_arithmetic(L),t), arithmetic_head(L,F,M,_), arithmetic(L,C), 
    holds(val(X,_),t+MD) : arithmetic(L,X,K,I,MD);
    V = (H+C)/M,
    #sum {-K*Z,I:arithmetic(L,X,K,I,MD),holds(val(X,Z),t+MD);-K*X,I:arithmetic(L,_sum,X,K,I,_)} = H.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%% Query: Check finallys
#program check(t).
%#external query(t).% Done by the internal encoding

% Goals for planning
:- not holds(val(G,GV),t), finally(val(G,GV)), query(t).
:- not holds(_arithmetic(L),t), finally(_arithmetic(L)), query(t).
%:- t==0, query(t). %for testing

