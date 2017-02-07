% Theory
#include "csp.lp".

% Domains of integers
&dom {L..U : integer_domain(V,L,U)} = val(V,T) :- step(T), integer_domain(V,_,_).

% Include integers in answer sets.
&show {val(I,T) : integer(I), step(T)}.

%---------------------------------------------------------
% Transitions
#include "base_translation.lp".

% arithmetic_laws are atoms, therefore they can hold at time steps.
atom(_arithmetic(L)) :- arithmetic_law(L,_).

% Dynamic Assignments
:- holds(_arithmetic(L),T), allassigned(L,T-1), 
    arithmetic_assignment_dynamic(L), not arithmetic_fulfilled(L,T), 
    step(T), step(T-1).

% Static Assignments
:- holds(_arithmetic(L),T), allassigned(L,T), 
    arithmetic_assignment(L), not arithmetic_fulfilled(L,T), 
    step(T).

% Non-Assignments which appear in bodys:
holds(_arithmetic(L),T) :- allassigned(L,T), 
    allassigned_head(L,T), not arithmetic_assignment(L), 
    not arithmetic_assignment_dynamic(L), arithmetic_fulfilled(L,T), 
    step(T).

%------------------------------------------------

% Handle equations
arithmetic_fulfilled(L,T) :- arithmetic_law(L,eq),
    &sum {K*X,I:arith_law_atom(K,X,I,L,T)} = C, 
    arithmetic(L,C), step(T).

arithmetic_fulfilled(L,T) :- arithmetic_law(L,ne),
    &sum {K*X,I:arith_law_atom(K,X,I,L,T)} != C,
    arithmetic(L,C), step(T).

arithmetic_fulfilled(L,T) :- arith_law_simp(L,C,F),
    &sum {F*K*X,I:arith_law_atom(K,X,I,L,T)} < C,
    step(T).

%---------------------------------------------------------
% SMT to HTC encoding
% (Integers must be assigned at each step.)

% Initial values are assumed to be assigned for the initial step
assigned(V,0) :- integer(V), step(0).

% Handle inertial laws (domain/2 doesn't exist integers)
assigned(V,T) :- integer(V), inertial(V),
    &sum{val(V,T)} = val(V,T-1), 
    step(T), step(T-1).

% An integer is assigned if there is a dynamic law assigning it.
assigned(V,T) :- integer(V), arithmetic_head(L,V,_,_), 
    holds(_arithmetic(L),T), 
    allassigned(L,T-1),
    arithmetic_assignment_dynamic(L), 
    step(T), step(T-1).

% An integer is assigned if there is a static law assigning it.
assigned(V,T) :- integer(V), arithmetic_head(L,V,_,_), 
    holds(_arithmetic(L),T), 
    allassigned(L,T),
    arithmetic_assignment(L), step(T).

% All integers must be assigned at any step.
:- not assigned(V,T), integer(V), step(T).

%---------------------------------------------------------
% Simplifications

% Collect assigned atoms
allassigned(L,T) :- arithmetic_law(L,_),
    assigned(V,T) : arithmetic(L,V,_,_), integer(V);  
    step(T).

allassigned_head(L,T) :- arithmetic_law(L,_),
    assigned(V,T) : arithmetic_head(L,V,_,_), integer(V);
    step(T).

% Handle Atoms that are unknown during the translation process
arithmetic(L,V,K,I):-       arithmetic(L,_unknown,V,K,I),   integer(V).
arithmetic(L,K,V,I):-       arithmetic(L,_unknown,V,K,I),   not integer(V), integer(K).
arithmetic(L,_sum,V,K,I):-  arithmetic(L,_unknown,V,K,I),   not integer(V), not integer(K).

arithmetic(L,V,K*U,I):-     arithmetic(L,_unknown,V,U,K,I), integer(V),     not integer(U).
arithmetic(L,U,K*V,I):-     arithmetic(L,_unknown,V,U,K,I), not integer(V), integer(U).

% Collect atoms for the sum construct
arith_law_atom(K,val(X,T-1),I,L,T) :- arithmetic(L,X,K,I), 
    arithmetic_assignment_dynamic(L), 
    arithmetic(L,C), 
    step(T), step(T-1).

arith_law_atom(K,val(X,T),I,L,T) :- arithmetic(L,X,K,I), 
    not arithmetic_assignment_dynamic(L), 
    arithmetic(L,C), 
    step(T).

arith_law_atom(K,val(X,T),I,L,T) :- arithmetic_head(L,X,K,I), 
    arithmetic(L,C), 
    step(T).

arith_law_atom(K,X,I,L,T) :- arithmetic(L,_sum,X,K,I), 
    arithmetic(L,C),
    step(T).

% Convert laws to "lower than"
arith_law_simp(L,C,1) :-     arithmetic_law(L,lt), arithmetic(L,C). 
arith_law_simp(L,C+1,1) :-   arithmetic_law(L,le), arithmetic(L,C).
arith_law_simp(L,-C,-1) :-   arithmetic_law(L,gt), arithmetic(L,C).
arith_law_simp(L,-C+1,-1) :- arithmetic_law(L,ge), arithmetic(L,C).

%---------------------------------------------------------
% Divisions
arithmetic_division(V,L,F*R,X) :- arithmetic_helper_division(V,L,F,R,X).

%Trunc  
:- arithmetic_division(V,L,R,X), not &sum {R*val(X,T); -L*val(V,T)} <= 0, step(T).
:- arithmetic_division(V,L,R,X), not &sum {R*val(X,T); -L*val(V,T)} > -R, step(T).

%Ceil
%:- arithmetic_division(V,L,R,X), not &sum {R*val(X,T); -L*val(V,T)} < R, step(T).
%:- arithmetic_division(V,L,R,X), not &sum {R*val(X,T); -L*val(V,T)} >= 0, step(T).

%Round
%:- arithmetic_division(V,L,R,X), not &sum {2*R*val(X,T); -2*L*val(V,T)} < R, step(T).
%:- arithmetic_division(V,L,R,X), not &sum {2*R*val(X,T); -2*L*val(V,T)} >= -R, step(T).


% Divisions are extracted and replaced by a helper integer that 
% will yield the rounded result of the division.
% The division itself will then be handled in the additional laws below.
%
% Example for truncation:
% ( a / 3 ) is replaced by h 
% where (3 * h - 1 * a <= 0) and (3 * h - 1 * a > -3)
% So if a is 10: (3*h <= 10) and (3*h > 7); meaning h can only be 3

%%%%%%%%%%%%%

%&show {val(X,T) : arithmetic_additive_law(L), arithmetic_head(L,X,_,_), step(T)}.

%%%%%%%%%%%%%%%%%%%


allassigned(L,T) :- arithmetic_additive_law(L),
    assigned(V,T) : arithmetic(L,V,_,_), integer(V);  
    step(T).

arithmetic_fulfilled(L,T) :- arithmetic_additive_law(L),
    &sum {K*X,I:arith_law_atom(K,X,I,L,T)} = C, 
    arithmetic(L,C), step(T).

:- holds(_arithmetic(L),T), arithmetic_fulfilled(L,T), 
    arithmetic_additive_law(L), arithmetic_additive_fluent(L,X), 
    not &sum {val(X,T); -1*val(X,T-1); -K*val(C,T):arithmetic_head(I,C,K,_),arithmetic_additive_fluent(I,X)} = 0,
    step(T), step(T-1).

:- not holds(_arithmetic(L),T), arithmetic_additive_law(L),
    arithmetic_head(L,C,K,_),
    not &sum {val(C,T)} = 0, 
    step(T).

:- arithmetic_additive_fluent(_,X), 
    not &sum {val(X,T); -K*val(C,T):arithmetic_head(I,C,K,_),arithmetic_additive_fluent(I,X)} = val(X,T-1),
    step(T), step(T-1).

assigned(V,T) :- integer(V), arithmetic_additive_fluent(L,V), step(T).




%:- arithmetic_additive_fluent(law(1),x),
%    not &sum {val(x,1); -val(additive_helper(law(1),x),1) } = val(x,0).



