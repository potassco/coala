% Theory
#include "csp.lp".
% Transitions
#include "base_translation.lp".

% Domains of integers
&dom {L..U : integer_domain(V,L,U)} = val(V,T) :- step(T), integer_domain(V,_,_).

% Include integers in answer sets.
&show {val(I,T) : integer(I), step(T)}.

%---------------------------------------------------------

% arithmetic_laws are atoms, therefore they can hold at time steps.
atom(_arithmetic(L)) :- arithmetic_law(L,_).

% Enforces arithmetics to hold when laws do.
:- holds(_arithmetic(L),T), allassigned(L,T), not arithmetic_fulfilled(L,T).
%:- holds(_arithmetic(L),T), not arithmetic_fulfilled(L,T).

% Non-Assignments which appear in bodys:
holds(_arithmetic(L),T) :- allassigned(L,T), not ifcons(_,_arithmetic(L)),
    allassigned_head(L,T), arithmetic_fulfilled(L,T), 
    not arithmetic_assignment(L),
    not arithmetic_assignment_dynamic(L), 
    step(T).

% Handling ifcons parts
holds(_arithmetic(L),T) :- arithmetic_fulfilled(L,T), ifcons(_,_arithmetic(L)), step(T).

%------------------------------------------------
% Handle equations

arithmetic_fulfilled(L,T) :- arithmetic_law(L,eq),
    &sum {K*val(X,T+M),I:arith_law_atom(K,X,I,L,M),step(T+M);K*X,I:arith_law_atom(K,X,I,L)} = C, 
    arithmetic(L,C), step(T).

arithmetic_fulfilled(L,T) :- arithmetic_law(L,ne),
    &sum {K*val(X,T+M),I:arith_law_atom(K,X,I,L,M),step(T+M);K*X,I:arith_law_atom(K,X,I,L)} != C,
    arithmetic(L,C), step(T).

arithmetic_fulfilled(L,T) :- arith_law_simp(L,C,F),
    &sum {F*K*val(X,T+M),I:arith_law_atom(K,X,I,L,M),step(T+M);F*K*X,I:arith_law_atom(K,X,I,L)} < C,
    step(T).

%---------------------------------------------------------
% SMT to HTC encoding
% (Integers must be assigned at each step.)

% Initial values are assumed to be assigned for the initial step
assigned(V,0) :- integer(V), step(0).

% Handle inertial laws (domain/2 doesn't exist integers)
assigned(V,T) :- integer(V), inertial(V),
    &sum{val(V,T); -K*val(C,T):arithmetic_head(I,C,K,_),arithmetic_additive_fluent(I,V)} = val(V,T-1), 
    step(T), step(T-1). % Includes increment helpers!

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
%    assigned(V,T) : arithmetic(L,V,_,_,_), integer(V);
    assigned(V,T) : arithmetic(L,V,C,ID,_), integer(V), not arithmetic_ifcons(L,V,C,ID);
    not not assigned(V,T) : arithmetic(L,V,C,ID,_), integer(V), arithmetic_ifcons(L,V,C,ID);        
    step(T).

allassigned_head(L,T) :- arithmetic_law(L,_),
    assigned(V,T) : arithmetic_head(L,V,_,_), integer(V);
    step(T).

allassigned(L,T) :- arithmetic_law(L,_), ifcons(_,_arithmetic(L)), 
%    not not assigned(V,T) : arithmetic(L,V,C,ID,_), integer(V), not arithmetic_ifcons(L,V,C,ID);  
    not not assigned(V,T) : arithmetic(L,V,_,_,_), integer(V);  
    step(T).

allassigned_head(L,T) :- arithmetic_law(L,_), ifcons(_,_arithmetic(L)), 
    not not assigned(V,T) : allassigned_head(L,V,_,_), integer(V);  
    step(T).

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

