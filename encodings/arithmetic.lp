% Theory
#include "csp.lp".

% Domains of integers
%&dom {L..U} = val(V,T) :- integer(V), integer_domain(V,L,U), step(T).
%&dom {L..U : integer_domain(V,L,U)} = val(V,T) :- integer(V), step(T).
&dom {L..U : integer_domain(V,L,U)} = val(V,T) :- step(T), integer_domain(V,_,_).

% Include integers in answer sets.
&show {val(I,T) : integer(I), step(T)}.

%---------------------------------------------------------

%% Include initially statements
%:- initially(val(V,X)), integer(V), not &sum{val(V,0)} = X.

% Transitions
#include "base_translation.lp".

% Handle inertial laws. (won't be handled in the base_translation.lp part as there is no domain/2 for integers)
assigned(V,T) :- integer(V), inertial(V), step(T), step(T-1), &sum{val(V,T)} = val(V,T-1).

% Initial values are assumed to be assigned for the initial step
%assigned(V,0) :- integer(V), initially(val(V,_)), step(0).
assigned(V,0) :- integer(V), step(0).

% An integer is assigned if there is a dynamic law assigning it.
assigned(V,T) :- integer(V), arithmetic_head(L,V,_,_), 
    holds(_arithmetic(L),T), 
    allassigned(L,T-1), % This is required for dynamic laws to prevent loops
    arithmetic_assignment_dynamic(L), step(T), step(T-1).

% An integer is assigned if there is a static law assigning it.
assigned(V,T) :- integer(V), arithmetic_head(L,V,_,_), 
    holds(_arithmetic(L),T), 
    allassigned(L,T),
    arithmetic_assignment(L), step(T).

% All integers must be assigned at any step.
:- not assigned(V,T), integer(V), step(T).

%---------------------------------------------------------

%Divisions!
arithmetic_division(V,L,F*R,X) :- arithmetic_helper_division(V,L,F,R,X).

%Trunc
:- arithmetic_division(V,L,R,X), step(T), not &sum {R*val(X,T); -L*val(V,T)} <= 0.
:- arithmetic_division(V,L,R,X), step(T), not &sum {R*val(X,T); -L*val(V,T)} > -R.

%Ceil
%:- arithmetic_helper_division(V,L,R,X), step(T), not &sum {R*val(X,T); -L*val(V,T)} < R.
%:- arithmetic_helper_division(V,L,R,X), step(T), not &sum {R*val(X,T); -L*val(V,T)} >= 0.

%Round
%:- arithmetic_helper_division(V,L,R,X), step(T), not &sum {2*R*val(X,T); -2*L*val(V,T)} < R.
%:- arithmetic_helper_division(V,L,R,X), step(T), not &sum {2*R*val(X,T); -2*L*val(V,T)} >= -R.

%Show helper
%&show {val(X,T): arithmetic_helper_division(V,L,F,R,X), step(T)}.

%---------------------------------------------------------

% Simplification
arithmetic_law(L) :- arithmetic(L,_).

% arithmetic_laws are atoms, therefore they can hold at time steps.
atom(_arithmetic(L)) :- arithmetic_law(L).

% Workaround concerning a bug; Arithmetic laws are only used if all integers in it are assigned!
allassigned(L,T) :- assigned(V,T) : arithmetic(L,V,_,_), integer(V); arithmetic_law(L,_), step(T).
allassigned_head(L,T) :- assigned(V,T) : arithmetic_head(L,V,_,_), integer(V); arithmetic_law(L,_), step(T).

arithmetic(L,V,K,I):- arithmetic(L,_unknown,V,K,I), integer(V).
arithmetic(L,K,V,I):- arithmetic(L,_unknown,V,K,I), not integer(V), integer(K).
arithmetic(L,V,K*U,I):- arithmetic(L,_unknown,V,U,K,I), integer(V), not integer(U).
arithmetic(L,U,K*V,I):- arithmetic(L,_unknown,V,U,K,I), not integer(V), integer(U).
arithmetic(L,_sum,V,K,I):- arithmetic(L,_unknown,V,K,I), not integer(V), not integer(K).


arithmetic_fulfilled(L,T) :- &sum {K*val(X,T-1),I:arithmetic(L,X,K,I);K*val(X,T),I:arithmetic_head(L,X,K,I);K*X,I:arithmetic(L,_sum,X,K,I)} = C, arithmetic_assignment_dynamic(L), arithmetic_law(L,eq), arithmetic(L,C), step(T), step(T-1).
arithmetic_fulfilled(L,T) :- &sum {K*val(X,T-1),I:arithmetic(L,X,K,I);K*val(X,T),I:arithmetic_head(L,X,K,I);K*X,I:arithmetic(L,_sum,X,K,I)} < C, arithmetic_assignment_dynamic(L), arithmetic_law(L,lt), arithmetic(L,C), step(T), step(T-1).
arithmetic_fulfilled(L,T) :- &sum {K*val(X,T-1),I:arithmetic(L,X,K,I);K*val(X,T),I:arithmetic_head(L,X,K,I);K*X,I:arithmetic(L,_sum,X,K,I)} <= C, arithmetic_assignment_dynamic(L), arithmetic_law(L,le), arithmetic(L,C), step(T), step(T-1).
arithmetic_fulfilled(L,T) :- &sum {K*val(X,T-1),I:arithmetic(L,X,K,I);K*val(X,T),I:arithmetic_head(L,X,K,I);K*X,I:arithmetic(L,_sum,X,K,I)} > C, arithmetic_assignment_dynamic(L), arithmetic_law(L,gt), arithmetic(L,C), step(T), step(T-1).
arithmetic_fulfilled(L,T) :- &sum {K*val(X,T-1),I:arithmetic(L,X,K,I);K*val(X,T),I:arithmetic_head(L,X,K,I);K*X,I:arithmetic(L,_sum,X,K,I)} >= C, arithmetic_assignment_dynamic(L), arithmetic_law(L,ge), arithmetic(L,C), step(T), step(T-1).
arithmetic_fulfilled(L,T) :- &sum {K*val(X,T-1),I:arithmetic(L,X,K,I);K*val(X,T),I:arithmetic_head(L,X,K,I);K*X,I:arithmetic(L,_sum,X,K,I)} != C, arithmetic_assignment_dynamic(L), arithmetic_law(L,ne), arithmetic(L,C), step(T), step(T-1).
arithmetic_fulfilled(L,T) :- &sum {K*val(X,T),I:arithmetic(L,X,K,I);K*val(X,T),I:arithmetic_head(L,X,K,I);K*X,I:arithmetic(L,_sum,X,K,I)} = C, not arithmetic_assignment_dynamic(L), arithmetic_law(L,eq), arithmetic(L,C), step(T).
arithmetic_fulfilled(L,T) :- &sum {K*val(X,T),I:arithmetic(L,X,K,I);K*val(X,T),I:arithmetic_head(L,X,K,I);K*X,I:arithmetic(L,_sum,X,K,I)} < C, not arithmetic_assignment_dynamic(L), arithmetic_law(L,lt), arithmetic(L,C), step(T).
arithmetic_fulfilled(L,T) :- &sum {K*val(X,T),I:arithmetic(L,X,K,I);K*val(X,T),I:arithmetic_head(L,X,K,I);K*X,I:arithmetic(L,_sum,X,K,I)} <= C, not arithmetic_assignment_dynamic(L), arithmetic_law(L,le), arithmetic(L,C), step(T).
arithmetic_fulfilled(L,T) :- &sum {K*val(X,T),I:arithmetic(L,X,K,I);K*val(X,T),I:arithmetic_head(L,X,K,I);K*X,I:arithmetic(L,_sum,X,K,I)} > C, not arithmetic_assignment_dynamic(L), arithmetic_law(L,gt), arithmetic(L,C), step(T).
arithmetic_fulfilled(L,T) :- &sum {K*val(X,T),I:arithmetic(L,X,K,I);K*val(X,T),I:arithmetic_head(L,X,K,I);K*X,I:arithmetic(L,_sum,X,K,I)} >= C, not arithmetic_assignment_dynamic(L), arithmetic_law(L,ge), arithmetic(L,C), step(T).
arithmetic_fulfilled(L,T) :- &sum {K*val(X,T),I:arithmetic(L,X,K,I);K*val(X,T),I:arithmetic_head(L,X,K,I);K*X,I:arithmetic(L,_sum,X,K,I)} != C, not arithmetic_assignment_dynamic(L), arithmetic_law(L,ne), arithmetic(L,C), step(T).

% Handle arithmetics!
% Assignments
% ^-- dynamic
:- holds(_arithmetic(L),T), allassigned(L,T-1), arithmetic_assignment_dynamic(L), step(T), step(T-1), not arithmetic_fulfilled(L,T).

% ^-- static
:- holds(_arithmetic(L),T), allassigned(L,T), arithmetic_assignment(L), step(T), not arithmetic_fulfilled(L,T).

% Non-Assignments which appear in bodys:
holds(_arithmetic(L),T) :- allassigned(L,T), allassigned_head(L,T), not arithmetic_assignment(L), not arithmetic_assignment_dynamic(L), step(T), arithmetic_fulfilled(L,T).


%%%%%%%%%%%%%

