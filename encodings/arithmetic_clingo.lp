% Transitions
#include "base_translation.lp".


fluent(F) :- integer(F).
domain(F,L..U) :- integer_domain(F,L,U).

%---------------------------------------------------------

% arithmetic_laws are atoms, therefore they can hold at time steps.
atom(_arithmetic(L)) :- arithmetic_law(L,_).

% Enforces arithmetics to hold when laws do.
:- holds(_arithmetic(L),T), not arithmetic_fulfilled(L,T), not arithmetic_illegal(L,T). %TODO: this can be rewritten as a domain() check inside the laws

% Non-Assignments which appear in bodys:
holds(_arithmetic(L),T) :- %not ifcons(_,_arithmetic(L)),
    arithmetic_fulfilled(L,T), 
    %not arithmetic_assignment(L),
    %not arithmetic_assignment_dynamic(L), 
    step(T).

% Handling ifcons parts
%holds(_arithmetic(L),T) :- arithmetic_fulfilled(L,T), ifcons(_,_arithmetic(L)), step(T).

%------------------------------------------------
holds(val(F,V),T) :- domain(F,V), arithmetic_assignment(L), not arithmetic_illegal(L,T), holds(_arithmetic(L),T), arithmetic_law(L,eq), arithmetic_head(L,F,M,_), arithmetic(L,C), 
    holds(val(X,_),T+MD) : arithmetic(L,X,K,I,MD);
    V = (H+C)/M,
    #sum {-K*Z,I:arithmetic(L,X,K,I,MD),holds(val(X,Z),T+MD);-K*X,I:arithmetic(L,_sum,X,K,I,_)} = H, step(T).%%%

holds(val(F,V),T) :- domain(F,V), arithmetic_assignment_dynamic(L), not arithmetic_illegal(L,T), holds(_arithmetic(L),T), arithmetic_law(L,eq), arithmetic_head(L,F,M,_), arithmetic(L,C), 
    holds(val(X,_),T+MD) : arithmetic(L,X,K,I,MD);
    V = (H+C)/M,
    #sum {-K*Z,I:arithmetic(L,X,K,I,MD),holds(val(X,Z),T+MD);-K*X,I:arithmetic(L,_sum,X,K,I,_)} = H, step(T).%%%

%------------------------------------------------
% Handle equations

arithmetic_fulfilled(L,T) :- arithmetic_law(L,eq),
    %&sum {K*val(X,t),I:arith_law_atom(K,X,I,L,0);K*X,I:arith_law_atom(K,X,I,L)} = C,
    holds(val(X,_),T+M) : arith_law_atom(_,X,_,L,M);
    #sum {K*V,I:arith_law_atom(K,X,I,L,M),holds(val(X,V),T+M);K*X,I:arith_law_atom(K,X,I,L)} = C,  
    arithmetic(L,C), step(T).

arithmetic_fulfilled(L,T) :- arithmetic_law(L,ne),
    %&sum {K*val(X,t),I:arith_law_atom(K,X,I,L,t);K*X,I:arith_law_atom(K,X,I,L)} != C,
    holds(val(X,_),T+M) : arith_law_atom(_,X,_,L,M);
    #sum {K*V,I:arith_law_atom(K,X,I,L,M),holds(val(X,V),T+M);K*X,I:arith_law_atom(K,X,I,L)} != C,
    arithmetic(L,C), step(T).

arithmetic_fulfilled(L,T) :- arith_law_simp(L,C,_),
    %&sum {F*K*val(X,t),I:arith_law_atom(K,X,I,L,t);F*K*X,I:arith_law_atom(K,X,I,L)} < C.
    holds(val(X,_),T+M) : arith_law_atom(_,X,_,L,M);
    #sum {F*K*V,I:arith_law_atom(K,X,I,L,M),holds(val(X,V),T+M),arith_law_simp(L,_,F);F*K*X,I:arith_law_atom(K,X,I,L),arith_law_simp(L,_,F)} < C, step(T).

%ar_x(L,C,T) :- arith_law_simp(L,_,F),
%    %&sum {F*K*val(X,t),I:arith_law_atom(K,X,I,L,t);F*K*X,I:arith_law_atom(K,X,I,L)} < C.
%    holds(val(X,_),T+M) : arith_law_atom(_,X,_,L,M);
%    #sum {K*V,I:arith_law_atom(K,X,I,L,M),holds(val(X,V),T+M);K*X,I:arith_law_atom(K,X,I,L)} = C, step(T).


%arithmetic_fulfilled(L,T) :- arithmetic_law(L,eq),
%    &sum {K*val(X,T+M),I:arith_law_atom(K,X,I,L,M),step(T+M);K*X,I:arith_law_atom(K,X,I,L)} = C, 
%    arithmetic(L,C), step(T).

%arithmetic_fulfilled(L,T) :- arithmetic_law(L,ne),
%    &sum {K*val(X,T+M),I:arith_law_atom(K,X,I,L,M),step(T+M);K*X,I:arith_law_atom(K,X,I,L)} != C,
%    arithmetic(L,C), step(T).

%arithmetic_fulfilled(L,T) :- arith_law_simp(L,C,F),
%    &sum {F*K*val(X,T+M),I:arith_law_atom(K,X,I,L,M),step(T+M);F*K*X,I:arith_law_atom(K,X,I,L)} < C,
%    step(T).

%---------------------------------------------------------
% An assignment is legal if the value of the head would be inside it's domain

arithmetic_illegal(L,T) :- arithmetic_head(L,F,_,_), step(T+M):arith_law_atom(_,_,_,L,M); arithmetic_assignment(L), arithmetic(L,C), integer_domain(F,LD,UD), #sum {K*V,I:arith_law_atom(K,X,I,L,M),holds(val(X,V),T+M),not arithmetic_head(L,X,K,I);K*X,I:arith_law_atom(K,X,I,L)} < C-UD;  step(T).

arithmetic_illegal(L,T) :- arithmetic_head(L,F,_,_), step(T+M):arith_law_atom(_,_,_,L,M); arithmetic_assignment(L), arithmetic(L,C), integer_domain(F,LD,UD), #sum {K*V,I:arith_law_atom(K,X,I,L,M),holds(val(X,V),T+M),not arithmetic_head(L,X,K,I);K*X,I:arith_law_atom(K,X,I,L)} > C-LD; step(T).

arithmetic_illegal(L,T) :- arithmetic_head(L,F,_,_), step(T+M):arith_law_atom(_,_,_,L,M); arithmetic_assignment_dynamic(L), arithmetic(L,C), integer_domain(F,LD,UD), #sum {K*V,I:arith_law_atom(K,X,I,L,M),holds(val(X,V),T+M),not arithmetic_head(L,X,K,I);K*X,I:arith_law_atom(K,X,I,L)} < C-UD;  step(T).

arithmetic_illegal(L,T) :- arithmetic_head(L,F,_,_), step(T+M):arith_law_atom(_,_,_,L,M); arithmetic_assignment_dynamic(L), arithmetic(L,C), integer_domain(F,LD,UD), #sum {K*V,I:arith_law_atom(K,X,I,L,M),holds(val(X,V),T+M),not arithmetic_head(L,X,K,I);K*X,I:arith_law_atom(K,X,I,L)} > C-LD; step(T).
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

arith_law_atom(K,X,I,L) :- arithmetic(L,_sum,X,K,I,_), 
    arithmetic(L,C).

% Convert laws to "lower than"
arith_law_simp(L,C,1) :-     arithmetic_law(L,lt), arithmetic(L,C). 
arith_law_simp(L,C+1,1) :-   arithmetic_law(L,le), arithmetic(L,C).
arith_law_simp(L,-C,-1) :-   arithmetic_law(L,gt), arithmetic(L,C).
arith_law_simp(L,-C+1,-1) :- arithmetic_law(L,ge), arithmetic(L,C).

%---------------------------------------------------------
% Divisions

%arithmetic_division(V,L,F*R,X) :- arithmetic_helper_division(V,L,F,R,X).
holds(val(X,S),T):- S = (Z*L)/(F*R), holds(val(V,Z),T), arithmetic_helper_division(V,L,F,R,X), step(T). %trunc
%holds(val(X,S,Z,L,F,R),T) :- S = (Z*L)/(F*R), holds(val(V,Z),T), arithmetic_helper_division(V,L,F,R,X), step(T). %trunc

%Trunc  
%:- arithmetic_division(V,L,R,X), not &sum {R*val(X,T); -L*val(V,T)} <= 0, step(T).
%:- arithmetic_division(V,L,R,X), not &sum {R*val(X,T); -L*val(V,T)} > -R, step(T).

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

