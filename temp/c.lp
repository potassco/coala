#const k=1.
step(0..k).

fluent(X) :- defined_fluent(X).
atom(val(F,B)) :- domain(F,B).

% Initial choice
{ holds(val(F,B),0) : domain(F,B) } = 1 :- fluent(F), not defined_fluent(F).

% Action occurence
{ occurs(A,T) : action(A) } :- step(T), T < k.

% Static laws
holds(F,T) :- static_law(I), head(I,F), 
        holds(val(P,V),T) : if(I,val(P,V)); 
        not not holds(val(P,V),T) : ifcons(I,val(P,V));  
        step(T).

%holds(F,T) :- static_law(I), head(I,F), 
%        holds(P,T) : if(I,P), atom(P); 
%        not not holds(P,T) : ifcons(I,P);
%        step(T).

% Dynamic laws
holds(F,T) :- dynamic_law(I), head(I,F), 
        holds(P,T-1) : after(I,P), atom(P); 
        occurs(A,T-1) : after(I,A), action(A); 
        not not holds(P,T) : ifcons(I,P); 
        step(T), T > 0.

% Fluent domain restriction
:- { holds(val(X,_),T) } != 1, fluent(X), step(T). 

