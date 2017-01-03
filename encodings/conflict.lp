#const k=1.
step(0..k).

fluent(X) :- defined_fluent(X).
atom(val(F,B)) :- domain(F,B).

% Initial choice
{ holds(val(F,B),0) : domain(F,B) } = 1 :- fluent(F), not defined_fluent(F).

% Action occurence
{ occurs(A,T) : action(A) } :- step(T), T < k.

% Static laws
holds(H,T) :- static_law(I), head(I,H), 
        holds(F,T) : if(I,F), atom(F); 
        not not holds(F,T) : ifcons(I,F); 
        not holds(val(F,O),T) : ifcons(I,val(F,C)), domain(F,O), C != O; 
        step(T).

% Dynamic laws
holds(H,T) :- dynamic_law(I), head(I,H), 
        holds(F,T-1) : after(I,F), atom(F); 
        occurs(A,T-1) : after(I,A), action(A); 
        not not holds(F,T) : ifcons(I,F); 
        not holds(val(F,O),T) : ifcons(I,val(F,C)), domain(F,O), C != O; 
        step(T), T > 0.

% Fluent domain restriction
:- { holds(val(X,_),0) } != 1, fluent(X). 
fail(X) :- { holds(val(X,_),T) } != 1, fluent(X), step(T), T > 0. 
:- not fail(_).

% Simplification for impossible and nonexecutable laws
fail(_false) :- holds(_false,T), step(T).
