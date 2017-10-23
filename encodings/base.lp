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
        #false : if(I,F), not atom(F);
        not not holds(F,T) : ifcons(I,F); 
        step(T).

% Dynamic laws
holds(H,T) :- dynamic_law(I), head(I,H), 
        holds(F,T-1) : after(I,F), atom(F); 
        occurs(A,T-1) : after(I,A), action(A); 
        #false : after(I,F), not atom(F), not action(F);
        not not holds(F,T) : ifcons(I,F); 
        step(T), T > 0.

% Fluent domain restriction
:- { holds(val(X,A),T):domain(X,A) } != 1, fluent(X), step(T). 

% Simplification for impossible and nonexecutable laws
:- holds(_false,T), step(T).
