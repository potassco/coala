
fluent(X) :- defined_fluent(X).

{occurs(Ac,0) : action(Ac)}.
holds(Ac,0) :- occurs(Ac,0).
occurs(Ac,0) :- holds(Ac,0), action(Ac).

{holds(val(F,V),1)} :- inertial(F), holds(val(F,V),0).

{holds(F,1)} :- default(F).
{holds(F,1)} :- default(I,F), 
    holds(P,1) : if(I,P); 
    holds(P,0) : after(I,P).

holds(F,1) :- static_law(I), head(I,F), 
    holds(P,1) : if(I,P); 
    not not holds(P,1) : ifcons(I,P).

holds(F,1) :- dynamic_law(I), head(I,F), 
    holds(P,0) : after(I,P); 
    not not holds(P,1) : ifcons(I,P).

:- impossible(I,_), 
    holds(P,1) : impossible(I,P); 
    not not holds(P,1) : ifcons(I,P).

:- nonexecutable(I,_), 
    holds(P,0) : nonexecutable(I,P); 
    not not holds(P,1) : ifcons(I,P).

:- fluent(X), not 1{ holds(val(X,A),1) }1. 
:- holds(_false,1).
