
fluent(X) :- defined_fluent(X).

1{holds(val(F,B),0) : domain(F,B)}1 :- fluent(F), not defined_fluent(F).
{holds(F,0)} :- default(F).
{holds(F,0)} :- default(I,F), 
    holds(P,0) : if(I,P); 
    not after(I,_).

holds(F,0) :- static_law(I), head(I,F), 
    holds(P,0) : if(I,P); 
    not not holds(P,0) : ifcons(I,P).

:- impossible(I,_), 
    holds(P,0) : impossible(I,P); 
    not not holds(P,0) : ifcons(I,P).

:- fluent(X), not 1{ holds(val(X,A),0):domain(X,A) }1.
:- holds(_false,0).
