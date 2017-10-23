
fluent(X) :- defined_fluent(X).

holds(Ac,0) :- occurs(Ac,0).
:- holds(act(Ac),0), not occurs(act(Ac),0).

{holds(val(F,V),1)} :- inertial(F), holds(val(F,V),0).

{holds(F,1)} :- default(F).
{holds(F,1)} :- default(I,F), 
    holds(P,1) : if(I,P); 
    holds(P,0) : after(I,P).

holds(F,1) :- static_law(I), head(I,F), 
    holds(P,1) : if(I,P); 
    not holds(val(P,O),1) : ifcons(I,val(P,C)), domain(P,O), C != O; 
    not not holds(P,1) : ifcons(I,P).

holds(F,1) :- dynamic_law(I), head(I,F), 
    holds(P,0) : after(I,P); 
    not holds(val(P,O),1) : ifcons(I,val(P,C)), domain(P,O), C != O; 
    not not holds(P,1) : ifcons(I,P).

fail :- impossible(I,_), 
    holds(P,1) : impossible(I,P); 
    not holds(val(P,O),1) : ifcons(I,val(P,C)), domain(P,O), C != O; 
    not not holds(P,1) : ifcons(I,P).

fail :- nonexecutable(I,_), 
    holds(P,0) : nonexecutable(I,P); 
    not holds(val(P,O),1) : ifcons(I,val(P,C)), domain(P,O), C != O; 
    not not holds(P,1) : ifcons(I,P).

fail :- fluent(X), 2{ holds(val(X,A),1):domain(X,A) }. 
:- fluent(X), not { holds(val(X,A),1):domain(X,A) }1.
fail :- holds(_false,1).

:- not fail.
%:- fail.
