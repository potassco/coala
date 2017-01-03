
fluent(X) :- defined_fluent(X).

{do(Ac,0) : action(Ac)}.
holds(Ac,0) :- do(Ac,0).

{holds(val(F,V),1)} :- inertial(F), holds(val(F,V),0).

{holds(F,1)} :- default(F).
{holds(F,1)} :- default(I,F), holds(val(P,PV),1) : default_if(I,val(P,PV)); 
    not holds(val(P,PV),1) : default_if(I,neg_val(P,PV));
    holds(A,0) : default_after(I,A),action(A); 
    holds(val(P,PV),0) : default_after(I,val(P,PV));
    not holds(val(P,PV),0) : default_after(I,neg_val(P,PV)).

holds(F,1) :- static_law(I,F), holds(val(P,PV),1) : if(I,val(P,PV)); 
    not holds(val(P,PV),1) : if(I,neg_val(P,PV)); 
    not not holds(val(P,PV),1) : ifcons(I,val(P,PV)); 
    not holds(val(P,PV),1) : ifcons(I,neg_val(P,PV)).

holds(F,1) :- dynamic_law(I,F), holds(A,0) : after(I,A),action(A); 
    holds(val(P,PV),0) : after(I,val(P,PV)); 
    not holds(val(P,PV),0) : after(I,neg_val(P,PV)); 
    not not holds(val(P,PV),1) : difcons(I,val(P,PV)); 
    not holds(val(P,PV),1) : difcons(I,neg_val(P,PV)).

:- impossible(I,_), holds(val(P,PV),1) : impossible(I,val(P,PV)); 
    not holds(val(P,PV),1) : impossible(I,neg_val(P,PV)); 
    not not holds(val(P,PV),1) : impossible_ifcons(I,val(P,PV)); 
    not holds(val(P,PV),1) : impossible_ifcons(I,neg_val(P,PV)).

:- nonexecutable(I,_), holds(A,0) : nonexecutable(I,A),action(A); 
    holds(val(P,PV),0) : nonexecutable(I,val(P,PV)); 
    not holds(val(P,PV),0) : nonexecutable(I,neg_val(P,PV)); 
    not not holds(val(P,PV),1) : nonexecutable_ifcons(I,val(P,PV)); 
    not holds(val(P,PV),1) : nonexecutable_ifcons(I,neg_val(P,PV)).

:- fluent(X), not 1{ holds(val(X,A),1) }1. 

:- fluent(X), holds(val(X,Y),1), holds(neg_val(X,Y),1).

