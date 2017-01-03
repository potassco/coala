
fluent(X) :- defined_fluent(X).

#program staticbase.

1{holds(val(F,B),0) : domain(F,B)}1 :- fluent(F), not defined_fluent(F).
{holds(val(F,FV),0)} :- default(val(F,FV)), fluent(F).
{holds(val(F,FV),0)} :- default(I,val(F,FV)), fluent(F), 
    holds(val(P,PV),0) : default_if(I,val(P,PV)); 
    not holds(val(P,PV),0) : default_if(I,neg_val(P,PV));
    not default_after(I,_).

holds(F,0) :- static_law(I,F), holds(val(P,PV),0) : if(I,val(P,PV)); 
    not holds(val(P,PV),0) : if(I,neg_val(P,PV)); 
    not not holds(val(P,PV),0) : ifcons(I,val(P,PV)); 
    not holds(val(P,PV),0) : ifcons(I,neg_val(P,PV)).
:- impossible(I,_), holds(val(P,PV),0) : impossible(I,val(P,PV)); 
    not holds(val(P,PV),0) : impossible(I,neg_val(P,PV)); 
    not not holds(val(P,PV),0) : impossible_ifcons(I,val(P,PV)); 
    not holds(val(P,PV),0) : impossible_ifcons(I,neg_val(P,PV)).
:- fluent(X), not 1{ holds(val(X,A),0) }1. 
:- fluent(X), holds(val(X,Y),0), holds(neg_val(X,Y),0).

#program initialbase.
holds(F,0) :- initially(F).

{holds(val(F,FV),0)} :- default(val(F,FV)), fluent(F).
{holds(val(F,FV),0)} :- default(I,val(F,FV)), fluent(F), 
    holds(val(P,PV),0) : if(I,val(P,PV)); 
    not holds(val(P,PV),0) : if(I,neg_val(P,PV));
    not after(I,_).

holds(F,0) :- static_law(I,F), holds(val(P,PV),0) : if(I,val(P,PV)); 
    not holds(val(P,PV),0) : if(I,neg_val(P,PV)); 
    not not holds(val(P,PV),0) : ifcons(I,val(P,PV)); 
    not holds(val(P,PV),0) : ifcons(I,neg_val(P,PV)).

:- impossible(I,_), holds(val(P,PV),0) : impossible(I,val(P,PV)); 
    not holds(val(P,PV),0) : impossible(I,neg_val(P,PV)); 
    not not holds(val(P,PV),0) : impossible_ifcons(I,val(P,PV)); 
    not holds(val(P,PV),0) : impossible_ifcons(I,neg_val(P,PV)).

:- fluent(X), not 1{ holds(val(X,A),0) }1. 
:- fluent(X), holds(val(X,Y),0), holds(neg_val(X,Y),0).

#program transition(t).
{occurs(Ac,t-1) : action(Ac)}.

{holds(val(F,V),t)} :- inertial(F), holds(val(F,V),t-1).
{holds(F,t)} :- default(F).
{holds(F,t)} :- default(I,F), holds(val(P,PV),t) : default_if(I,val(P,PV)); 
    not holds(val(P,PV),t) : default_if(I,neg_val(P,PV));
    occurs(A,t-1) : default_after(I,A),action(A); 
    holds(val(P,PV),t-1) : default_after(I,val(P,PV));
    not holds(val(P,PV),t-1) : default_after(I,neg_val(P,PV)).

holds(F,t) :- static_law(I,F), holds(val(P,PV),t) : if(I,val(P,PV)); 
    not holds(val(P,PV),t) : if(I,neg_val(P,PV)); 
    not not holds(val(P,PV),t) : ifcons(I,val(P,PV)); 
    not holds(val(P,PV),t) : ifcons(I,neg_val(P,PV)).
holds(F,t) :- dynamic_law(I,F), occurs(A,t-1) : after(I,A),action(A); 
    holds(val(P,PV),t-1) : after(I,val(P,PV)); 
    not holds(val(P,PV),t-1) : after(I,neg_val(P,PV)); 
    not not holds(val(P,PV),t) : difcons(I,val(P,PV)); 
    not holds(val(P,PV),t) : difcons(I,neg_val(P,PV)).

:- impossible(I,_), holds(val(P,PV),t) : impossible(I,val(P,PV)); 
    not holds(val(P,PV),t) : impossible(I,neg_val(P,PV));
    not not holds(val(P,PV),t) : impossible_ifcons(I,val(P,PV)); 
    not holds(val(P,PV),t) : impossible_ifcons(I,neg_val(P,PV)).
:- nonexecutable(I,_), occurs(A,t-1) : nonexecutable(I,A),action(A);
    holds(val(P,PV),t-1) : nonexecutable(I,val(P,PV)); 
    not holds(val(P,PV),t-1) : nonexecutable(I,neg_val(P,PV)); 
    not not holds(val(P,PV),t) : nonexecutable_ifcons(I,val(P,PV)); 
    not holds(val(P,PV),t) : nonexecutable_ifcons(I,neg_val(P,PV)).

:- fluent(X), not 1{ holds(val(X,A),t) }1. 
:- fluent(X), holds(val(X,Y),t), holds(neg_val(X,Y),t).

#program query(t).
#external query(t).
:- not holds(val(G,GV),t), goal(val(G,GV)), query(t).
:- holds(val(G,GV),t), goal(neg_val(G,GV)), query(t).

#program utility(t).
#external utility(t).
#maximize {1,G : holds(G,t), goal(G), utility(t); -1,G : holds(val(G,X),t), goal(neg_val(G,X)), utility(t)}.
