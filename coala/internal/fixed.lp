#const k=10.

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
:- fluent(X), not 1{ holds(val(X,A),0):domain(X,A) }1. 
:- fluent(X), holds(val(X,Y),0), holds(neg_val(X,Y),0).
:- holds(_false,0).

#program initialbase.
holds(F,0) :- initially(F).
1{holds(val(F,B),0) : domain(F,B)}1 :- fluent(F), not defined_fluent(F).

%{holds(val(F,FV),0)} :- default(val(F,FV)), fluent(F).
%{holds(val(F,FV),0)} :- default(I,val(F,FV)), fluent(F), 
%    holds(val(P,PV),0) : if(I,val(P,PV)); 
%    not holds(val(P,PV),0) : if(I,neg_val(P,PV));
%    not after(I,_).

holds(F,0) :- static_law(I), head(I,F), holds(val(P,PV),0) : if(I,val(P,PV)); 
    not holds(val(P,PV),0) : if(I,neg_val(P,PV)); 
    not not holds(val(P,PV),0) : ifcons(I,val(P,PV)); 
    not holds(val(P,PV),0) : ifcons(I,neg_val(P,PV)).

:- impossible(I,_), holds(val(P,PV),0) : impossible(I,val(P,PV)); 
    not holds(val(P,PV),0) : impossible(I,neg_val(P,PV)); 
    not not holds(val(P,PV),0) : ifcons(I,val(P,PV)); 
    not holds(val(P,PV),0) : ifcons(I,neg_val(P,PV)).

:- fluent(X), not 1{ holds(val(X,A),0):domain(X,A) }1. 
:- fluent(X), holds(val(X,Y),0), holds(neg_val(X,Y),0).
:- holds(_false,0).

#program base.
step(1..k).
fluent(X) :- defined_fluent(X).
{occurs(Ac,T-1) : action(Ac)} :- step(T).
holds(Ac,t) :- occurs(Ac,t).
occurs(Ac,t) :- holds(Ac,t), action(Ac).

{holds(val(F,V),T)} :- inertial(F), holds(val(F,V),T-1), step(T).
{holds(F,T)} :- default(F), step(T).
{holds(F,T)} :- default(I,F), holds(val(P,PV),T) : if(I,val(P,PV)); 
    not holds(val(P,PV),T) : if(I,neg_val(P,PV));
    occurs(A,T-1) : after(I,A),action(A); 
    holds(val(P,PV),T-1) : after(I,val(P,PV));
    not holds(val(P,PV),T-1) : after(I,neg_val(P,PV)); step(T).

holds(F,T) :- static_law(I), head(I,F), holds(val(P,PV),T) : if(I,val(P,PV)); 
    not holds(val(P,PV),T) : if(I,neg_val(P,PV)); 
    not not holds(val(P,PV),T) : ifcons(I,val(P,PV)); 
    not holds(val(P,PV),T) : ifcons(I,neg_val(P,PV)); step(T).
holds(F,T) :- dynamic_law(I), head(I,F), occurs(A,T-1) : after(I,A),action(A); 
    holds(val(P,PV),T-1) : after(I,val(P,PV)); 
    not holds(val(P,PV),T-1) : after(I,neg_val(P,PV)); 
    not not holds(val(P,PV),T) : ifcons(I,val(P,PV)); 
    not holds(val(P,PV),T) : ifcons(I,neg_val(P,PV)); step(T).

:- impossible(I,_), holds(val(P,PV),T) : impossible(I,val(P,PV)); 
    not holds(val(P,PV),T) : impossible(I,neg_val(P,PV));
    not not holds(val(P,PV),T) : ifcons(I,val(P,PV)); 
    not holds(val(P,PV),T) : ifcons(I,neg_val(P,PV)); step(T).
:- nonexecutable(I,_), occurs(A,T-1) : nonexecutable(I,A),action(A);
    holds(val(P,PV),T-1) : nonexecutable(I,val(P,PV)); 
    not holds(val(P,PV),T-1) : nonexecutable(I,neg_val(P,PV)); 
    not not holds(val(P,PV),T) : ifcons(I,val(P,PV)); 
    not holds(val(P,PV),T) : ifcons(I,neg_val(P,PV));step(T).

:- fluent(X), not 1{ holds(val(X,A),T):domain(X,A) }1, step(T). 
:- fluent(X), holds(val(X,Y),T), holds(neg_val(X,Y),T), step(T).
:- holds(_false,T), step(T).

#program query.
:- not holds(val(G,GV),k), finally(val(G,GV)).
:- holds(val(G,GV),k), finally(neg_val(G,GV)).

#program utility.
#maximize {1,G : holds(G,k), finally(G); -1,G : holds(val(G,X),k), finally(neg_val(G,X))}.
