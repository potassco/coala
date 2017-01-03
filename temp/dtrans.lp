
fluent(X) :- defined_fluent(X).

1{holds(val(F,B),0) : domain(F,B)}1 :- fluent(F), not defined_fluent(F).
{holds(val(F,FV),0)} :- default(val(F,FV)), fluent(F).
{holds(val(F,FV),0)} :- default(I,val(F,FV)), fluent(F), 
    holds(val(P,PV),0) : if(I,val(P,PV));
    not after(I,_).

% 1{holds(val(F,B),0) : domain(F,B)}1 :- fluent(F). % Without static laws

holds(F,0) :- static_law(I), head(I,F), holds(val(P,VP),0) : if(I,val(P,VP));
    not not holds(val(P,VP),0) : ifcons(I,val(P,VP)).

:- fluent(X), not 1{ holds(val(X,A),0) }1.


fluent(X) :- defined_fluent(X).

{occurs(Ac,0) : action(Ac)}.
holds(Ac,0) :- occurs(Ac,0).
occurs(Ac,0) :- holds(Ac,0), action(Ac).

{holds(F,1)} :- default(F).
{holds(F,t)} :- default(I,F), holds(val(P,PV),1) : if(I,val(P,PV)); 
    holds(A,0) : after(I,A),action(A); 
    holds(val(P,PV),0) : after(I,val(P,PV)).

holds(F,1) :- static_law(I), head(I,F), 
    holds(val(P,PV),1) : if(I,val(P,PV));
    not not holds(val(P,PV),1) : ifcons(I,val(P,PV)).

holds(F,1) :- dynamic_law(I), head(I,F), 
    holds(A,0) : after(I,A),action(A); 
    holds(val(P,PV),0) : after(I,val(P,PV));
    not not holds(val(P,PV),1) : ifcons(I,val(P,PV)).

:- fluent(X), not 1{ holds(val(X,A),1) }1. 

