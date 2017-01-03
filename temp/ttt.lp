%---
action(drink(cup(water))).
action(medicate).
fluent(infected).
fluent(infected).
fluent(hydrated).
fluent(hydrated).
fluent(hydrated).
fluent(dead).
fluent(dead).
domain(hydrated,tr). 
domain(hydrated,fa). 
domain(hydrated,dooo). 
domain(infected,tr). 
domain(infected,fa). 
domain(dead,tr). 
domain(dead,fa). 


dynamic_law(law(1),val(hydrated,tr)).
after(law(1),drink(cup(water))).

dynamic_law(law(2),val(dead,tr)).
after(law(2),medicate).
after(law(2),neg_val(hydrated,tr)).
after(law(2),val(infected,tr)).

dynamic_law(law(3),val(infected,fa)).
after(law(3),medicate).
difcons(law(3),val(hydrated,tr)).

nonexecutable(law(4),drink(cup(water))).
nonexecutable(law(4),val(dead,tr)).
nonexecutable(law(5),val(medicate,tr)).
nonexecutable(law(5),val(dead,tr)).
inertial(dead).
inertial(hydrated).
inertial(infected).

initially(val(infected,tr)).
initially(val(hydrated,fa)).
initially(val(dead,fa)).
goal(neg_val(infected,tr)).
goal(neg_val(dead,tr)).

%
holds(F,0) :- initially(F).

holds(F,0) :- static_law(I,F), holds(val(P,VP),0) : if(I,val(P,VP)); not holds(val(P,VP),0) : if(I,neg_val(P,VP)); not not holds(val(P,VP),0) : ifcons(I,val(P,VP)); not holds(val(P,VP),0) : ifcons(I,neg_val(P,VP)).

:- impossible(I,_), holds(P,0) : impossible(I,P).

:- fluent(X), not 1{ holds(val(X,A),0) }1.

:- fluent(X), holds(val(X,Y),0), holds(neg_val(X,Y),0).

%
step(1..2).

{do(Ac,STEP-1) : action(Ac)} :- step(STEP).
holds(Ac,STEP-1) :- do(Ac,STEP-1), step(STEP).

{holds(val(F,V),STEP)} :- inertial(F), holds(val(F,V),STEP-1), step(STEP).

{holds(val(F,FV),STEP)} :- default(val(F,FV)); step(STEP).

holds(F,STEP) :- static_law(I,F), holds(val(P,PV),STEP) : if(I,val(P,PV)); not holds(val(P,PV),STEP) : if(I,neg_val(P,PV)); not not holds(val(P,PV),STEP) : ifcons(I,val(P,PV)); not holds(val(P,PV),STEP) : ifcons(I,neg_val(P,PV)); step(STEP).

holds(F,STEP) :- dynamic_law(I,F), holds(A,STEP-1) : after(I,A),action(A);holds(val(P,PV),STEP-1) : after(I,val(P,PV)); not holds(val(P,PV),STEP-1) : after(I,neg_val(P,PV)); not not holds(val(P,PV),STEP) : difcons(I,val(P,PV)); not holds(val(P,PV),STEP) : difcons(I,neg_val(P,PV)); step(STEP).

:- impossible(I,_), holds(val(P,PV),STEP) : impossible(I,val(P,PV)); not holds(val(P,PV),STEP) : impossible(I,neg_val(P,PV)); step(STEP).
:- nonexecutable(I,_), holds(val(P,PV),STEP-1) : nonexecutable(I,val(P,PV)); not holds(val(P,PV),STEP-1) : nonexecutable(I,neg_val(P,PV)); holds(val(P,PV),STEP) : nonexecutable_if(I,val(P,PV)); not holds(val(P,PV),STEP) : nonexecutable_if(I,neg_val(P,PV)); step(STEP).

:- fluent(X), not 1{ holds(val(X,A),STEP) }1, step(STEP). 

:- fluent(X), holds(val(X,Y),STEP), holds(neg_val(X,Y),STEP), step(STEP).

#show holds/2.
%#show do/2.
