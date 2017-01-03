dir(left;right).
office(1..3).

nextOffice(X,X+1) :- office(X), office(X+1).

rightmostOffice(X) :- office(X), not office(X+1).
leftmostOffice(X) :-  office(X), not office(X-1).

action(go(D)) :- dir(D).
fluent(at(X)) :- office(X).
domain(at(X),true) :- office(X). domain(at(X),false) :- office(X). 


dynamic_law(law(1,X,X1)) :- nextOffice(X,X1).
head(law(1,X,X1),val(at(X),false)) :- nextOffice(X,X1).
head(law(1,X,X1),val(at(X1),true)) :- nextOffice(X,X1).
after(law(1,X,X1),act(go(right),true)) :- nextOffice(X,X1).
after(law(1,X,X1),val(at(X),true)) :- nextOffice(X,X1).
dynamic_law(law(2,X,X1)) :- nextOffice(X1,X).
head(law(2,X,X1),val(at(X),false)) :- nextOffice(X1,X).
head(law(2,X,X1),val(at(X1),true)) :- nextOffice(X1,X).
after(law(2,X,X1),act(go(left),true)) :- nextOffice(X1,X).
after(law(2,X,X1),val(at(X),true)) :- nextOffice(X1,X).

impossible(law(3,X,X1),val(at(X),true)) :- fluent(at(X)),fluent(at(X1)),X!=X1.
impossible(law(3,X,X1),val(at(X1),true)) :- fluent(at(X)),fluent(at(X1)),X!=X1.
nonexecutable(law(4),act(go(left),true)).
nonexecutable(law(4),act(go(right),true)).
nonexecutable(law(5,X),act(go(left),true)) :- leftmostOffice(X).
nonexecutable(law(5,X),val(at(X),true)) :- leftmostOffice(X).
nonexecutable(law(6,X),act(go(right),true)) :- rightmostOffice(X).
nonexecutable(law(6,X),val(at(X),true)) :- rightmostOffice(X).
inertial(at(X)) :- office(X).

initially(val(at(1),true)).
initially(val(at(X),false)) :- office(X),X!=1.
goal(val(at(3),true)).
