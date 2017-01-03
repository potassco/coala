dir(left;right).
office(1..3).

nextOffice(X,X+1) :- office(X), office(X+1).

rightmostOffice(X) :- office(X), not office(X+1).
leftmostOffice(X) :-  office(X), not office(X-1).

action(act(go(D))) :- dir(D).
fluent(at(X)) :- office(X).
domain(at(X),true) :- office(X). domain(at(X),false) :- office(X). 


dynamic_law(law(1,X,X1)) :- nextOffice(X,X1).
head(law(1,X,X1),val(at(X),false)) :- nextOffice(X,X1).
head(law(1,X,X1),val(at(X1),true)) :- nextOffice(X,X1).
after(law(1,X,X1),act(go(right))) :- nextOffice(X,X1).
after(law(1,X,X1),val(at(X),true)) :- nextOffice(X,X1).
dynamic_law(law(2,X,X1)) :- nextOffice(X1,X).
head(law(2,X,X1),val(at(X),false)) :- nextOffice(X1,X).
head(law(2,X,X1),val(at(X1),true)) :- nextOffice(X1,X).
after(law(2,X,X1),act(go(left))) :- nextOffice(X1,X).
after(law(2,X,X1),val(at(X),true)) :- nextOffice(X1,X).

static_law(law(3,X,X1)) :- fluent(at(X)),fluent(at(X1)),X!=X1,office(_X).
head(law(3,X,X1),val(at(_X),true)) :- fluent(at(X)),fluent(at(X1)),X!=X1,office(_X).
head(law(3,X,X1),val(at(_X),false)) :- fluent(at(X)),fluent(at(X1)),X!=X1,office(_X).
if(law(3,X,X1),val(at(X),true)) :- fluent(at(X)),fluent(at(X1)),X!=X1,office(_X).
if(law(3,X,X1),val(at(X1),true)) :- fluent(at(X)),fluent(at(X1)),X!=X1,office(_X).
dynamic_law(law(4)) :- office(_X).
head(law(4),val(at(_X),true)) :- office(_X).
head(law(4),val(at(_X),false)) :- office(_X).
after(law(4),act(go(left))) :- office(_X).
after(law(4),act(go(right))) :- office(_X).
dynamic_law(law(5,X)) :- leftmostOffice(X),office(_X).
head(law(5,X),val(at(_X),true)) :- leftmostOffice(X),office(_X).
head(law(5,X),val(at(_X),false)) :- leftmostOffice(X),office(_X).
after(law(5,X),act(go(left))) :- leftmostOffice(X),office(_X).
after(law(5,X),val(at(X),true)) :- leftmostOffice(X),office(_X).
dynamic_law(law(6,X)) :- rightmostOffice(X),office(_X).
head(law(6,X),val(at(_X),true)) :- rightmostOffice(X),office(_X).
head(law(6,X),val(at(_X),false)) :- rightmostOffice(X),office(_X).
after(law(6,X),act(go(right))) :- rightmostOffice(X),office(_X).
after(law(6,X),val(at(X),true)) :- rightmostOffice(X),office(_X).
dynamic_law(law(7,X,_DOMAIN_ELEMENT)) :- office(X),domain(at(X),_DOMAIN_ELEMENT).
head(law(7,X,_DOMAIN_ELEMENT),val(at(X),_DOMAIN_ELEMENT)) :- office(X),domain(at(X),_DOMAIN_ELEMENT).
after(law(7,X,_DOMAIN_ELEMENT),val(at(X),_DOMAIN_ELEMENT)) :- office(X),domain(at(X),_DOMAIN_ELEMENT).
ifcons(law(7,X,_DOMAIN_ELEMENT),val(at(X),_DOMAIN_ELEMENT)) :- office(X),domain(at(X),_DOMAIN_ELEMENT).

initially(val(at(1),true)).
initially(val(at(X),false)) :- office(X),X!=1.
goal(val(at(3),true)).

#show holds/2.
#show occurs/2.
