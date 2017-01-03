%walker instance

#const w = 8.
#const h = 8.

node(X,Y) :- X = 0..w, Y = 0..h.

wall(0,Y) :- node(0, Y).
wall(X,0) :- node(X, 0).
wall(w,Y) :- node(w, Y).
wall(X,h) :- node(X, h).

wall(X,Y) :- obstacle(X,Y).

yp1(Y1,Y) :- Y1 = Y + 1, node(_, Y1), node(_, Y).
xp1(X1,X) :- X1 = X + 1, node(X1, _), node(X, _).


%obstacles
obstacle(7,4).
obstacle(6,1).

%

%to print values with #show
at(X, Y, T) :- holds(val(at(X, Y), true), T).
blocked(X,Y,T) :- holds(val(blocked(X,Y), true), T).


init(at(4,4)).

#show occurs/2.
#show at/3.
#show wall/2.
#show blocked/3.

