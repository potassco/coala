action(go(D)) :- dir(D).
action(pickup(From,To)) :- office(From),office(To).
action(deliver(From,To)) :- office(From),office(To).
fluent(at(X)) :- office(X).
fluent(request(X,Y)) :- office(X),office(Y).
fluent(holding(X,Y)) :- office(X),office(Y).
fluent(fullbags(X)) :- capacity(X).
fluent(tasksremaining).
fluent(wentup).
fluent(wentdown).
fluent(somethingabove).
fluent(somethingbelow).
static(wentup).
static(wentdown).
static(somethingabove).
static(somethingbelow).
domain(fullbags(X),true) :- capacity(X). domain(fullbags(X),false) :- capacity(X). 
domain(holding(X,Y),true) :- office(X),office(Y). domain(holding(X,Y),false) :- office(X),office(Y). 
domain(request(X,Y),true) :- office(X),office(Y). domain(request(X,Y),false) :- office(X),office(Y). 
domain(at(X),true) :- office(X). domain(at(X),false) :- office(X). 
domain(somethingabove,true). domain(somethingabove,false). 
domain(somethingbelow,true). domain(somethingbelow,false). 
domain(tasksremaining,true). domain(tasksremaining,false). 
domain(wentup,true). domain(wentup,false). 
domain(wentdown,true). domain(wentdown,false). 

static_law(law(1,Y,X)) :- office(X),office(Y).
head(law(1,Y,X),val(tasksremaining,true)) :- office(X),office(Y).
if(law(1,Y,X),val(request(X,Y),true)) :- office(X),office(Y).
static_law(law(2,Y,X)) :- office(X),office(Y).
head(law(2,Y,X),val(tasksremaining,true)) :- office(X),office(Y).
if(law(2,Y,X),val(holding(X,Y),true)) :- office(X),office(Y).
static_law(law(3,X,From,To)) :- office(X),office(From),office(To),officeorder(X,From).
head(law(3,X,From,To),val(somethingabove,true)) :- office(X),office(From),office(To),officeorder(X,From).
if(law(3,X,From,To),val(at(X),true)) :- office(X),office(From),office(To),officeorder(X,From).
if(law(3,X,From,To),val(request(From,To),true)) :- office(X),office(From),office(To),officeorder(X,From).
static_law(law(4,X,From,To)) :- office(X),office(From),office(To),officeorder(X,To).
head(law(4,X,From,To),val(somethingabove,true)) :- office(X),office(From),office(To),officeorder(X,To).
if(law(4,X,From,To),val(at(X),true)) :- office(X),office(From),office(To),officeorder(X,To).
if(law(4,X,From,To),val(holding(From,To),true)) :- office(X),office(From),office(To),officeorder(X,To).
static_law(law(5,X,From,To)) :- office(X),office(From),office(To),officeorder(X,From).
head(law(5,X,From,To),val(somethingbelow,true)) :- office(X),office(From),office(To),officeorder(X,From).
if(law(5,X,From,To),val(at(X),true)) :- office(X),office(From),office(To),officeorder(X,From).
if(law(5,X,From,To),val(request(From,To),true)) :- office(X),office(From),office(To),officeorder(X,From).
static_law(law(6,X,From,To)) :- office(X),office(From),office(To),officeorder(X,To).
head(law(6,X,From,To),val(somethingbelow,true)) :- office(X),office(From),office(To),officeorder(X,To).
if(law(6,X,From,To),val(at(X),true)) :- office(X),office(From),office(To),officeorder(X,To).
if(law(6,X,From,To),val(holding(From,To),true)) :- office(X),office(From),office(To),officeorder(X,To).

dynamic_law(law(7,X,X1)) :- officeplusone(X,X1).
head(law(7,X,X1),val(at(X1),true)) :- officeplusone(X,X1).
after(law(7,X,X1),go(up)) :- officeplusone(X,X1).
after(law(7,X,X1),val(at(X),true)) :- officeplusone(X,X1).
dynamic_law(law(8,X,X1)) :- officeplusone(X1,X).
head(law(8,X,X1),val(at(X1),true)) :- officeplusone(X1,X).
after(law(8,X,X1),go(down)) :- officeplusone(X1,X).
after(law(8,X,X1),val(at(X),true)) :- officeplusone(X1,X).
dynamic_law(law(9,X,D)) :- dir(D),office(X).
head(law(9,X,D),val(at(X),false)) :- dir(D),office(X).
after(law(9,X,D),go(D)) :- dir(D),office(X).
after(law(9,X,D),val(at(X),true)) :- dir(D),office(X).
dynamic_law(law(10,To,From)) :- office(From),office(To).
head(law(10,To,From),val(holding(From,To),true)) :- office(From),office(To).
after(law(10,To,From),pickup(From,To)) :- office(From),office(To).
after(law(10,To,From),val(request(From,To),true)) :- office(From),office(To).
dynamic_law(law(11,To,From)) :- office(From),office(To).
head(law(11,To,From),val(request(From,To),false)) :- office(From),office(To).
after(law(11,To,From),pickup(From,To)) :- office(From),office(To).
after(law(11,To,From),val(request(From,To),true)) :- office(From),office(To).
dynamic_law(law(12,To,From)) :- office(From),office(To).
head(law(12,To,From),val(holding(From,To),false)) :- office(From),office(To).
after(law(12,To,From),deliver(From,To)) :- office(From),office(To).
after(law(12,To,From),val(holding(From,To),true)) :- office(From),office(To).
dynamic_law(law(13,To,F2,From,F1)) :- capacityplusone(F1,F2),office(From),office(To).
head(law(13,To,F2,From,F1),val(fullbags(F2),true)) :- capacityplusone(F1,F2),office(From),office(To).
after(law(13,To,F2,From,F1),pickup(From,To)) :- capacityplusone(F1,F2),office(From),office(To).
after(law(13,To,F2,From,F1),val(fullbags(F1),true)) :- capacityplusone(F1,F2),office(From),office(To).
dynamic_law(law(14,To,F2,From,F1)) :- capacityplusone(F2,F1),office(From),office(To).
head(law(14,To,F2,From,F1),val(fullbags(F2),true)) :- capacityplusone(F2,F1),office(From),office(To).
after(law(14,To,F2,From,F1),deliver(From,To)) :- capacityplusone(F2,F1),office(From),office(To).
after(law(14,To,F2,From,F1),val(fullbags(F1),true)) :- capacityplusone(F2,F1),office(From),office(To).
dynamic_law(law(15,To,From,F)) :- capacity(F),office(From),office(To).
head(law(15,To,From,F),val(fullbags(F),false)) :- capacity(F),office(From),office(To).
after(law(15,To,From,F),deliver(From,To)) :- capacity(F),office(From),office(To).
after(law(15,To,From,F),val(fullbags(F),true)) :- capacity(F),office(From),office(To).
dynamic_law(law(16,To,From,F)) :- capacity(F),office(From),office(To).
head(law(16,To,From,F),val(fullbags(F),false)) :- capacity(F),office(From),office(To).
after(law(16,To,From,F),pickup(From,To)) :- capacity(F),office(From),office(To).
after(law(16,To,From,F),val(fullbags(F),true)) :- capacity(F),office(From),office(To).
dynamic_law(law(17)).
head(law(17),val(wentup,true)).
after(law(17),go(up)).
dynamic_law(law(18)).
head(law(18),val(wentdown,true)).
after(law(18),go(down)).

nonexecutable(law(19,X),go(up)) :- notofficeplusone(X).
nonexecutable(law(19,X),val(at(X),true)) :- notofficeplusone(X).
nonexecutable(law(20,X),go(down)) :- notofficeminusone(X).
nonexecutable(law(20,X),val(at(X),true)) :- notofficeminusone(X).
nonexecutable(law(21,To,From,X),pickup(From,To)) :- office(From),office(To),notcapacityplusone(X).
nonexecutable(law(21,To,From,X),val(at(From),true)) :- office(From),office(To),notcapacityplusone(X).
nonexecutable(law(21,To,From,X),val(request(From,To),true)) :- office(From),office(To),notcapacityplusone(X).
nonexecutable(law(21,To,From,X),val(fullbags(X),true)) :- office(From),office(To),notcapacityplusone(X).
nonexecutable(law(22,To,From),deliver(From,To)) :- office(From),office(To).
nonexecutable(law(22,To,From),val(at(To),false)) :- office(From),office(To).
nonexecutable(law(23,To,From),deliver(From,To)) :- office(From),office(To).
nonexecutable(law(23,To,From),val(holding(From,To),false)) :- office(From),office(To).
nonexecutable(law(24),go(up)).
nonexecutable(law(24),val(wentdown,true)).
nonexecutable(law(25),go(down)).
nonexecutable(law(25),val(wentup,true)).
nonexecutable(law(26,Y,X,Dir),go(Dir)) :- office(X),office(Y),dir(Dir).
nonexecutable(law(26,Y,X,Dir),val(at(Y),true)) :- office(X),office(Y),dir(Dir).
nonexecutable(law(26,Y,X,Dir),val(holding(X,Y),true)) :- office(X),office(Y),dir(Dir).
nonexecutable(law(27,Y,X,Dir),go(Dir)) :- office(X),office(Y),dir(Dir).
nonexecutable(law(27,Y,X,Dir),val(at(X),true)) :- office(X),office(Y),dir(Dir).
nonexecutable(law(27,Y,X,Dir),val(request(X,Y),true)) :- office(X),office(Y),dir(Dir).
nonexecutable(law(27,Y,X,Dir),val(fullbags(0),true)) :- office(X),office(Y),dir(Dir).
nonexecutable(law(28),go(up)).
nonexecutable(law(28),val(somethingabove,false)).
nonexecutable(law(29),go(down)).
nonexecutable(law(29),val(somethingbelow,false)).
nonexecutable(law(30,X,Later,Earlier),pickup(X,Later)) :- office(X),office(Earlier),office(Later),officeorder(Earlier,Later).
nonexecutable(law(30,X,Later,Earlier),val(at(X),true)) :- office(X),office(Earlier),office(Later),officeorder(Earlier,Later).
nonexecutable(law(30,X,Later,Earlier),val(request(X,Earlier),true)) :- office(X),office(Earlier),office(Later),officeorder(Earlier,Later).
nonexecutable(law(30,X,Later,Earlier),val(request(X,Later),true)) :- office(X),office(Earlier),office(Later),officeorder(Earlier,Later).
default(val(tasksremaining,false)).
default(val(wentup,false)).
default(val(wentdown,false)).
default(val(somethingabove,false)).
default(val(somethingbelow,false)).
inertial(at(X)) :- office(X).
inertial(request(X,Y)) :- office(X),office(Y).
inertial(holding(X,Y)) :- office(X),office(Y).
inertial(fullbags(X)) :- capacity(X).

initially(val(at(1),true)).
initially(val(at(X),false)) :- office(Y,X).
initially(val(fullbags(0),true)).
initially(val(fullbags(X),false)) :- capacityplusone(X).
initially(val(request(X,Y),true)) :- initialrequest(X,Y).
initially(val(request(X,Y),false)) :- office(X),office(Y),notinitialrequest(X,Y).
goal(val(tasksremaining,false)).

