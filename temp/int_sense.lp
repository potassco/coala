action(act(increase)).
integer(x).
integer_domain(x,5,100).
integer(y).
integer_domain(y,1,10).

dynamic_law(law(3)).
head(law(3),_arithmetic(law(1))).
after(law(3),act(increase)).

inertial(x).
inertial(y).

arithmetic_assignment_dynamic(law(1)).
arithmetic_law(law(1),eq).
arithmetic_head(law(1),x,1).
arithmetic(law(1),x,-1).
arithmetic(law(1),y,-1).
arithmetic(law(1),0).

initially(val(x,10)).
initially(val(y,5)).

