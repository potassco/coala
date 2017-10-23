#program base.
h(A,T) :- holds(A,T), action(A).
h(val(F,V),T) :- holds(val(F,V),T), domain(F,V).

