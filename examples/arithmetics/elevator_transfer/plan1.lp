
#show holds/2.
#show occurs/2. 
#show.

holds(val(crash,false),0).
&sum{val(speed,0)}=0.
&sum{val(floor,0)}=0.
&sum{val(at(1),0)}=0.
&sum{val(at(2),0)}=10.
&sum{val(at(3),0)}=100.
&sum{val(at(4),0)}=1000.
&sum{val(at(5),0)}= -5.

&sum{val(at(1),6)}= 6. % Goals for person 1.
&sum{val(floor,6)}= 7. % Goal for elevator

holds(val(traveling(X),false),0) :- person(X).

% coala *.bc | clingcon - *.lp ../../encodings/arithmetic.lp 0 -c k=6 | outputformatclingo
