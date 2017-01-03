%#const k=3.
%step(0..3).

%#show holds/2. 
#show occurs/2. 
%#show.

%holds(val(bounce,false),0).
holds(val(fall,true),0).
&sum{val(height,0)}=100. %10 m
&sum{val(velocity,0)}=150. %15 m/s

% coala *.bc | clingcon - plan1.lp ../../encodings/arithmetic.lp 0 -c k=3 | outputformatclingo
