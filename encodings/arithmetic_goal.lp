
% Include goal statements
%:- goal(val(V,X)), integer(V), not &sum{val(V,k)} = X.
:- not holds(_arithmetic(L),k), goal(_arithmetic(L)).
