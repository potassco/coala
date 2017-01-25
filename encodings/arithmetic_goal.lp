
% Include finally statements
%:- finally(val(V,X)), integer(V), not &sum{val(V,k)} = X.
:- not holds(val(G,GV),k), finally(val(G,GV)).
:- not holds(_arithmetic(L),k), finally(_arithmetic(L)).
