
holds(F,0) :- initially(F).

fluent(X) :- defined_fluent(X).

{holds(val(F,FV),0)} :- default(val(F,FV)), fluent(F).
{holds(val(F,FV),0)} :- default(I,val(F,FV)), fluent(F), 
    holds(val(P,PV),0) : if(I,val(P,PV)); 
    not holds(val(P,PV),0) : if(I,neg_val(P,PV));
    not after(I,_).

% 1{holds(val(F,B),0) : domain(F,B)}1 :- fluent(F). % Without static laws

holds(F,0) :- static_law(I), head(I,F), holds(val(P,VP),0) : if(I,val(P,VP)); 
    not holds(val(P,VP),0) : if(I,neg_val(P,VP)); 
    not not holds(val(P,VP),0) : ifcons(I,val(P,VP)); 
    not holds(val(P,VP),0) : ifcons(I,neg_val(P,VP)).

error(i,I,0) :- impossible(I,_), holds(val(P,PV),0) : impossible(I,val(P,PV)); 
    not holds(val(P,PV),0) : impossible(I,neg_val(P,PV)); 
    not not holds(val(P,PV),0) : ifcons(I,val(P,PV)); 
    not holds(val(P,PV),0) : ifcons(I,neg_val(P,PV)).

error(f,X,0) :- fluent(X), not 1{ holds(val(X,A),0):domain(X,A) }1.

error(nf,X,0) :- fluent(X), holds(val(X,Y),0), holds(neg_val(X,Y),0).

#minimize {1,A,B,C:error(A,B,C)}.
#show error/3.
