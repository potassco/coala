{
#const steps =2.
start(0).
end(steps).
time_step(S..E) :- start(S), end(E).
next(X,X+1) :- time_step(X), time_step(X+1).
diff(X,Y) :- time_step(X), time_step(Y), X != Y.

save(current_horizon(S)) :- time_step(S).
save(current_time_step(S)) :- time_step(S).
save(done).
save(grounded(S)) :- time_step(S).
save(next_horizon(S)) :- time_step(S).
save(released_external(query(S))) :- time_step(S).
save(released_time_step(S)) :- time_step(S).
save(solved).

#external event(info,new_requests,0).
#external event(info,pending_actions,0).
#external event(info,pending_requests,0).
#external event(info,pending_messages,0).
#external event(info,result(sat),0).
#external event(info,result(unknown),0).
#external event(info,result(unsat),0).
#external event(save,F,0) : save(F).

holds(val(F,true),0) :- event(info,F,0).
holds(val(F,true),0) :- event(save,F,0).
%%%%%

do(controller,A,T) :- do(A,T).
}
