%%% action description
% start       - setup the solver & controller
% query(H)    - test if there is a plan with length H
% publish     - publish the solution found by the solver
% exit        - exit the solver
%%%
% note: m is an INT chosen at program start
%%%
% actions = {start, query(0..m), publish, exit}
% fluents = {result(sat), result(unsat), horizon(0..m), done, ready}
%%%

succ(0,1).
succ(1,2).
succ(2,3).
succ(3,4).
succ(4,5).
succ(5,6).
succ(6,7).
succ(7,8).

<action> start.
<action> ground(S) <where> dom(S).
<action> query(S) <where> dom(S).
<action> commit(S) <where> dom(S).

<fluent> result(sat).
<fluent> result(unsat).
<fluent> result(unknown).

<fluent> grounded(0).
<fluent> grounded(S) <where> dom(S).
<fluent> horizon(S) <where> dom(S).
<fluent> commited(S) <where> dom(S).
<fluent> possible(A) <where> <action> A.

possible(start) <if> -result(sat), -result(unsat), -result(unknown).
%possible(ground(S1)) <if> result(unsat), grounded(S2), -grounded(S1) <where> dom(S1), dom(S2), succ(S2,S1).
%possible(query(S1)) <if> result(unsat), horizon(S2), grounded(S1) <where> dom(S1), dom(S2), succ(S2,S1).

start <causes> grounded(0).
ground(S) <causes> grounded(S) <where> dom(S).
query(S) <causes> horizon(S) <where> dom(S).
query(S1) <causes> -horizon(S2) <if> horizon(S2) <where> dom(S1), dom(S2).

<nonexecutable> start <if> -possible(start).
<nonexecutable> ground(S) <if> -possible(ground(S)) <where> dom(S).
<nonexecutable> query(S) <if> -possible(query(S)) <where> dom(S).
<nonexecutable> commit(S) <if> -possible(commit(S)) <where> dom(S).
