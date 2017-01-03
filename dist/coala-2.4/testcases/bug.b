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

<action> start.


<fluent> result(sat).
<fluent> result(unsat).
<fluent> result(unknown).

<fluent> grounded(0).
<fluent> grounded(H) <where> solvingstep(H).
<fluent> possible(A) <where> <action> A.

possible(start) <if> -result(sat), -result(unsat), -result(unknown).

start <causes> grounded(0).


<nonexecutable> A <if> -possible(A) <where> <action> A.
