%% 3 sheep an three wolves shall cross a river in a boat
%% which carries at most 2 animals at once. 
%% On either side, the wolves may never outnumber the sheep
%% or the sheep will be eaten.
%
%:- sorts
%	int;
%	small_int;
%	big_int;
%	type.
%
%:- macros
%	NUM -> 120;
%	CAPACITY -> 4.
%
%:- objects
%	0..NUM :: int;
%	0..CAPACITY :: small_int;
%	NUM-CAPACITY..NUM :: big_int;
%	sheep, wolf :: type.

<asp>
#const numb=120.
type(sheep).type(wolf).
small_int(0..4).
</asp>


%:- constants
%	cross(small_int, small_int) :: exogenousAction;
%	here(type) :: inertialFluent(int);
%	boat_here :: inertialFluent.
action cross(I,J) where small_int(I), small_int(J).
fluent here(Type) : 0 .. numb where type(Type).
fluent boat_here.

%:- variables
%	SS, SS1, SW, SW1 :: small_int;
%	BS, BS1, BW, BW1 :: big_int;
%	HS :: int;
%	HW :: int;
%	N, N1 :: int.
%
%
%% don't cross with more sheep than still here
%nonexecutable cross(SS, SW) if boat_here & here(sheep)=SS1 where SS1 < SS.
nonexecutable cross(SS, SW) if boat_here, here(sheep) < SS where small_int(SS), small_int(SW).

%% don't cross with more wolves than still here
%nonexecutable cross(SS, SW) if boat_here & here(wolf)=SW1 where SW1 < SW.
nonexecutable cross(SS, SW) if boat_here, here(wolf) < SW where small_int(SS), small_int(SW).

%% don't cross when boat not here and more than n sheep
%nonexecutable cross(SS, SW) if -boat_here & here(sheep)=BS where SS + BS > NUM.
%%% We don't have such a maximal number anymore. This handled by the domain instead.

%% don't cross when boat not here and more than n wolves
%nonexecutable cross(SS, SW) if -boat_here & here(wolf)=BW where  SW + BW > NUM.  
%%% We don't have such a maximal number anymore. This handled by the domain instead.

%% don't cross with an empty boat
%nonexecutable cross(0, 0). 
nonexecutable cross(0, 0). 

%% don't cross with more than m animals
%nonexecutable cross(SS, SW) where SS + SW > CAPACITY.
nonexecutable cross(SS, SW) where SS + SW > 4, small_int(SS), small_int(SW).

%% update animal count
%caused -boat_here after cross(SS,SW) & boat_here. 
%caused boat_here after cross(SS,SW) & -boat_here.
-boat_here after cross(SS,SW), boat_here where small_int(SS), small_int(SW). 
boat_here after cross(SS,SW), -boat_here where small_int(SS), small_int(SW).

%cross(SS, SW) causes here(sheep)=HS - SS if boat_here & here(sheep)=HS where HS - SS >= 0.
%cross(SS, SW) causes here(wolf)=HW - SW if boat_here & here(wolf)=HW where HW - SW >= 0.
cross(SS, SW) causes here(sheep):=here(sheep) - SS, here(wolf):=here(wolf) - SW if boat_here where small_int(SS), small_int(SW).


%cross(SS, SW) causes here(sheep)=HS+SS if -boat_here & here(sheep)=HS where HS + SS < 121. 
%cross(SS, SW) causes here(wolf)=HW+SW if -boat_here & here(wolf)=HW where HW + SW < 121. 
cross(SS, SW) causes here(sheep):=here(sheep) + SS, here(wolf):=here(wolf) + SW if -boat_here where small_int(SS), small_int(SW).

%% don't allow less sheep than wolves when still sheeps here
%caused false if here(wolf)=N & here(sheep)=N1 where 0 < N1 & N1 < N. 
<false> if here(wolf) > here(sheep), here(sheep) > 0.

%% don't allow less wolves than sheeps when less then n sheeps here
%caused false if here(wolf)=N & here(sheep)=N1 where N1 < NUM & N < N1.
<false> if here(wolf) < here(sheep), here(sheep) < numb.

%:- query
%	label::0;
%	maxstep:: 1..600;
%	0: here(wolf)=NUM & here(sheep)=NUM;
%	0: boat_here;
%	maxstep: here(wolf)=0 & here(sheep)=0.
initially here(wolf)=numb.
initially here(sheep)=numb.
finally here(wolf)=0.
finally here(sheep)=0.

%coala ferry_const.cp | clingcon - ../../encodings/arithmetic.lp ../../encodings/arithmetic_initial.lp ../../encodings/arithmetic_finally.lp -c k=201 | outputformatclingocoala
% Note that the number of steps must be odd (-c k=200 won't work)
