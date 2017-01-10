BC:

coala -l bc [input.bc]


The language has the following reserved words:
    not, true, false, if, causes, 
    ifcons, after, default, inertial, 
    nonexecutable, impossible, action, 
    fluent, where

These words may not be used for and inside fluent and action names.
A more formal way of writing those statements (except for not) is using "<" and ">".
E.g. <if> <true> <after>



The .bc file may contain the following rules:



*************************************
*** Fluent definitions:

<fluent> alive.
<fluent> at(1,2).


+ Alternative:

fluent alive.
fluent at(1,2).

++ Multivalued fluents:

<fluent> status=stationary, status=moving.
<fluent> status=falling.
<fluent> number=X <where> elem(X). % See the "using Variables from ASP parts" section for details.



*************************************
*** Static Laws:

alive <if> -dead.
at(1,2) <ifcons> at(1,2).
dooropen <if> buttonon <ifcons> dooropen, -blocked.


+ Alternative:

dooropen if buttonon ifcons dooropen, -blocked.



*************************************
*** Dynamic Laws:

buttonpressed <after> toggle.
has(cup) <after> pickup(cup), at(cup) <ifcons> has(cup).

+ Alternatives:

has(cup) after pickup(cup), at(cup) ifcons has(cup).
pickup(cup) <causes> has(cup) <if> at(cup) <ifcons> has(cup).
pickup(cup) causes has(cup) if at(cup) ifcons has(cup).



*************************************
*** Impossible Laws:

<impossible> at(1,2), has(object).
<impossible> at(1,2) <ifcons> has(object).

+ Alternative:

impossible at(1,2) ifcons has(object).



*************************************
*** Nonexecutable Laws:

<nonexecutable> jump, indoors.
<nonexecutable> jump <if> indoors.

+ Alternative:

nonexecutable jump if indoors.



*************************************
*** Inertial, Default:

<inertial> at(1,2).
<default> onground.
<default> -open.

+ Alternative:

inertial at(1,2), at(2,4).
default -open, onground



*************************************
*** ASP:

<asp>
someaspstuff(1..10000).
</asp>

Code inside the <asp> tags remains untouched.



*************************************
*** using Variables:

Variables can be used in any law.
There must be a where-part to bind variables.

at(X,Y) <after> moveto(X,Y) <where> <fluent> at(X,Y).
at(X,Y) <after> moveto(X,Y) <where> <action> moveto(X,Y).
at(X,Y) <after> moveto(X,Y) <where> <fluent> at(X,Y), <action> moveto(X,Y).

Variables for fluents and actions can be used in a more general way (if necessary):

-idle <after> A <where> <action> A.
F <after> A <where> <action> A, <fluent> F.

+ Alternative:

at(X,Y) after moveto(X,Y) where fluent at(X,Y), action moveto(X,Y).



*************************************
*** using Variables from ASP parts:

Additionally, variables can also be bound using domain predicates from ASP programs.
In the following examples, position(X,Y) is bound in an ASP-part.

<asp>position(1..10,1..10).</asp>

at(X,Y) <after> moveto(X,Y) <where> position(X,Y).
at(X,Y) <after> moveto(X,Y) <where> position(X,Y), not nogo(X,Y).
at(X,Y) <after> moveto(X,Y) <where> position(X,Y), X != Y.
at(X,Y) <after> moveto(X,Y) <where> position(X,Y), X = Y + 1.
at(X,Y) <after> moveto(X,Y) <where> position(X,Y), X > Y + 1.

+ Alternative:

at(X,Y) after moveto(X,Y) where position(X,Y), X > Y + 1.



*************************************
*** using Arithmetics:

Using clingcon, it is possible to add fluents with large domains.
( Visit the clingcon page at https://potassco.org/clingcon/ )
Otherwise if using writing
    at(X) <after> moveto(X) <where> position(X).
would reproduce that law for every possible element of X.

We can currently only allow Linear Constraints and in arithmetics.
Linear constraints have the form:
    1 * A + 2 * B + 34345 * C + -123 * C = 1234.
We apply some transformations to allow as general terms as possible,
but there are some things, like multiplying C*A which sadly cannot be done here.
We added division by numbers, which are technically done using helping variables (and additional LCs):
1.    -235*A/23 + B = 123
2. ==   -235*H + B = 123
3.      H*23 = A        (or H*23 -1*A = 0)
Note that we do use rounding in our encoding, which translates 3. instead to one of the different options:
For truncating (rounding down):
4.  H*23 -A <= 0
5.  H*23 -A > -23
For ceiling (rounding up):
4.  H*23 -A < 23
5.  H*23 -A >= 0
For normal rounding (rounding up at .5):
4.  H*46 -2*A < R
5.  H*46 -2*A >= -R
By default, truncating is enabled (this may be changed by commenting in/out lines in the encodings/arithmetic.lp file)


+ Declaration

<fluent> numbername : -100 .. 100000.

This declares a fluent "numbername" with a domain from -100 to 100000.

<fluent> unbound : <int>.


+ Usage

In order not to reproduce the laws for each possible assignment,
try to minimize the number of variables used in such laws.
Therefore we allow direct reference to other arithmetic fluents in arithmetic laws.

+ Assignments (in the head of static and dynamic laws)
unbound:=125 <if> set.
unbound:=numbername*10 <if> something.
something:=1 <after> reset.

Note that dynamic laws allow to refer to the previous step in the Assignment:
unbound:=unbound+1 <after> increase.

Therefore these laws won't allow to access values of fluents in the same step as unbound will be set.


+ Checks

good <if> unbound*10-100 <= something*-1.
good <if> unbound*10-100=something*-1.
good <if> unbound*10-100==something*-1.

Accepted compairison operators:
    <, <=, >, >=, =, ==, !=


+ Translation.

Here is an example for the reduction.
Assume that there are two fluents with 1000 elements in their domain:
PREVIOUS
    <asp>dom(1..1000).</asp>
    fluent x=X where dom(X).
    fluent y=X where dom(X).
    x=X after transfer, y=X where fluent y=X.

will now be written as:
    fluent x,y : 1..1000.
    x:=y after transfer.


