:- module(common, [
	separate_constraints/3,
	constraint/2,
	list2Conj/2,
	conj2List/2,
	listofList2Disj/2,
	list2Disj/2,
	max_member/2,
	number_atom/2,
	convert2num/2,
	dummyCList/2,
	occurs/2,
	memb1/2
	], [assertions, isomodes, doccomments]).

%! \title Some common useful predicates

separate_constraints([],[],[]).
separate_constraints([B|Bs],[C|Cs],Ds) :-
	constraint(B,C),
	!,
	separate_constraints(Bs,Cs,Ds).
separate_constraints([B|Bs],Cs,[B|Ds]) :-
	separate_constraints(Bs,Cs,Ds).

% TODO: Move this translation to the program reader
constraint(X=Y, X=Y).
constraint(X=:=Y, X=Y).
constraint(X is Y, X = Y).
constraint(X>Y, X>Y).
constraint(X>=Y, X>=Y).
constraint(X=<Y, X=<Y).
constraint(X<Y, X<Y).
constraint(_\==_,0=0). % TODO: document (drops constraint)
constraint(_=\=_,0=0). % TODO: document (drops constraint)
constraint(true,0=0).
constraint(fail,1=0).

list2Conj([A], (A)):- !.
list2Conj([A|R], (A,R1)):- !,
	list2Conj(R, R1).
list2Conj([], (true)). % meaning true

listofList2Disj([A], (A1)):- !,
	list2Conj(A, A1).
listofList2Disj([A|R], ((A1);R1)):- !,
	list2Conj(A, A1),
	listofList2Disj(R, R1).
listofList2Disj([], (1=0)). %meaning false

list2Disj([A], A):-
	!.
list2Disj([A|R], (A;R1)):-
	!,
	list2Disj(R, R1).
list2Disj([], (1=0)).


number_atom(N, A) :- number_codes(N, C), atom_codes(A, C).

max_member([X], X).
max_member([X|R], M):-
	!,
	max_member(R, Max),
	max(X,Max, M).

max(X, Y, X):-
	X>=Y,
	!.
max(_, Y, Y).

convert2num(A,A) :-
	number(A),
	!.
convert2num(A,A1) :-
	atom(A),
	atom_number(A,A1).

dummyCList([],[]).
dummyCList([C|Cs],[C=C|Cs1]) :-
	dummyCList(Cs,Cs1).

conj2List((A, B), [A|R]) :- !,
	conj2List(B,R).
conj2List(A, [A]).


occurs(X,[Y|_]) :-
	X == Y,
	!.
occurs(X,[_|Ys]) :-
	occurs(X,Ys).


memb1(X,[X|_]) :- !.
memb1(X,[_|Xs]) :-
	memb1(X,Xs).

