:- module(common, [
    prg_theory/1, % (data)
    separate_constraints/3,
    separate_array_constraints/3,
    constraint0/2,
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
    ], [datafacts, assertions, isomodes, doccomments]).

%! \title Some common useful predicates

:- data prg_theory/1.
prg_theory(_) :- fail.
prg_theory(array).

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
constraint(read(F,X,Y), read(F,X,Y)) :- prg_theory(array). % TODO:{arrays}
constraint(write(F,X,Y,F2), write(F,X,Y,F2)) :- prg_theory(array). % TODO:{arrays}
constraint(true,0=0).
constraint(fail,1=0).

% TODO: (for loader preprocessing)
constraint0(X=Y, X=Y).
constraint0(X=:=Y, X=Y).
constraint0(X is Y, X = Y).
constraint0(X>Y, X>Y).
constraint0(X>=Y, X>=Y).
constraint0(X=<Y, X=<Y).
constraint0(X<Y, X<Y).
constraint0(read(F,X,Y), read(F,X,Y)). % TODO:{arrays}
constraint0(write(F,X,Y,F2), write(F,X,Y,F2)). % TODO:{arrays}

% separate array constraints
% TODO: not a good name
separate_array_constraints([], [], []).
separate_array_constraints([C|Cs], [C|As], Rs) :-
    array_constraint(C), !,
    separate_array_constraints(Cs, As, Rs).
separate_array_constraints([C|Cs], As, [C|Rs]) :-
    separate_array_constraints(Cs, As, Rs).

array_constraint(read(_,_,_)) :- prg_theory(array).
array_constraint(write(_,_,_,_)) :- prg_theory(array).

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

conj2List(B, [A|R]) :- 
    nonvar(B),
    B = (A,B1),
    !,
    conj2List(B1,R).
conj2List(A, [A]).


occurs(X,[Y|_]) :-
    X == Y,
    !.
occurs(X,[_|Ys]) :-
    occurs(X,Ys).


memb1(X,[X|_]) :- !.
memb1(X,[_|Xs]) :-
    memb1(X,Xs).

