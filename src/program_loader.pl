:- module(program_loader,[
	load_file/1,my_clause/3
   ],[assertions, isomodes, doccomments, dynamic]).

%! \title Program (Horn clauses) loader
%
%  \module
%    Load clauses in `my_clause/3` (keeps a unique identifer for each
%    clause). Drops any `:- _` declaration.
%

% TODO: merge with load_simple.pl

:- use_module(library(streams)).
:- use_module(library(read)).
:- use_module(library(lists)).
:- use_module(chclibs(common), [conj2List/2, occurs/2, constraint0/2]).

:- dynamic my_clause/3.

load_file(F) :-
	retractall(my_clause(_,_,_)),
	open(F,read,S),
	remember_all(S,1),
	close(S).

remember_all(S,K) :-
	read(S,C),
	( C == end_of_file ->
	    true
	; remember_clause(C,K),
	  K1 is K+1,
	  remember_all(S,K1)
	).

remember_clause((A :- B),K) :- !,
	atomconstraints(A, ACs0,ACs1, Ant),
	writeAtomEq(Ant,Anodupl,Es0,Es1),
	%
	conj2List(B,BL),
	bodyconstraints(BL,BL0,BCs0,BCs1),
	ACs1=Es0,
	Es1=BCs0,
	BCs1=BL0,
	makeClauseId(K,CK),
	assertz(my_clause(Anodupl,ACs0,CK)).
remember_clause(A,K) :-
	atomconstraints(A, ACs0, ACs1, Ant),
	writeAtomEq(Ant,Anodupl,Es0,[]),
	ACs1=Es0,
	makeClauseId(K,CK),
	assertz(my_clause(Anodupl,ACs0,CK)),
	!.
%Drop all non-execute/specialize clauses
remember_clause(_,_).

makeClauseId(K,CK) :-
	name(K,NK),
	append("c",NK,CNK),
	name(CK,CNK).

bodyconstraints([],[],Cs,Cs).
bodyconstraints([B|Bs],[B|Bs1],Cs0,Cs1) :-
	constraint0(B,_),
	!,
	bodyconstraints(Bs,Bs1,Cs0,Cs1).
bodyconstraints([B|Bs],[B2|Bs1],Cs0,Cs1) :-
	atomconstraints(B,Cs0,BCs1,B1),
	writeAtomEq(B1,B2,Es0,Es1),
	BCs1=Es0,
	bodyconstraints(Bs,Bs1,Es1,Cs1).
	
% ---------------------------------------------------------------------------
% TODO: Document

atomconstraints(H,Cs0,Cs1,H1) :-
	H =.. [P|Xs],
	genConstraints(Xs,Ys,Cs0,Cs1),
	H1 =.. [P|Ys].

genConstraints([],[],Cs,Cs).
genConstraints([X|Xs],[Y|Ys],[X=Y|Cs0],Cs1) :-
	var(X),
	occurs(X,Xs),
	!,
	genConstraints(Xs,Ys,Cs0,Cs1).
genConstraints([X|Xs],[X|Ys],Cs0,Cs1) :-
	var(X),
	!,
	genConstraints(Xs,Ys,Cs0,Cs1).
genConstraints([T|Xs],[Y|Ys],[Y=T|Cs0],Cs1):-
	genConstraints(Xs,Ys,Cs0,Cs1).

%! writeAtomEq(A,A1,Eqs0,Eqs1):
%    Remove duplicate variables from A, introducing fresh variables
%    and unifications
	
% Example:
% ```
% ?- writeAtomEq(p(U,U,V,U,V,W),A,Es,[]).
%
% A = p(U,_A,V,_B,_C,W),
% Es = [U=_A,U=_B,V=_C] 
% ```

writeAtomEq(A,A1,Eqs0,Eqs1) :-
	A =.. [P|Xs],
	removeDupls(Xs,Xs1,Eqs0,Eqs1),
	A1 =.. [P|Xs1].
	
removeDupls([],[],Es,Es).
removeDupls([X|Xs],Xs2,[X=Y|Eqs0],Eqs1) :-
	replaceDupl(X,Xs,Y,Xs1),
	!,
	removeDupls([X|Xs1],Xs2,Eqs0,Eqs1).
removeDupls([X|Xs],[X|Xs1],Eqs0,Eqs1) :-
	removeDupls(Xs,Xs1,Eqs0,Eqs1).

replaceDupl(X1,[X2|Xs],XK,[XK|Xs]) :-
	X1 == X2,
	!.
replaceDupl(X,[X1|Xs],Y,[X1|Xs1]) :-
	replaceDupl(X,Xs,Y,Xs1).

