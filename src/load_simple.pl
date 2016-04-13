:- module(load_simple, [load_file/1,my_clause/3], [assertions, isomodes, doccomments]).

%! \title Simple program loader
%
%  \module
%    Load clauses in `my_clause/3` (keeps a unique identifer for each
%    clause). Drops any `:- _` declaration.

:- dynamic my_clause/3.

:- use_module(library(lists)).
:- use_module(library(dynamic)).
:- use_module(library(read)).
:- use_module(common, [conj2List/2]).

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

% Drop all non-execute/specialize clauses
remember_clause(A, _) :- var(A), !. % Drop
remember_clause((:- _), _):- !.
remember_clause((A :- B), K) :- !,
	conj2List(B,BL),
	makeClauseId(K,CK),
	assertz(my_clause(A,BL,CK)).
remember_clause(A,K) :-
	makeClauseId(K,CK),
	assertz(my_clause(A,[],CK)).

makeClauseId(K,CK) :-
	name(K,NK),
	append("c",NK,CNK),
	name(CK,CNK).


