:- module(load_simple_ciaopp, [load_file/1,my_clause/3], [assertions, isomodes, doccomments, dynamic]).

%! \title Simple program loader
%
%  \module
%    Load clauses in `my_clause/3` (keeps a unique identifer for each
%    clause). Drops any `:- _` declaration.

:- use_module(ciaopp(ciaopp)).
:- use_module(ciaopp(p_unit),[program/2,replace_program/2]).


:- dynamic my_clause/3.

:- use_module(library(streams)).
:- use_module(library(lists)).
:- use_module(library(read)).
:- use_module(chclibs(common), [conj2List/2]).
:- use_module(library(write)).
:- use_module(library(streams)).

load_file(F) :-
    retractall(my_clause(_,_,_)),
    module(F),
    program(Cs,_Ds),
    assert_all(Cs,1),
    showProg.
    
assert_all([],_).
assert_all([C|Cs],K) :-
	assert_my_clause(C,K),
	!,
	K1 is K+1,
	assert_all(Cs,K1).
assert_all([_|Cs],K) :-
	assert_all(Cs,K).
	

assert_my_clause(clause(Head,Body):_ClauseID, K) :- !,
    tidyHead(Head,H),
	tidyBody(Body,B),
	conj2List(B,BL),
    makeClauseId(K,CK),
    assertz(my_clause(H,BL,CK)).


makeClauseId(K,CK) :-
    name(K,NK),
    append("c",NK,CNK),
    name(CK,CNK).

tidyHead(H,H).

tidyBody((B,Bs),(B1,Bs1)) :-
	!,
	tidyAtom(B,B1),
	tidyBody(Bs,Bs1).
tidyBody(B,B1) :-
	!,
	tidyAtom(B,B1).
	
tidyAtom(A:_Pos,A1) :-
	A =.. [P|Args],
	tidyPred(P,P1),
	A1 =.. [P1|Args].
	
tidyPred(P,P1) :-	
	atom_concat('arithmetic:',P1,P),
	!.
tidyPred(P,P1) :-	
	atom_concat('term_basic:',P1,P),
	!.
tidyPred(P,P).
	
showProg :-
	my_clause(H,B,C),
	write(my_clause(H,B,C)),
	nl,
	fail.
showProg.	

