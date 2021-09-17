:- module(loadfile_ciaopp,[
    load_file/1,my_clause/3,
    tidyHead/2,tidyBody/2, showProg/0
   ],[assertions, isomodes, doccomments, dynamic]).

:- use_module(ciaopp(ciaopp)).
:- use_module(ciaopp(p_unit),[program/2,replace_program/2]).
:- use_module(chclibs(common), [conj2List/2, occurs/2, constraint0/2]).

:- use_module(library(write)).
:- use_module(library(streams)).

:- dynamic my_clause/3.
    
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

	
assert_my_clause(clause(Head,Body):_ClauseID,K) :-
	tidyHead(Head,H),
	tidyBody(Body,B),
	atomconstraints(H, ACs0,ACs1, Ant),
    writeAtomEq(Ant,Anodupl,Es0,Es1),
    conj2List(B,BL),
    bodyconstraints(BL,BL0,BCs0,BCs1),
    ACs1=Es0,
    Es1=BCs0,
    BCs1=BL0,
	atom_number(KA,K),
	atom_concat(c,KA,CK),
	assertz(my_clause(Anodupl,ACs0,CK)).
	
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
