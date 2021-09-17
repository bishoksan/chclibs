:- module(readprog_ciaopp, [
    readprog/2, 
    sortClauses/3, 
    user_clauses/3,
    getPreds/2,
    writeClauses/2,
    applyVarNames/1,
    writeTerms/2
   ], [assertions, isomodes, doccomments, hiord]).

%! \title Program reader
%
%  \module
%    This module is used in other components (like \lib{qa},
%    \lib{scc}, etc.).
%
%    Limitations: 
%     - Input program consists of definite clauses.
%     - Doesn't handle metagoals like if-then-else, disjunction, bagof etc.
%     - Maybe the ciaopp program parser will enable this later.
%
%    Usage: `readprog(+File,-Program)`
%     - `File`: a filename containing the program to be transformed
%     - `Program`: a list containing the program clauses.
%         - first element of list a term predicates(Ps) where Ps
%           is a list of the predicates in the transformed program.
%         - remaining elements, terms clause((H :- B), Vs) where H:-B
%           is a clause, Vs is a binding list with the
%           original variable names.
%
%    Example query (using naive reverse program)
%    ```ciao
%    ?- readprog('rev.pl', Cls).
%    
%    Ps = [predicates([rev/2,app/3]),
%          cl((rev([],[]):-true),[]),
%          cl((rev([_B|_C],_D):-rev(_C,_A),app(_A,[_B],_D)),
%                 ['Ws'=_A,'X'=_B,'Xs'=_C,'Ys'=_D]),
%          cl((app([],_E,_E):-true),['Ys'=_E]),
%          cl((app([_F|_G],_H,[_F|_I]):-app(_G,_H,_I)),
%                 ['X'=_F,'Xs'=_G,'Ys'=_H,'Zs'=_I])]
%    ```

:- use_module(ciaopp(ciaopp)).
:- use_module(ciaopp(p_unit),[program/2,replace_program/2]).

:- use_module(library(streams)).
:- use_module(library(read)).
:- use_module(library(write)).
:- use_module(library(lists)).
:- use_module(chclibs(builtins)).
:- use_module(chclibs(myterms)).
:- use_module(chclibs(canonical)).
:- use_module(chclibs(common), [memb1/2]).
%:- use_package(runtime_ops).

:- use_module(library(operators)).
:- use_module(engine(runtime_control), [set_prolog_flag/2]).
:- use_module(loadfile_ciaopp).

readprog(F,[predicates(Ps)|Prog]) :-
    module(F),
    program(Cs,Ds),
    buildClauses(Cs,Ds,Ps,0,_,Prog).
    

buildClauses([],_,Ps,N,N,[]) :- 
    !,
    close_list(Ps).
buildClauses([C|Cls],[D|Ds],Ps,N0,N2,[T|Ts]) :- 
	buildClause(C,D,Ps,N0,N1,T),
    !,
    buildClauses(Cls,Ds,Ps,N1,N2,Ts).
buildClauses([_|Cls],[_|Ds],Ps,N0,N1,Ts) :- 
    buildClauses(Cls,Ds,Ps,N0,N1,Ts).



buildClause(clause(Head,Body):_ClauseID,dic(Xs,Ys),Ps,N0,N1,clause((H :- B),Vs)) :- 
    !,
    tidyHead(Head,H),
	tidyBody(Body,B),
    varNames(Xs,Ys,Vs),
    canonical((H:-B)),
    get_pred_name((H :- B),Pred,Bodypreds),
    each_memb1([Pred|Bodypreds],Ps),
    N1 is N0+1,
    !.

	
varNames([X|Xs],[Y|Ys],[X=Y|Vs]) :-
	varNames(Xs,Ys,Vs).
varNames([],[],[]).

ignore_decl(module(_,_)).
ignore_decl(module(_,_,_)).
ignore_decl(include(_)).
ignore_decl(use_module(_,_)).
ignore_decl(use_module(_)).
ignore_decl(entry(_,_)).
ignore_decl(entry(_)).
ignore_decl(multifile(_)).
ignore_decl(type(_)).
ignore_decl(dynamic(_)).

get_pred_name((H :- B),P/N,BPs) :-
    !,
    functor(H,P,N),
    body_preds(B,BPs).
get_pred_name(H ,P/N,[]) :-
    functor(H,P,N).

body_preds(true,[]) :-
    !.
body_preds((\+ B,Bs),[(\+)/1|Ps]) :-
    !,
    body_preds((B,Bs),Ps).
body_preds((B,Bs),[P/N|Ps]) :-
    !,
    functor(B,P,N),
    body_preds(Bs,Ps).
body_preds(\+ B,[(\+)/1|Ps]) :-
    !,
    body_preds(B,Ps).
body_preds(B,[P/N]) :-
    functor(B,P,N).

each_memb1([],_).
each_memb1([P|Ps],S) :-
    memb1(P,S),
    each_memb1(Ps,S).
    
% TODO: move to common
close_list([]) :-
    !.
close_list([_|X]) :-
    close_list(X).

read_clause(S,cl(C,Vs)) :-
    read_term(S,C,[variable_names(Vs)]).

sortClauses([predicates(Ps)|Cls], Ps,Procs) :-
    initProcs(Ps,Procs0),
    buildProcs(Cls,Procs0,Procs).

initProcs([],[]).
initProcs([P/N|Ps], [proc(P/N,[])|Procs]) :-
    initProcs(Ps,Procs).
    
buildProcs([],Pr,Pr).
buildProcs([clause((H :- B), Vs)|Cls], Procs0, Procs2) :-
    functor(H,P,N),
    insertClause(Procs0,P/N,H,B,Vs,Procs1),
    buildProcs(Cls, Procs1, Procs2).
    
insertClause([proc(Pred,Cls)|Procs0],Pred,H,B,Vs,[proc(Pred,Cls1)|Procs0]) :-
    !,
    append(Cls,[clause((H :- B), Vs)],Cls1).
insertClause([Proc|Procs0],Pred,H,B,Vs,[Proc|Procs1]) :-
    insertClause(Procs0,Pred,H,B,Vs,Procs1).
    
user_clauses([],_,[]).
user_clauses([proc(P/N,Cls)|_],P/N,Cls1) :-
    !,
    returnCls(Cls,Cls1).
user_clauses([_|Prcs],P/N,Cls) :-
    user_clauses(Prcs,P/N,Cls).

returnCls([],[]).
returnCls([clause(C,_)|Cls],[C|Cls1]) :-
    returnCls(Cls,Cls1).

getPreds([clause(Cl,_)|Cls],Qs) :-
    get_pred_name(Cl,P,Ps),
    each_memb1([P|Ps],Qs),
    getPreds(Cls,Qs).
getPreds([],S) :-
    close_list(S).

writeClauses([],_).
writeClauses([predicates(_)|Cls],S) :-
    writeClauses(Cls,S).
writeClauses([clause((A :- B),_Ws)|BCls],Stream) :-
    %applyVarNames(Ws),
    writeq(Stream,A),
    write(Stream,' :-'),
    nl(Stream),
    writeBody(Stream,B),
    write(Stream,'.'),
    nl(Stream),
    writeClauses(BCls,Stream).
    
writeBody(S,(B,Bs)) :-
    !,
    write(S,'      '),
    writeq(S,B),
    write(S,','),
    nl(S),
    writeBody(S,Bs).
writeBody(S,B) :-
    write(S,'      '),
    writeq(S,B).

applyVarNames([]).
applyVarNames([X=X|Ws]) :-
    applyVarNames(Ws).

% TODO: move to common.pl
writeTerms([],_).
writeTerms([T|Ts],Stream) :-
    writeq(Stream,T),
    write(Stream,'.'),
    nl(Stream),
    writeTerms(Ts,Stream).
    
% added to handle operators in input file

enable_assrt_syntax :-
    % flags for hiord
    set_prolog_flag(read_hiord, on),
    % operators for assertions
    op(975, xfx,(=>)),
    op(978, xfx,(::)),
    op(1150, fx,(decl)),
    op(1150,xfx,(decl)),
    op(1150, fx,(pred)),
    op(1150,xfx,(pred)),
    op(1150, fx,(func)),
    op(1150,xfx,(func)),
    op(1150, fx,(prop)),
    op(1150,xfx,(prop)),
    op(1150, fx,(modedef)),
    op(1150,xfx,(modedef)),
    op(1150, fx,(calls)),
    op(1150,xfx,(calls)),
    op(1150, fx,(success)),
    op(1150,xfx,(success)),
    op(1150, fx,(test)),
    op(1150,xfx,(test)),
    op(1150, fx,(texec)),
    op(1150,xfx,(texec)),
    op(1150, fx,(comp)),
    op(1150,xfx,(comp)),
    op(1150, fx,(entry)),
    op(1150,xfx,(entry)),
    op(1150, fx,(exit)),
    op(1150,xfx,(exit)),
    % operators for regtypes
    op(1150, fx,(regtype)),
    op(1150,xfx,(regtype)).
