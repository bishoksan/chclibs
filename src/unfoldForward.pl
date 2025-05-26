:- module(unfoldForward,[main/1],[dynamic]).

:- use_module(library(read)).
:- use_module(library(write)).
:- use_module(library(streams)).
:- use_module(library(aggregates)).
:- use_module(library(lists)).
:- use_module(library(cyclic_terms)).
:- use_module(chclibs(program_loader)).
:- use_module(chclibs(common)).
:- use_module(chclibs(builtins)).
:- use_module(chclibs(setops)).
:- use_module(library(system), [mktemp_in_tmp/2]).
:- use_module(library(system_extra), [del_file_nofail/1]).


:- dynamic(deterministic/0).
:- dynamic(callequals/0).



go3(F,OutPFile,Q) :-
    main(['-prg',F,'-entry',Q,'-o',OutPFile]).
    
go2(F,OutPFile) :-
    main(['-prg',F,'-entry',false,'-o',OutPFile]).

go(F) :-
    main(['-prg',F,'-entry',false]).
    
main(ArgV) :-
    cleanup,
    setOptions(ArgV,File,OutS,Entry),
    load_file(File),
    functor(Entry,P,N),
    findBackEdges([P/N],[],Ps,[],Bs,[]),
    extractBackPreds(Bs,BPs),
    unfoldablePreds(Ps,BPs,Us),
    unfoldForwardEdges(P/N,Us,OutS),
    close(OutS).

findBackEdges([P|Ps],M0,M3,Anc,Bs0,Bs3) :-
    successors(P,Ss),
    getBackEdges(Ss,P,Anc,Bs0,Bs1),
    marking(Ss,M0,M1,Ss1),
    findBackEdges(Ss1,[P|M1],M2,[P|Anc],Bs1,Bs2),
    findBackEdges(Ps,[P|M2],M3,Anc,Bs2,Bs3).
findBackEdges([],M,M,_,Bs,Bs).

extractBackPreds([(_-P)|Bs],Ps1) :-
    extractBackPreds(Bs,Ps),
    insertElement(Ps,P,Ps1).
extractBackPreds([],[]).

insertElement(Ps,P,Ps) :-
    member(P,Ps),
    !.
insertElement(Ps,P,[P|Ps]).

successors(P/N,Ss) :-
    setof(Q/M, [H,C,B]^(
            functor(H,P,N),
            my_clause(H,B,C),
            bodyPred(B,Q/M)),
            Ss),
    !.
successors(_,[]).

bodyPred([B|_],P/N) :-
    hasDef(B),
    functor(B,P,N).
bodyPred([B|_],P/N) :-
    \+ constraint(B,_),
    \+ builtin(B),
    functor(B,P,N).
bodyPred([_|Bs],Q) :-
    bodyPred(Bs,Q).

getBackEdges([],_,_,Bs,Bs).
getBackEdges([Q|Qs],P,Anc,[P-Q|Bs0],Bs1) :-
    member(Q,[P|Anc]),
    !,
    getBackEdges(Qs,P,Anc,Bs0,Bs1).
getBackEdges([_|Qs],P,Anc,Bs0,Bs1) :-
    getBackEdges(Qs,P,Anc,Bs0,Bs1).

marking([],M,M,[]).
marking([Q|Qs],M0,M1,Ss) :-
    member(Q,M0),
    !,
    marking(Qs,M0,M1,Ss).
marking([Q|Qs],M0,M1,[Q|Ss]) :-
    marking(Qs,M0,M1,Ss).

setOptions(ArgV,File,OutS,Entry) :-
    get_options(ArgV,Options,_),
    (member(programO(File),Options); 
            write(user_output,'No input file given.'),nl(user_output),fail),
    (member(entry(Q),Options) -> convertQueryString(Q,Entry); 
            write(user_output,'Warning: No entry goal given.'),nl(user_output),Entry=false),
    (member(outputFile(user_output),Options) -> OutS=user_output;
            member(outputFile(OutFile),Options), open(OutFile,write,OutS); 
                OutS=user_output),
    (member(deterministic,Options) -> assert(deterministic); true),
    (member(callequals,Options) -> assert(callequals); true).

% get_options/3 provided by Michael Leuschel
get_options([],[],[]).
get_options([X|T],Options,Args) :-
   (recognised_option(X,Opt,Values) ->
      ( append(Values, Rest, T),
        RT = Rest,
        Options = [Opt|OT], Args = AT
      )
   ;
      (
        Options = OT,    Args = [X|AT],
        RT = T
      )
   ),
   get_options(RT,OT,AT).

recognised_option('-prg',  programO(R),[R]).
recognised_option('-o',    outputFile(R),[R]).
recognised_option('-entry',  entry(Q),[Q]).
recognised_option('-det',  deterministic,[]).
recognised_option('-eq',  callequals,[]).

cleanup :-
    retractall(my_clause(_,_,_)),
    retractall(deterministic),
    retractall(callequals).

unfoldForwardEdges(P/N,Us,OutS) :-
    my_clause(H,B,_),
    functor(H,Q,M),
    (member(Q/M,Us) -> Q/M=P/N; true),  % not unfoldable or entry pred
    resultants(H,B,Us,Rs),
    writeClauses(Rs,OutS),
    fail.
unfoldForwardEdges(_,_,_).
    
resultants(H,B,Us,Rs) :-
    findall((H1:-R2), (
    	unfoldForward(B,Us,R), 
    	uncycle_term((H:-R),((H1:-R1),Eqs)), 	% Allow for cyclic terms
    	appendTail(Eqs,R1,R2),
    	numbervars((H1,R2),0,_)), Rs).
    	
appendTail([],Ys,Ys) :- 	% End of open list
	!.
appendTail([X-A|Xs],Ys,[A=X|Zs]) :-
	appendTail(Xs,Ys,Zs).

unfoldForward([true|Bs],Us,R) :-
	!,
    unfoldForward(Bs,Us,R).
unfoldForward([B|Bs],Us,R) :-
    functor(B,P,N),
    member(P/N,Us),
    !,
    my_clause(B,Body,_),
    append(Body,Bs,Bs1),
    unfoldForward(Bs1,Us,R).
unfoldForward([X=X|Bs],Us,R) :-     % unfold equalities if option is set
	callequals,
    !,
    unfoldForward(Bs,Us,R).
unfoldForward([B|Bs],Us,[B|R]) :-
    unfoldForward(Bs,Us,R).
unfoldForward([],_,[]).
    
writeClauses([(H:-B)|Rs],S) :-
    writeq(S,H),
    write(S,' :-'),
    nl(S),
    writeBodyAtoms(S,B),
    write(S,'.'),
    nl(S),
    writeClauses(Rs,S).
writeClauses([],_).
    
writeBodyAtoms(S,[]) :-
    !,
    write(S,'   '),
    write(S,true).
writeBodyAtoms(S,[B]) :-
    !,
    write(S,'   '),
    writeq(S,B).
writeBodyAtoms(S,[B1,B2|Bs]) :-
    write(S,'   '),
    writeq(S,B1),
    write(S,','),
    nl(S),
    writeBodyAtoms(S,[B2|Bs]).

% Read term Q1 from atom Q
convertQueryString(Q,Q1) :-
    mktemp_in_tmp('querystring.XXXXXXXX', TMP),
    open(TMP,write,S),
    write(S,Q),
    write(S,'.'),
    nl(S),
    close(S),
    open(TMP,read,S1),
    read(S1,Q1),
    close(S1),
    del_file_nofail(TMP).


detPred(P/N) :-
	P\==random,		% random is non-deterministic even though it has single result
    functor(A,P,N),
    findall(C,my_clause(A,_,C),Cls),
    length(Cls,L),
    L=<1.    
    
unfoldablePreds(Ps,BPs,Us) :-
    \+ deterministic,
    !,
    setdiff(Ps,BPs,Us).    
unfoldablePreds([],_,[]).
unfoldablePreds([P|Ps],BPs,[P|Us]) :-
    \+ member(P,BPs),
    detPred(P),
    !,
    unfoldablePreds(Ps,BPs,Us).
unfoldablePreds([_|Ps],BPs,Us) :-
    unfoldablePreds(Ps,BPs,Us).
    
hasDef(B) :-
    my_clause(B,_,_),
    !.
