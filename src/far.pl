:- module(far, [main/1, far/2], []).

% Computes redundant arguments using the FAR algorithm
% Leuschel and Sørensen 1996

:- use_module(chclibs(builtins)).
:- use_module(chclibs(scc)).
:- use_module(chclibs(balanced_tree)).
:- use_module(chclibs(readprog)).
:- use_module(chclibs(canonical)).
:- use_module(chclibs(timer_ciao)).

:- use_module(chclibs(setops)).

:- use_module(library(lists)).
:- use_module(library(streams)).
:- use_module(library(write)).

main([File,Outfile]) :-
    far(File,Outfile).

main([File]) :-
    far(File,user_output).

far(F,OutF) :-
    readprog(F,Cls),
    sortClauses(Cls,Ps,Prog),
    far_fix(Ps,Prog,Filters),
    filterProg(Cls,Filters,Cls1),
    (OutF=user_output -> S=user_output; open(OutF,write,S)),
    writeClauses(Cls1,S),
    close(S).

far_fix(Ps,Prog,F) :-
    scc(Ps,Prog,G),% compute the dependency ordering
    far_fix_groups(G,Prog,root,F).

% far_fix_groups(X,Prog,Y,Z): X is a list of SCCs.  Y is the current approx.
% Z is the final result.

far_fix_groups([],_,F,F) :-
    !.
% case where the SCC is non-recursive

far_fix_groups([(R,[G])|Gs],Prog,F0,F3) :-
    nonrec(R),
    !,
    init([G],R0),
    updateDefs(R0,F0,F1),
    user_clauses(Prog,G,Cls),
    far_alpha([Cls],iterate(0,[]),F1,R0,R2),  % no need to iterate if non-rec.
    updateDefs(R2,F1,F2),
    far_fix_groups(Gs,Prog,F2,F3).

% case where the SCC is recursive

far_fix_groups([(_,G)|Gs],Prog,F0,F3) :-
    user_procs(G,Prog,Procs),
    init(G,R0),
    updateDefs(R0,F0,F1),
    far_iterate(iterate(0,[]),Procs,G,F1,R0,R2),
    updateDefs(R2,F1,F2),
    far_fix_groups(Gs,Prog,F2,F3).

nonrec(non_recursive).

user_procs([],_,[]).
user_procs([P|Ps],Prog,[Cls|Procs]) :-
    user_clauses(Prog,P,Cls),
    user_procs(Ps,Prog,Procs).

init([P/N|Ps],[(P/N :- [])|R]) :-
    functor(B,P,N),
    sp_builtin(B),
    !,
    init(Ps,R).
init([P/N|Ps],[(P/N :- Js)|R]) :-
    argNums(N,Js),
    init(Ps,R).
init([],[]).

argNums(0,[]).
argNums(J,[J|Js]) :-
    J > 0,
    J1 is J-1,
    argNums(J1,Js).

% far_iterate(A,C,D,E,F,G):  finds the solution for a single SCC
%	A: list of predicates that changed on previous iteration.
%	C: solutions for the temp goals
%	D: list of predicates in the SCC
%	E: accumulated solution of all lower SCCs
%	F: current solution for this SCC
%	G: final solution for this SCC

far_iterate(iterate(N,[]),_,_,_,R,R) :-
    N > 0,
    !.
far_iterate(iterate(N,Nofix),Procs,Ps,Acc,R1,R) :-
    updateDefs(R1,Acc,D),
    far_alpha(Procs,iterate(N,Nofix),D,R1,R2),
    check_fix(Ps,R1,R2,Fix),
    N1 is N+1,
    !,
    far_iterate(iterate(N1,Fix),Procs,Ps,Acc,R2,R).

updateDefs([],D,D).
updateDefs([(P :- S)|R1],D0,D2) :-
    search_replace_tree(D0,P,_,D1,(P :- S)),
    !,
    updateDefs(R1,D1,D2).
updateDefs([(P :- S)|R1],D0,D2) :-
    !,
    insert_tree(D0,P,(P :- S),D1),
    updateDefs(R1,D1,D2).

far_alpha([],_,_,[],[]).
far_alpha([Cls|Ps], Nofix,R,[PR|PRs],[UP1|R1]) :-
    infer_proc(Cls,Nofix,R,As),
    allKept(As,Es),
    newFilter(Es,PR,UP1),
    far_alpha(Ps,Nofix,R,PRs,R1).

newFilter((S :- B1),(S :- B2),(S :- B3)) :-
    setdiff(B2,B1,B3).

infer_proc([(_:-B)|Cls],Nofix,R,As) :-% if no predicate in the body
    nochange(B,Nofix),			% changed, skip clause
    !,
    infer_proc(Cls,Nofix,R,As).
infer_proc([Cl|Cls],Nofix,R,[(P/N :- Ys)|As]) :-
    melt(Cl,(H:-B)),
    varseq(H,Ws),
    multipleOccurringVars(Ws,Us),
    functor(H,P,N),
    applyfilters(B,R,B1),
    vars(B1,Vs),
    collectFilteredArgs(H,N,Us,Vs,Ys),
    !,
    infer_proc(Cls,Nofix,R,As).
infer_proc([],_,_,[]).

applyfilters((B,Bs),R,[B|BVs]) :-
    sp_builtin(B),
    !,
    applyfilters(Bs,R,BVs).
applyfilters((B,Bs),R,[Vs|BVs]) :-
    !,
    functor(B,P,N),
    search_tree(R,P/N,(P/N :- Zs)),
    selectArgs(B,N,Zs,Vs),
    applyfilters(Bs,R,BVs).
applyfilters(B,_,[B]) :-
    sp_builtin(B),
    !.
applyfilters(B,R,[Vs]) :-
    functor(B,P,N),
    search_tree(R,P/N,(P/N :- Zs)),
    selectArgs(B,N,Zs,Vs).

selectArgs(_,J,_,[]) :-
    J < 1.
selectArgs(B,J,Zs,Vs) :-
    J >= 1,
    member(J,Zs), 	% non-filtered arg
    !,
    J1 is J-1,
    selectArgs(B,J1,Zs,Vs).
selectArgs(B,J,Zs,[T|Vs]) :-
    J1 is J-1,
    arg(J,B,T),
    selectArgs(B,J1,Zs,Vs).

collectFilteredArgs(_,J,_,_,[]) :-
    J < 1,
    !.
collectFilteredArgs(H,J,Us,Vs,Ys) :-
    %J >= 1,
    J1 is J-1,
    arg(J,H,A),
    filteredArg(A,Us,Vs,J,Ys,Ys1),
    collectFilteredArgs(H,J1,Us,Vs,Ys1).


filteredArg(A,_,_,J,[J|Ys1],Ys1) :-		% rule 1
    nonvar(A),
    !.
filteredArg(A,Us,_,J,[J|Ys1],Ys1) :-	% rule 2
    var(A),
    memb3(A,Us),
    !.
filteredArg(A,_,Vs,J,[J|Ys1],Ys1) :-	% rule 3
    var(A),
    memb3(A,Vs),
    !.
filteredArg(_,_,_,_,Ys1,Ys1).


nochange(B,iterate(N,Nofix)) :-
    N > 0,		% always evaluate the first (N=0) iteration
    preds(B,Ps),
    \+ commonpred(Ps,Nofix).

preds(true,[]) :-
    !.
preds((B,Bs), [P/N|Ps]) :-
    !,
    functor(B,P,N),
    preds(Bs,Ps).
preds(B,[P/N]) :-
    functor(B,P,N).

commonpred(X,Y) :-
    member(Z,X),
    member(Z,Y).



check_fix([],[],[],[]).
check_fix([_|Ps],[RP|R],[RP1|S],Qs) :-
    fixpoint(RP,RP1),
    !,
    check_fix(Ps,R,S,Qs).
check_fix([P|Ps],[_|R],[_|S],[P|Qs]) :-
    check_fix(Ps,R,S,Qs).

fixpoint([],[]).
fixpoint((_ :- X),(_ :- Y)) :-
    \+ surplus_element(X,Y).

surplus_element(Y,X) :-
    member(Z,Y), 
    \+ member(Z,X).

allKept([],(_ :- [])).
allKept([(S :- B)|As],(S :- B1)) :-
    allKept(As,(S :- B2)),
    setunion(B,B2,B1).


memb1(X,[X|_]) :-
    !.
memb1(X,[_|Xs]) :-
    memb1(X,Xs).

memb3(X,[X1|_]) :-
    X == X1,
    !.
memb3(X,[_|Xs]) :-
    memb3(X,Xs).

vars(T,Vs) :-
    vars3(T,[],Vs).

vars3(X,Vs,Vs1) :-
    var(X),
    !,
    insertvar(X,Vs,Vs1).
vars3(X,Vs,Vs) :-
    atomic(X),
    !.
vars3(X,Vs,Vs1) :-
    nonvar(X),
    X =.. [_|Args],
    argvars(Args,Vs,Vs1).

argvars([],Q,Q).
argvars([X|Xs],Vs,Vs2) :-
    vars3(X,Vs,Vs1),
    argvars(Xs,Vs1,Vs2).

insertvar(X,[],[X]).
insertvar(X,[Y|Vs],[Y|Vs]) :-
    X == Y,
    !.
insertvar(X,[Y|Vs],[Y|Vs1]) :-
    insertvar(X,Vs,Vs1).


writeList([],_).
writeList([X|Xs],S) :-
    write(S,X),
    writeList(Xs,S).

varseq(X,S) :-
    varseq3(X,S,[]).

varseq3(X,[X|S],S) :-
    var(X),
    !.
varseq3(X,S0,S2) :-
    X =.. [_|Xs],
    varseqList(Xs,S0,S2).

varseqList([],S0,S0).
varseqList([X|Xs],S0,S2) :-
    varseq3(X,S0,S1),
    varseqList(Xs,S1,S2).

multipleOccurringVars([],[]).
multipleOccurringVars([_],[]).
multipleOccurringVars([X1,X2|Xs],[X1|Ys]) :-
    memb3(X1,[X2|Xs]),
    !,
    multipleOccurringVars([X2|Xs],Ys).
multipleOccurringVars([_,X2|Xs],Ys) :-
    multipleOccurringVars([X2|Xs],Ys).

filterProg([predicates(Ps)|Cls],Filters,[predicates(Ps)|Cls1]) :-
    filterProg(Cls,Filters,Cls1).
filterProg([clause((H :- B),Ws)|Cls],Filters,[clause((H1 :- B1),Ws)|Cls1]) :-
    filterAtom(H,Filters,H1),
    filterBody(B,Filters,B1),
    filterProg(Cls,Filters,Cls1).
filterProg([],_,[]).

filterAtom(H,Filters,H1) :-
    functor(H,P,N),
    search_tree(Filters,P/N,(P/N :- F)),
    H =.. [P|Xs],
    filterArgs(Xs,1,N,F,Ys),
    H1 =.. [P|Ys].

filterBody((B,Bs),Filters,(B,Bs1)) :-
    sp_builtin(B),
    !,
    filterBody(Bs,Filters,Bs1).
filterBody((B,Bs),Filters,(B1,Bs1)) :-
    !,
    filterAtom(B,Filters,B1),
    filterBody(Bs,Filters,Bs1).
filterBody(B,_,B) :-
    sp_builtin(B).
filterBody(B,Filters,B1) :-
    filterAtom(B,Filters,B1).

filterArgs([],_,_,_,[]).
filterArgs([_|Xs],J,N,F,Ys) :-
    member(J,F),
    !,
    J1 is J+1,
    filterArgs(Xs,J1,N,F,Ys).
filterArgs([X|Xs],J,N,F,[X|Ys]) :-
    J1 is J+1,
    filterArgs(Xs,J1,N,F,Ys).

	