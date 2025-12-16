%:- module(cpascc, [main/1,cpa/1], [assertions, isomodes, doccomments]).
:- module(cpascc_rank, _, [assertions, isomodes, doccomments, dynamic]).
%! \title Convex Polyhedra Analysis

%  \module
%    NOTE: It also generates path FTA (Bish on 21-01-2016)

:- use_module(library(streams)).
:- use_module(library(read)).
:- use_module(library(write)).
:- use_module(library(aggregates)).

:- use_module(common).

:- use_module(setops).
:- use_module(canonical).
:- use_module(wto).
:- use_module(linearize).
:- use_module(library(terms_vars)).
:- use_module(library(ppl)).
:- use_module(library(lists)).
:- use_module(timer_ciao).
:- use_module(program_loader).
:- use_module(ppl_ops).
:- use_module(scc).


:- include(chclibs(get_options)).
:- include(chclibs(messages)).

:- dynamic(flag/1).
:- dynamic(currentflag/1).
:- dynamic(nextflag/1).
:- dynamic(operatorcount/1).
:- dynamic(widening_point/3).
:- dynamic(outputfile/1).
:- dynamic(newfact/2).
:- dynamic(oldfact/2).
:- dynamic(prio_widen/1).
:- dynamic(widenAt/1).
:- dynamic(widenf/1).
:- dynamic(detectwps/1).
:- dynamic(delays/1).
:- dynamic(clauseCount/1).
:- dynamic(invariant/2).
:- dynamic(narrowiterations/1).
:- dynamic(versionCount/1).
:- dynamic(versiontransition/2).
:- dynamic(version/3).
:- dynamic(clauseCount/1).
:- dynamic(pathtransition/1).
:- dynamic(atomicproposition/1).
:- dynamic cEx/1.
:- dynamic threshold/1.
:- dynamic traceTerm/2.


go(File) :-
	start_ppl,
    go2(File,temp),
    end_ppl.
    
go2(FileIn,FileOut) :-
    start_ppl,
    cpa(
            ['-prg',FileIn,
            '-widenpoints','widenpoints',
            '-widenout','widencns',
            '-narrowout','narrowcns',
            '-narrowiterations','0',
            '-delaywidening','0',
            '-withwut',
            '-wfunc','h79',
            '-o',FileOut]),
    end_ppl.
    
main(['-prg',FileIn]) :-
    !,
    go(FileIn).             
main(['-prg',FileIn, '-o', FileOut]) :-
    !,
    go2(FileIn,FileOut).
main(ArgV) :-
	start_ppl,
    cpa(ArgV),
    end_ppl.
    
% cpa/1 can be called from another module in which PPL is already initialised

cpa(ArgV) :-
    verbose_message(['Starting Convex Polyhedra analysis']),
    get_options(ArgV,Options,_),
    cleanWorkspace,
    set_options(Options,File,FactFile),
    initialise,
    ( flag(verbose) -> start_time ; true ),
    load_file(File),
    dependency_graph(Es,Vs),
    scc_graph(Es,Vs,G),
    iterate(G),
    narrow,
    verbose_message(['Convex Polyhedra Analysis Succeeded']),
    ( flag(verbose) -> end_time(user_output) ; true ),
    !,
    factFile(FactFile),
    generateCEx.
    
generateCEx:-
    cEx('$NOCEX'),
    !.
generateCEx :-
    cEx(CexFile),
    buildversions2,
    versioniterate,
    open(CexFile,write,S),
    findCounterexampleTrace(S),
    close(S).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Iterate solves each component 
% recursive components involve iterative fixpoint
% non-recursive components solved in one step.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

iterate([(non_recursive,P)|SCCs]) :-
    debug_message(['Non-recursive component ',P]),
    (flag(first) -> true; assertz(flag(first))),
    non_recursive_scc(P),
    iterate(SCCs).

iterate([(recursive,Ps)|SCCs]) :-
    (flag(first) -> true; assertz(flag(first))),
    sccClauses(Ps,Cls),
    select(P,Ps,Ps1),
	pClauses(Cls,P,PCls),
    hasRankingFunction(P,Ps1,PCls,R),
    !,
    debug_message(['Recursive component with ranking function ',R,' on ',P]),
    addCounters(Cls,P,R,KCls),
    addWideningPoint(P),
    addThresholds(P),
    linkClause(P,R,Cl),
    recursive_scc_with_counter(Ps,P,[Cl|KCls]),
    narrow_with_counter([Cl|KCls]),
    %eliminateCounter(P,R),
    newoldfacts,
    switch_flags,
    iterate(SCCs).
iterate([(recursive,Ps)|SCCs]) :-
    debug_message(['Recursive component ',Ps]),
    (flag(first) -> true; assertz(flag(first))),
    recursive_scc(Ps),
    narrow(Ps),
    iterate(SCCs).
iterate([]).

linkClause(P/N,R,clause(H,[K=<R+1,HK],PId)) :-
	functor(H,P,N),
	H=..[P|Xs],
	append(Xs,[K],XsK),
	HK=..[P|XsK],
	numbervars((H,K),0,_),
	atom_concat(P,k,PId).
	%check_entailed_rank(HK,N,K=<R+1).

hasRankingFunction(P,Ps1,PCls,R) :-
	singleRecursion(PCls,P,H,Bs,B),
	sameScc(Bs,Ps1,Bs1),
	melt((H,Bs1,B),(MH,MBs,MB)),
	prove(MBs,Cs,_),
	rankingFunction(MH,Cs,MB,R).
	
sameScc([B|Bs],Ps,Bs1) :-
	functor(B,Q,M),
	member(Q/M,Ps),	% call to same SCC - treat as if true
	!,
	sameScc(Bs,Ps,Bs1).
sameScc([B|Bs],Ps,[B|Bs1]) :-
	sameScc(Bs,Ps,Bs1).
sameScc([],_,[]).

	
sccClauses(Ps,PCls) :-
	findall(clause(H,B,Id),
		(member(P/N,Ps), my_clause(H,B,Id),functor(H,P,N),
		 numbervars((H,B),0,_)),
		 PCls).
		 
pClauses([clause(H,B,Id)|Cls],P/N,[clause(H,B,Id)|PCls]) :-
	functor(H,P,N),
	!,
	pClauses(Cls,P/N,PCls).
pClauses([_|Cls],P/N,PCls) :-
	pClauses(Cls,P/N,PCls).
pClauses([],_,[]).


singleRecursion(Cls,P,H,Bs,B) :-
	select(clause(H,Bs1,_Id),Cls,Cls1),
	linearRecursiveBody(P,Bs1,Bs,B),
	baseCases(P,Cls1).
	
linearRecursiveBody(P/N,Bs1,Bs,B) :-
	select(B,Bs1,Bs),
	functor(B,P,N),
	nonRecursive(P/N,Bs).
	
nonRecursive(_,[]).
nonRecursive(P/N,[B|Bs]) :-
	functor(B,Q,M),
	Q/M\==P/N,
	nonRecursive(P/N,Bs).
	
baseCases(P,[clause(_H,B,_Id)|Cls]) :-
	nonRecursive(P,B),
	baseCases(P,Cls).
baseCases(_,[]).

rankingFunction(MH,MCs,MB,R) :-
	functor(MH,P,N),
	MH=..[P|Ys0],
	MB=..[P|Ys1],
	freshVars(Ys0,Ws0,ACs1,MCs),
	freshVars(Ys1,Ws1,ACs,ACs1),
	numbervars((Ws0,Ws1,ACs),0,_),
	elimLocals(ACs,(Ws0,Ws1),Cs1),
	melt((Cs1,Ws0,Ws1),(Cs2,Zs,Zs1)),
	numbervars((Zs1,Zs,Cs2),0,_),		% get vars in order required by PPL
	makePolyhedron(Cs2,H),
	ppl_Polyhedron_space_dimension(H,Dim),
	J is 2*N-Dim,
	ppl_Polyhedron_add_space_dimensions_and_embed(H,J), % ensure polyhedron has dim 2*M
	rankingFunction_MS(H,point(Q)),
	makeAffineFunction(Q,N,R).	
	
elimLocals(B,(Xs,Xs1),B2) :-
	linearPart(B,BL),
	variables(BL,BVs),
	append(Xs,Xs1,Xs2),
	setdiff(BVs,Xs2,EVars),
	makePolyhedron(BL,H),
	project(H,EVars,H1), 	% note: eliminated variables have higher indexes 
	getConstraint(H1,B2).

variables('$VAR'(N),['$VAR'(N)]) :-
	!.
variables(T,Vs) :-
	T=..[_|Xs],
	argVars(Xs,Vs).
	
argVars([],[]).
argVars([X|Xs],Vs) :-
	variables(X,Vs1),
	argVars(Xs,Vs2),
	setunion(Vs1,Vs2,Vs).
	
freshVars([X|Xs],[Y|Ys],[X=Y|ACs],Cs) :-
	freshVars(Xs,Ys,ACs,Cs).
freshVars([],[],Cs,Cs).

linearPart(B,BL) :-
	melt(B,B1),
	linearize(B1,BL),
	B=B1.
	
% remove the k+1th variable if it is present since it represents the constant
makeAffineFunction(F1, K, F) :-
    VK = '$VAR'(K),
    subterm(F1, N*VK, F, N),
    !.
makeAffineFunction(F, _, F).

subterm(T,T,X,X) :-
	!.
subterm(T,R,T1,R1) :-
	T =.. [F|Xs],
	replace(Xs,R,Xs1,R1),
	T1 =.. [F|Xs1].

replace([],_,[],_).
replace([T|Xs],U,[T1|Ys],Y) :-
	subterm(T,U,T1,Y),
	replace(Xs,U,Ys,Y).
	
%---------------------------------------
addCounters([clause(H,B,Id)|PCls],P/N,R,[clause(HK,[K=0|B1],Id)|PKCls]) :-
	functor(H,P,N),
	nonRecursive(P/N,B),
	!,
	melt((H,B),(H1,B1)),
	H1=..[P|Xs],
	append(Xs,[K],XsK),
	HK=..[P|XsK],
	numbervars((HK,B1),0,_),
	addCounters(PCls,P/N,R,PKCls).
addCounters([clause(H,Bs1,Id)|PCls],P/N,R,[clause(HK,[K1=K-1,BK|Bs2],Id)|PKCls]) :-
	functor(H,P,N),
	linearRecursiveBody(P/N,Bs1,Bs,B),
	melt((H,Bs,B),(H1,Bs2,B1)),
	H1=..[P|Xs],
	append(Xs,[K],XsK),
	HK=..[P|XsK],
	B1=..[P|Ys],
	append(Ys,[K1],YsK),
	BK=..[P|YsK],
	numbervars((HK,Bs2,BK),0,_),
	addCounters(PCls,P/N,R,PKCls).
addCounters([clause(H,B,Id)|PCls],P/N,R,[clause(MH,BK,Id)|PKCls]) :-
	functor(H,Q,M),
	Q/M \== P/N,
	melt((H,B),(MH,MB)),
	addK(MB,P/N,R,BK),
	numbervars((MH,BK),0,_),
	addCounters(PCls,P/N,R,PKCls).
addCounters([],_,_,[]).

addK([B|Bs],P/N,R,[K=<MR+1,BK|BsK]) :-
	functor(B,P,N),
	!,
	B=..[P|Xs],
	append(Xs,[K],XsK),
	BK=..[P|XsK],
	functor(B1,P,N),   
	numbervars(B1,0,_),
	melt((B1,R),(B,MR)),	% Match the ranking function args to B
	addK(Bs,P/N,R,BsK).
addK([B|Bs],P/N,R,[B|BsK]) :-
	addK(Bs,P/N,R,BsK).
addK([],_,_,[]).

recursive_scc_with_counter(_Ps,_P,KCls) :-
	tp_cpa(KCls),
	retract(operatorcount(X)),
    Y is X + 1,
    assertz(operatorcount(Y)),
    debug_message(['Iteration',X]),
    retractall(flag(first)),
    fail.
recursive_scc_with_counter(Ps,P,PKCls) :-
    ( flag(debug_print) ->
        factFile(user_output)
    ; true
    ),
    widen,
    newoldfacts,
    not_converged, 
    !,
    switch_flags,
    recursive_scc_with_counter(Ps,P,PKCls).
recursive_scc_with_counter(_,_,_).

tp_cpa(PKCls) :-
    member(Cl,PKCls),
    melt(Cl,clause(H,B,Id)),
    operator(H,B,Id),
    fail.
tp_cpa(_).

eliminateCounter(P/N,R) :-
	functor(H,P,N),
	H=..[P|Xs],
	append(Xs,[K],XsK),
	HK=..[P|XsK],
	numbervars((H,K),0,_),
	atom_concat(P,k,PId),
	check_entailed_rank(HK,N,K=<R+1),
	raise_flag(HK),
	switch_flags,
	tp_cpa([clause(H,[K=<R+1,HK],PId)]),
	newoldfacts,
    switch_flags.
    
check_entailed_rank(HK,N,K=<R+1) :-
	melt((HK,K,R),(MH,MK,MR)),
	getoldfact(MH,Cs,_),
	numbervars((MH,Cs),0,_),
	makePolyhedron(Cs,H1),
	makePolyhedron([MK=<MR+1],H2),
	ppl_Polyhedron_space_dimension(H1,Dim1),
	ppl_Polyhedron_space_dimension(H2,Dim2),
	J1 is N+1-Dim1,
	J2 is N+1-Dim2,
	ppl_Polyhedron_add_space_dimensions_and_embed(H1,J1), 
	ppl_Polyhedron_add_space_dimensions_and_embed(H2,J2),
	(contains(H2,H1) -> 
		debug_message(['Rank constraint implied']); 
		debug_message(['Rank constraint not implied'])). 

%--------------------------
	
non_recursive_scc(P) :-
    convexhull_operation(P),
    retract(operatorcount(X)),
    Y is X + 1,
    assertz(operatorcount(Y)),
    debug_message(['Iteration',X]),
    newoldfacts,
    switch_flags.
    
recursive_scc(Ps) :-
    convexhull_operation(Ps),
    retract(operatorcount(X)),
    Y is X + 1,
    assertz(operatorcount(Y)),
    debug_message(['Iteration',X]),
    retractall(flag(first)),
    fail.
recursive_scc(Ps) :-
    ( flag(debug_print) ->
        factFile(user_output)
    ; true
    ),
    widen,
    newoldfacts,
    not_converged, 
    !,
    switch_flags,
    recursive_scc(Ps).
recursive_scc(_).
    
not_converged :-
    nextflag(_).
    
convexhull_operation(Ps) :-
    member(P/N,Ps),
    functor(H,P,N),
    my_clause(H,B,Id),
    operator(H,B,Id),
    fail.
convexhull_operation(_).



    
%%% narrowing iterations %%%

narrow :-
    narrowiterations(NitN),
    narrow1(NitN).

narrow1(0).
narrow1(X):-
    X > 0,
    narrowIteration,
    newoldfacts,
    Y is X-1,
    narrow1(Y).
    
narrowIteration :- 
    my_clause(H,B,_),
    narrowOperator(H,B),
    fail.
narrowIteration.

%% (LR) more local narrowing operations
narrow(Ps) :-
    narrowiterations(NitN),
    narrow1(NitN, Ps).

narrow1(0, _).
narrow1(X, Ps):-
    X > 0,
    narrowIteration(Ps),
    newoldfacts,
    Y is X-1,
    narrow1(Y, Ps).

narrowIteration(Ps) :-
    member(P/N,Ps),
    functor(H,P,N),
    my_clause(H,B,_),
    narrowOperator(H,B),
    fail.
narrowIteration(_).

% Narrowing for procedure with counter
narrow_with_counter(PKCls) :-
	narrowiterations(NitN),
    narrow2(NitN, PKCls).
    
narrow2(0, _).
narrow2(X, PKCls):-
    X > 0,
    narrowIteration_proc(PKCls),
    newoldfacts,
    Y is X-1,
    narrow2(Y, PKCls).

narrowIteration_proc(PKCls) :-
    member(Cl,PKCls),
    melt(Cl,(H,B,_)),
    narrowOperator(H,B),
    fail.
narrowIteration_proc(_).

%%%%%%%%%%%%%%%%

operator(Head,B,Id):-
    (changed(B);flag(first)),
    prove(B,Cs,_),
    varset((Head,Cs),Ys),
    Head =.. [_|Xs],
    linearize(Cs,CsLinNOP),
    dummyCList(Xs,DCLx),
    dummyCList(Ys,DCLy),
    append(DCLx,DCLy,DCL),
    append(CsLinNOP,DCL,CsLin),
    numbervars((Head:-CsLin),0,_),
    satisfiable(CsLin,H1),
    setdiff(Ys,Xs,Zs),
    project(H1,Zs,Hp),
    record(Head,Hp,Id).
    

changed(Bs) :- 
    member(B,Bs),
    isflagset(B),
    !.

prove([],[],[]).
prove([true],[],[]).
prove([B|Bs],[C|Cs],Ts):-
    constraint(B,C),
    !,
    prove(Bs,Cs,Ts).
prove([B|Bs],Cs,[T|Ts]):-
    getoldfact(B,CsOld,T),
    prove(Bs,Cs2,Ts),
    append(CsOld,Cs2,Cs).

narrowOperator(Head,B):-
    prove(B,Cs,_),
    varset((Head,Cs),Ys),
    Head =.. [_|Xs],
    linearize(Cs,CsLinNOP),
    dummyCList(Xs,DCLx),
    dummyCList(Ys,DCLy),
    append(DCLx,DCLy,DCL),
    append(CsLinNOP,DCL,CsLin),
    numbervars((Head:-CsLin),0,_),
    satisfiable(CsLin,H1),
    setdiff(Ys,Xs,Zs),
    project(H1,Zs,Hp),
    narrow_record(Head,Hp).

%%%%%%%%%%%%%%%%%
%  new/old facts
%%%%%%%%%%%%%%%%%

switch_flags :-
    retractall(currentflag(_/_)),
    retract(nextflag(F/N)),
    assertz(currentflag(F/N)),
    fail.
switch_flags :-
    true.

isflagset(F) :-
    functor(F,Fn,N),
    currentflag(Fn/N).

raise_flag(F):-
    functor(F,Fn,N),
    ( nextflag(Fn/N) ->
        true
    ; assertz(nextflag(Fn/N))
    ).

record(F,H,T) :-
    cond_assert(F,H,T).
    
narrow_record(F,H) :- 
    narrow_cond_assert(F,H).

cond_assert(F,H,T):-
    \+ (fact(F,H1), contains(H1,H)),
    getExistingConstraints(F,H0),
    convhull(H0,H,H2),
    assertz(newfact(F,H2)),
    raise_flag(F),
    %(traceTerm(F,_) -> true; assertz(traceTerm(F,T)),write(traceTerm(F,T)),nl).
    (traceTerm(F,_) -> true; assertz(traceTerm(F,T))).
    %check_raise_flag(F,H0,H2).

narrow_cond_assert(F,H):-
    \+ (newfact(F,H1), contains(H1,H)),
    getExistingNewConstraints(F,H0),
    convhull(H0,H,H2),
    retractall(newfact(F,_)),
    assertz(newfact(F,H2)).
    %check_raise_flag(F,H0,H2).

getExistingConstraints(F,H0) :-
    retract(newfact(F,H0)),
    !.
getExistingConstraints(F,H0) :-
    oldfact(F,H0),
    !.
getExistingConstraints(_,empty).

getExistingNewConstraints(F,H0) :-
    newfact(F,H0),
    !.
getExistingNewConstraints(_,empty).

check_raise_flag(F,empty,_) :-
    !,
    raise_flag(F).
check_raise_flag(_,H0,H2) :-
    equivalent(H0,H2),
    !.
check_raise_flag(F,_,_) :-
    raise_flag(F).

getoldfact(B,Cs1,T) :-
    functor(B,F,N),
    functor(B1,F,N),
    oldfact(B1,H),
    ppl_Polyhedron_get_minimized_constraints(H,Cs2),
    melt((B1,Cs2),(B,Cs1)),
    traceTerm(B1,T).

fact(X,Y) :-
    newfact(X,Y).
fact(X,Y) :-
    oldfact(X,Y).
    
newoldfacts :-
    retract(newfact(F,H)),
    retractall(oldfact(F,_)),
    assertz(oldfact(F,H)),
    fail.
newoldfacts.

%%%%%%%%%%%%%
% Widening
%%%%%%%%%%%%%

widen :-
    prio_widen(PrioWiden),
    possibleWidenPs(PrioWiden,PosPW),
    debug_message(['Possible Wideningpoints ',PosPW]),
    !,
    widenlist(PosPW).
    
% Add a widening point for P/N+1 is there exists one for P/N

addWideningPoint(P/N) :-
	widening_point(P/N,Dg,Delays),
	!,
	retract(widening_point(P/N,Dg,Delays)),
	retract(prio_widen(WPs)),
	addWidenpoint(WPs,P/N,WPs1),
	assert(prio_widen(WPs1)), 
	N1 is N+1,	
	assert(widening_point(P/N1,Dg,Delays)).
addWideningPoint(_).

% Add a threshold constraint for P/N+1 if there exists one for P/N
addThresholds(P/N) :-
	functor(A,P,N),
	invariant(A,C),
	melt((A,C),(MA,MC)),
	MA=..[P|Xs],
	append(Xs,[_],XsK), 	% add extra arg
	MA1=..[P|XsK],
	numbervars((MA1,MC),0,_),
	assert(invariant(MA1,MC)),
	fail.
addThresholds(_).

addWidenpoint([(Dg,P,N)|WPs],P/N,[(Dg,count(P),N1)|WPs1]) :-
	!,
	N1 is N+1,
	addWidenpoint(WPs,P/N,WPs1).
addWidenpoint([WP|WPs],P/N,[WP|WPs1]) :-
	addWidenpoint(WPs,P/N,WPs1).
addWidenpoint([],_,[]).

possibleWidenPs([],[]).
possibleWidenPs([(Dg,count(F),N)|WPs],[Fn|PWPs]) :-
    widening_point(F/N,Dg,_Delays),
    functor(Fn,F,N),
    newfact(Fn,H1),
    oldfact(Fn,H0),
    origPredDiff(H0,H1,F/N),
    !,
    %(F/N==while__28_ans/9 -> showWidenFacts(F/N); true),
    possibleWidenPs(WPs,PWPs).
possibleWidenPs([(Dg,F,N)|WPs],[Fn|PWPs]) :-
    widening_point(F/N,Dg,_Delays),
    functor(Fn,F,N),
    newfact(Fn,_),
    oldfact(Fn,_),
    !,
    possibleWidenPs(WPs,PWPs).
possibleWidenPs([_|WPs],PWPs) :-
    !,
    possibleWidenPs(WPs,PWPs).
    
showWidenFacts(F/N) :-
	functor(Fn,F,N),
    newfact(Fn,H1),
    oldfact(Fn,H0),
    getConstraint(H0,Cs0),
    getConstraint(H1,Cs1),
    write(Cs0),nl,
    write(Cs1),nl.
    
origPredDiff(H0,H1,F/N) :-
	functor(A,F,N),
	numbervars(A,0,_),
	A=..[F|Xs],
	append(_,[K],Xs),
	%  Remove the counter and compare
	copyPolyhedron(H0,G0),
	copyPolyhedron(H1,G1),
	project(G0,[K],G2),
	project(G1,[K],G3),
	\+ equivalent(G2,G3).

widenlist([]).
widenlist([Wc|Ws]) :-
    functor(Wc,WcF,WcN),
    widening_point(WcF/WcN,P,D), % delay widening
    D > 0,
    !,
    ND is D-1,
    retractall(widening_point(WcF/WcN,P,D)),
    assertz(widening_point(WcF/WcN,P,ND)),
    widenlist(Ws).
widenlist([Wc|Ws]) :-
    functor(Wc,WcF,WcN),
    widening_point(WcF/WcN,_,0),
    retract(newfact(Wc,NewH)),
    retract(oldfact(Wc,OldH)),
    debug_message(['Widening at ',Wc]),
    wutwiden(Wc,NewH,OldH,H2),
    assertz(oldfact(Wc,H2)),
    widenlist(Ws).
    


wutwiden(F,H0,H1,H2) :-
    widenWRToptions(F,H0,H1),
    H2 = H0,
    ( equivalent(H1,H2) ->
        true
    ; raise_flag(F)
    ).

widenWRToptions(_,H0,H1) :-
    widenf(nowut),
    !,
    widenPolyhedra(H0,H1).
widenWRToptions(F,H0,H1) :-
    widenf(withwut),
    !,
    getThresholds(F,Cns),
    debug_message(['Widen upto constraints: ',Cns]),
    widenUpto(H0,H1,Cns).

widenPolyhedra(H0,H1) :-
    ( widenf(bhrz03) -> widenPolyhedraBHRZ03(H0,H1)
    ; widenPolyhedraH79(H0,H1)
    ).
            
widenUpto(H0,H1,Cs) :-
    ( widenf(bhrz03) -> widenUptoBHRZ03(H0,H1,Cs)
    ; widenUptoH79(H0,H1,Cs)
    ).

getThresholds(F,Cout) :-
    bagof(Cs,invariant(F,Cs),Clist),
    !,
    flattenList(Clist,Cout).
getThresholds(_,[]).

flattenList([],[]).
flattenList([L|Ls],Lout) :-
    flattenList(Ls,Lpre),
    append(L,Lpre,Lout).
    
%%% input threshold constraints %%%%
readWutfacts:-
    threshold('$NOTHRESHOLD'),
    !.
readWutfacts :-
    threshold(TFile),
    open(TFile,read,S),
    read(S,C),
    assertWutFacts(C,S),
    close(S).
    
assertWutFacts(end_of_file,_) :-
    !.
assertWutFacts((H :- C), S) :-
    numbervars((H :- C),0,_),
    assertz(invariant(H,C)),
    read(S,C1),
    assertWutFacts(C1,S).
    
%%% input widening points %%%%
    
load_widenpoints(WPfile) :-
    open(WPfile,read,WP),
    read(WP,W),
    assert_widenpoints(W, WP),
    collect_wps.
    
assert_widenpoints(end_of_file,WP) :-
    !,
    close(WP).
assert_widenpoints(W,WP) :-
    assertWP(W),
    read(WP,W1),
    assert_widenpoints(W1,WP).
    
collect_wps :-
    findall((Dgs,F,N),widening_point(F/N,Dgs,_Delays),Wps),
    reverse(Wps,RWps),
    debug_message(['Ordered by degree ',RWps]),
    assertz(prio_widen(RWps)).
    
assertWP(widening_point(X,Y)) :-
    !,
    delays(D),
    assertz(widening_point(X,Y,D)).
assertWP(widening_point(X)) :-
    !,
    delays(D),
    assertz(widening_point(X,0,D)).
    
%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Predicate dependency graph
%%%%%%%%%%%%%%%%%%%%%%%%%%%%

dependency_graph(Es,Vs) :-
    findall(P/N-Q/M, (
                    my_clause(H,Bs,_),
                    functor(H,P,N),
                    member(B,Bs),
                    \+ constraint(B,_),
                    functor(B,Q,M)
                    ),
                    Es),
    findall(A, (
                    member(X-Y,Es),
                    (A=X; A=Y)
                    ),
                    Vs1),
    findall(P/N, (my_clause(H,_,_),functor(H,P,N)), Vs2),
    append(Vs1,Vs2,Vs).             
    

%%%% Getting and setting options

recognised_option('-prg',programO(R),[R]).
recognised_option('-widenpoints',widenP(R),[R]).
recognised_option('-widenout',widenO(R),[R]).
recognised_option('-narrowout',narrowO(R),[R]).
recognised_option('-narrowiterations',narrowiterationsO(R),[R]).
recognised_option('-delaywidening',delaywiden(R),[R]).
recognised_option('-wfunc',widenF(F),[F]).
recognised_option('-v',verbose,[]). % some verbose
recognised_option('-debug-print',debug_print,[]). % detailed comments
recognised_option('-querymodel',querymodel(Q),[Q]).
recognised_option('-nowpscalc',nowpscalc,[]).
recognised_option('-withwut',withwut,[]).
recognised_option('-detectwps',detectwps(M),[M]).
recognised_option('-o',factFile(F),[F]).
recognised_option('-cex',counterExample(F),[F]).
recognised_option('-threshold',thresholdFile(F),[F]).

set_options(Options,File,FactFile) :-
    member(programO(File),Options),
    ( member(verbose,Options) -> assertz(flag(verbose))
    ; retractall(flag(verbose))
    ),
    ( member(debug_print,Options) -> assertz(flag(debug_print))
    ; retractall(flag(debug_print))
    ),
    ( member(singlepoint,Options) -> assertz(widenAt(singlepoint))
    ; assertz(widenAt(allpoints))
    ),
    ( member(widenO(WOutput),Options) -> true
    ; WOutput='widencns'
    ),
    ( member(widenF(WFunc),Options) -> assertz(widenf(WFunc))
    ; assertz(widenf(h79))
    ),
    ( member(detectwps(M),Options) -> assertz(detectwps(M))
    ; assertz(detectwps(feedback))
    ),
    ( member(thresholdFile(TFile),Options) -> assertz(threshold(TFile))
    ; assertz(threshold('$NOTHRESHOLD'))
    ),
    ( member(withwut,Options) ->
      assertz(widenf(withwut)),
      readWutfacts,
      ( flag(debug_print) ->
          write('Widening points: '),nl,
          showallwideningpoints
      ; true
      )
    ; assertz(widenf(nowut))
    ),
    ( member(widenP(WPoints),Options) -> true
    ; WPoints='widenpoints'
    ),
    ( member(narrowO(NOutput),Options) -> true
    ; NOutput='stdnarrowout'
    ),
    ( member(factFile(FactFile),Options) -> true
    ; true
    ),
    ( member(narrowiterationsO(Nit),Options) -> atom_number(Nit,NitN)
    ; NitN is 0
    ),
    ( member(delaywiden(DWit),Options) -> atom_number(DWit,DWitN)
    ; DWitN is 0
    ),
    ( member(counterExample(CexFile),Options) -> assertz(cEx(CexFile))
    ; assertz(cEx('$NOCEX'))
    ),
    assertz(delays(DWitN)),
    assertz(narrowiterations(NitN)),
    detectwps(WPSMethod),
    ( member(nowpscalc,Options) -> true
    ; verbose_opts(WOpts),
      wto_file(File,WPSMethod,WPoints,WOpts)
    ),
    load_widenpoints(WPoints),
    assertz(outputfile(WOutput)).
    
%%%% clean workspace

initialise :-
    assertz(operatorcount(0)),
    assertz(flag(first)).

cleanWorkspace :-
    retractall(flag(_)),
    retractall(currentflag(_)),
    retractall(nextflag(_)),
    retractall(operatorcount(_)),
    retractall(widening_point(_,_,_)),
    retractall(outputfile(_)),
    retractall(newfact(_,_)),
    retractall(oldfact(_,_)),
    retractall(prio_widen(_)),
    retractall(widenAt(_)),
    retractall(widenf(_)),
    retractall(detectwps(_)),
    retractall(delays(_)),
    retractall(clauseCount(_)),
    retractall(versionCount(_)),
    retractall(versiontransition(_,_)),
    retractall(version(_,_,_)),
    retractall(pathtransition(_)),
    retractall(atomicproposition(_)),
    retractall(cEx(_)),
    retractall(narrowiterations(_)),
    retractall(traceTerm(_,_)).

    
%%%% Output 

showallwideningpoints:-
    widening_point(X,Degree,Delays),
    write('  '),
    write(X),
    write(' Included in '),
    write(Degree),
    write(' program loops'),
    write(' - should be delayed for iterations = '),
    write(Delays),nl,
    fail.
showallwideningpoints.

factFile(user_output):-
    oldfact(F,H),
    ppl_Polyhedron_get_minimized_constraints(H,C),
    numbervars(F,0,_),
    writeq(F), write(' :- '), 
    writeq(C),
    write('.'),
    nl,
    fail.
factFile(user_output) :-
	!.

factFile(File) :-
    open(File,write,Sout),
    %(File=user_output -> Sout=user_output; open(File,write,Sout)),
    (oldfact(F,H),
    ppl_Polyhedron_get_minimized_constraints(H,C),
    numbervars(F,0,_),
    writeq(Sout,F), write(Sout,' :- '), 
    writeq(Sout,C),
    write(Sout,'.'),
    nl(Sout),
    fail;
    close(Sout)).

% Version generation and FTA construction

fact3(F,H,_) :-
    oldfact(F,H).

buildversions2 :-
    assertz(versionCount(0)),
    fact3(F,H,_),
    retract(versionCount(N1)),
    N is N1+1,
    assertz(versionCount(N)),
    assertz(version(F,H,N)),
    fail.
buildversions2.

versioniterate :-
    assertz(clauseCount(0)),
    versionoperator,
    fail.
versioniterate.

versionoperator :-
    my_clause(Head,B,_),
    retract(clauseCount(K)),
    K1 is K+1,
    assertz(clauseCount(K1)),
    versionprove(B,Cs,Ds,Vs,_),
    Head =.. [_|Xs],
    linearize(Cs,CsLin),
    append(CsLin,Ds,CsDs),
    varset((Head,CsDs),Ys),
    dummyCList(Ys,DCL),
    append(CsDs,DCL,CsL),
    numbervars((Head:-CsL,Vs),0,_),
    satisfiable(CsL,H1),
    setdiff(Ys,Xs,Zs),
    project(H1,Zs,Hp),
    headversion(Head,Hp,Hv),
    assertTransition(Hv,Vs,K1).
    

versionprove([],[],[],[],[]).
versionprove([true],[],[],[true],[]).
versionprove([B|Bs],[C|Cs],Ds,[B|Vs],As):-
    constraint(B,C),
    !,
    versionprove(Bs,Cs,Ds,Vs,As).
versionprove([B|Bs],Cs,Ds,[V|Vs],[_|As]):-
    getversionfact(B,CsOld,V),
    versionprove(Bs,Cs,Ds1,Vs,As),
    append(CsOld,Ds1,Ds).
    
getversionfact(B,Cs1,Bk) :-
    functor(B,F,N),
    functor(B1,F,N),
    version(B1,H,K),        
    ppl_Polyhedron_get_minimized_constraints(H,Cs2),
    melt((B1,Cs2),(B,Cs1)),
    name(F,NF),
    name(K,NK),
    append("_v",NK,SuffK),
    append(NF,SuffK,NFK),
    name(FK,NFK),
    B =.. [F|Xs],
    Bk =.. [FK|Xs].
    


headversion(Head,_,Hk) :-
    version(Head,_,K), 
    Head =.. [F|Xs],
    name(F,NF),
    name(K,NK),
    append("_v",NK,SuffK),
    append(NF,SuffK,NFK),
    name(FK,NFK),
    Hk =.. [FK|Xs].

stateSymb(H,R) :-
    functor(H,F,_),
    name(F,T),
    append(_,[0'_|Xs],T),
    \+ member(0'_,Xs),
    name(R,Xs).

unaryBody([V],[X],VX) :-
    !,
    VX =.. [V,X].
unaryBody([V|Vs],[X|Xs],(VX,VXs)) :-
    VX =.. [V,X],
    unaryBody(Vs,Xs,VXs).
unaryBody([],[],true).

bodyStates([],[]) :-
    !.
bodyStates([B|Bs],BSs) :-
    constraint(B,_),
    !,
    bodyStates(Bs,BSs).
bodyStates([B|Bs],[BS|BSs]) :-
    stateSymb(B,BS),
    bodyStates(Bs,BSs).

clauseFunctor(N1,F) :-
    name(N1,M),
    append("c",M,CM),
    name(F,CM).

makeAtomicPropositionFact(true,Head,Prop) :-
    !,
    Head =.. [R|_],
    Prop =.. [prop,R,R].
makeAtomicPropositionFact(Body,_Head,Prop) :-
    Body =.. [R1,_X],
    Prop =.. [prop,R1,R1].

makeBpath(true, true) :-
    !.
makeBpath(Body,BPath) :-
    Body =.. [R1,X],
    BPath =.. [path,[R1|X]].

makeHpath(true,Head,HPath) :-
    !,
    Head =.. [R|_],
    HPath =.. [initState,R].
makeHpath(Body,Head,HPath) :-
    Body =.. [R1,_X],
    Head =.. [R,_],
    HPath =.. [trans,R1,R].

assertTransition(Hv,Vs,K1) :-
    stateSymb(Hv,R),
    bodyStates(Vs,BSs),
    clauseFunctor(K1,F),
    L =.. [F|BSs],
    functor(L,F,M),
    functor(L1,F,M),
    L1 =.. [F|Xs],
    canonical(L1),
    Head =.. [R,L1],
    unaryBody(BSs,Xs,Body),
    assertz(versiontransition(Head,Body)),
    makeHpath(Body,Head,HPath),
    makeBpath(Body,_BPath),
    makeAtomicPropositionFact(Body,Head,Prop),
    assertz(pathtransition(HPath)),
    assertz(atomicproposition(Prop)).

findCounterexampleTrace(S) :-
    (traceTerm(false,Id); traceTerm(false_ans,Id)),
    !,
    makeTrace(Id,Trace),
    write(Trace),nl,
    write(S,counterexample(Trace)),
    write(S,'.'),
    nl(S).
findCounterexampleTrace(S) :-
    write(S,'safe'),
    write(S,'.'),
    nl(S).  

makeTrace(Id,Trace) :-
    my_clause(_,B,Id),
    makeTraceList(B,Ids),
    Trace =.. [Id|Ids].
    
makeTraceList([],[]).
makeTraceList([true],[]).
makeTraceList([B|Bs],Ts):-
    constraint(B,_),
    !,
    makeTraceList(Bs,Ts).
makeTraceList([B|Bs],[Trace|Ts]):-
    functor(B,P,N),
    functor(B1,P,N),
    traceTerm(B1,T),
    makeTrace(T,Trace),
    makeTraceList(Bs,Ts).
