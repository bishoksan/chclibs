%:- module(cpascc, [main/1,cpa/1], [assertions, isomodes, doccomments]).
:- module(cpascc_new, _, [assertions, isomodes, doccomments, dynamic]).
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
:- use_module(readprog).
:- use_module(ppl_ops).
:- use_module(scc).


go(File) :-
    go2(File,temp).
    
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
    get_options(ArgV,Opts,_),
    set_options(Opts,[],Options1,File,FactFile),
    verbose_message(['Starting Convex Polyhedra analysis'],Options1),
    get(detectwps,WPSMethod,Options1),
    get(widenP,WPoints,Options1),
    ( get(nowpscalc,yes,Options1) -> true
    ; verbose_opts(WOpts,Options1),
      wto_file(File,WPSMethod,WPoints,WOpts)
    ),
    load_widenpoints(WPoints,Options1,Options2),
    get(threshold,F,Options2),
    readWutfacts(F,Options2,Options3),
    
    ( member((verbose,yes),Options1) -> start_time ; true ),
    readprog(File,Prog),
    standardClauses(Prog,Prog1),
    dependency_graph(Prog1,Es,Vs),
    scc_graph(Es,Vs,G),
    put(operatorCount,0,Options3,Options4),
    makeset(Vs,Vs1),
    initSolns(Vs1,Soln0),
    iterate(G,Prog1,Options4,Options5,Soln0,Soln1),
    narrow(Prog1,Options5,Soln1,Soln2),
    verbose_message(['Convex Polyhedra Analysis Succeeded'],Options3),
    ( member((verbose,yes),Opts) -> end_time(user_output) ; true ),
    !,
    factFile(Soln2,FactFile).
    %generateCEx.
    
initSolns([],[]).
initSolns([P/N|Vs],[fact(A,H,0)|Soln]) :-
	functor(A,P,N),
	numbervars(A,0,_),
	makePolyhedron([0=1],H), % Initialise to empty polyhedron
	raiseDimension(H,N),
	initSolns(Vs,Soln).
    

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Iterate solves each component 
% recursive components involve iterative fixpoint
% non-recursive components solved in one step.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

iterate([(non_recursive,P)|SCCs],Prog,Options0,Options2,Soln0,Soln2) :-
    debug_message(['Non-recursive component ',P],Options0),
    sccClauses(P,Prog,Cls),
	incrementCount(Options0,Options1,J1),    
	tp_cpa(firstpass,Cls,J1,Soln0,NewSols),
    updateSolns(NewSols,Soln0,Soln1,_),
    J is J1-1,
    debug_message(['Iteration ',J],Options0),
    iterate(SCCs,Prog,Options1,Options2,Soln1,Soln2).
iterate([(recursive,Ps)|SCCs],Prog,Options0,Options4,Soln0,Soln4) :-
    sccClauses(Ps,Prog,Cls),
    select(P,Ps,Ps1),
	pClauses(Cls,P,PCls),
    hasRankingFunction(P,Ps1,PCls,Soln0,R),
    debug_message(['Recursive component with ranking function ',R,' on ',P],Options0),
    !,
    sccWithRf(Cls,P,R,Options0,Options1,Soln0,Soln1),
    sccWithoutRf(Cls,Options0,Options2,Soln0,Soln2),
    meetSolutions(Ps,Soln1,Soln2,Soln3),
    mergeOptions(Options1,Options2,Options3),
    iterate(SCCs,Prog,Options3,Options4,Soln3,Soln4).
iterate([(recursive,Ps)|SCCs],Prog,Options0,Options2,Soln0,Soln2) :-
    debug_message(['Recursive component ',Ps],Options0),
	sccClauses(Ps,Prog,Cls),
    sccWithoutRf(Cls,Options0,Options1,Soln0,Soln1),
    iterate(SCCs,Prog,Options1,Options2,Soln1,Soln2).
iterate([],_,Opts,Opts,Solns,Solns).

sccClauses(Ps,Prog,PCls) :-
	findall(clause(H,B,Id),
		(member(P/N,Ps), member(clause(H,B,Id),Prog),functor(H,P,N)),
		 PCls).
    
sccWithRf(Cls,P,R,Options0,Options3,Soln0,Soln3) :-    
    addCounters(Cls,P,R,KCls),
    addWideningPoint(P,Options0,Options1),
    addThresholds(P,Options1,Options2),
    initSolution(P,Soln0,Soln1),
    linkClause(P,R,Cl),
    recursive_scc(firstpass,[Cl|KCls],Options2,Options3,Soln1,Soln2),
    narrow([Cl|KCls],Options3,Soln2,Soln3),
    ( member((debug_print,yes),Options3) ->
        check_entailed(Cl,Soln3,Options3)
    ; true
    ).
    
sccWithoutRf(Cls,Options0,Options1,Soln0,Soln2) :-
    recursive_scc(firstpass,Cls,Options0,Options1,Soln0,Soln1),
    narrow(Cls,Options1,Soln1,Soln2).
    
    
%-----------------------
% Solve a recursive SCC 
%-----------------------

recursive_scc(FP,Cls,Options0,Options3,Soln0,Soln2) :-
	incrementCount(Options0,Options1,J),
	tp_cpa(FP,Cls,J,Soln0,NewSols),
	J1 is J-1,
	debug_message(['Iteration ',J1],Options1),
	( member((debug_print,yes),Options1) ->
        factFile(Soln0,user_output)
    ; true
    ),
    widen(Options1,Options2,Soln0,NewSols,NewSols1),
    updateSolns(NewSols1,Soln0,Soln1,Changed),
    check_change(Changed,Cls,Options2,Options3,Soln1,Soln2).
    
check_change(1,Cls,Options2,Options3,Soln1,Soln2) :-
    recursive_scc(cont,Cls,Options2,Options3,Soln1,Soln2).
check_change(0,_,Opts,Opts,Soln,Soln).


% Compute a new set of facts from the given clauses

tp_cpa(FP,[Cl|Cls],J,Soln0,NewSols1) :-
    melt(Cl,clause(H,B,Id)),
    operator(FP,H,B,Id,J,Soln0,NewSol),
    tp_cpa(FP,Cls,J,Soln0,NewSols0),
    addSol(NewSol,NewSols0,J,NewSols1).
tp_cpa(_,[],_,_,[]).

% Solve a clause body and project to clause head
% First pass always executes, otherwise look for change before solving

operator(firstpass,Head,B,_,_,Soln0,NewSol) :-
	!,
    solveAndProject(Head,B,Soln0,NewSol).
operator(cont,Head,B,_,J,Soln0,NewSol):-
    changed(B,J,Soln0),
    !,
    solveAndProject(Head,B,Soln0,NewSol).
operator(_,_,_,_,_,_,null).

changed(Bs,J,Soln) :- 
	J1 is J-1,
    member(B,Bs),
    changedFact(B,J1,Soln),
    !.

changedFact(B,J1,Soln) :-
	functor(B,P,N),
	functor(B1,P,N),
	member(fact(B1,_,J1),Soln). 	% Fact derived on previous iteration J1
    
solveAndProject(Head,B,Soln0,fact(H,Hp)) :-  
    prove(B,Cs,_,Soln0),
    linearize(Cs,CsLin),
    atomConstraints(Head,H,AllCs,CsLin),
    H=..[P|Xs],  
    varset((H,AllCs),Ys),
    H=..[P|Xs],
    setdiff(Ys,Xs,Zs),
    numbervars((H:-AllCs),0,_),
    satisfiable(AllCs,H1),
    !,
    functor(H,P,N),
    project(H1,Zs,Hp),
    raiseDimension(Hp,N).
solveAndProject(_,_,_,null). 



addSol(null,NewS,_,NewS).
addSol(fact(A,H0),NewSols,J,NewSols1) :-
	member(fact(A,H1,J),NewSols),
	!,
	convhull(H1,H0,H2),
	updateFact(A,H2,J,NewSols,NewSols1) .
addSol(fact(A,H0),NewSols,J,[fact(A,H0,J)|NewSols]).

updateFact(A,H,J,Soln0,Soln1) :-
	append(Fs,[fact(A,_,_)|Fs1],Soln0), 	% Replace the old fact
	append(Fs,[fact(A,H,J)|Fs1],Soln1).
	
updateWithHull(A,Soln0,NewSols,Soln1) :-
	member(fact(A,OldH,_),Soln0),
	member(fact(A,H,J),NewSols),
	convhull(OldH,H,NewH),
	updateFact(A,NewH,J,Soln0,Soln1).
	
updateSolns([fact(A,H0,J)|NewSols],Soln0,Soln2,Changed) :-
	condUpdateFact(A,H0,J,Soln0,Soln1,Ch1),
	updateSolns(NewSols,Soln1,Soln2,Ch2),
	(Ch2>Ch1 -> Changed=Ch2; Changed=Ch1).	% logical OR
updateSolns([],Solns,Solns,0).

updateSolnsSimple([fact(A,H0,J)|NewSols],Soln0,Soln2) :-
	updateFact(A,H0,J,Soln0,Soln1),
	updateSolnsSimple(NewSols,Soln1,Soln2).	
updateSolnsSimple([],Solns,Solns).


updateFactSimple(A,HW,J,Soln0,Soln1) :-
	append(Fs,[fact(A,_,_)|Fs1],Soln0), 	% Replace the old fact
	append(Fs,[fact(A,HW,J)|Fs1],Soln1).

condUpdateFact(A,H0,J,Soln0,Soln1,Ch) :-
	append(Fs,[fact(A,H1,_)|Fs1],Soln0), 
	checkContainment(H1,H0,A,J,Soln0,Soln1,Fs,Fs1,Ch).
	
checkContainment(H1,H0,_,_,Soln0,Soln0,_,_,0) :-	
	contains(H1,H0),	% already recorded
	!.
checkContainment(H1,H0,A,J,_,Soln1,Fs,Fs1,1) :-
	convhull(H1,H0,Hull),
	append(Fs,[fact(A,Hull,J)|Fs1],Soln1).
    
initSolution(P/N,Soln0,[fact(A1,H,0)|Soln0]) :-
	N1 is N+1,
	functor(A1,P,N1),
	numbervars(A1,0,_),
	makePolyhedron([0=1],H), % Initialise to empty polyhedron
	raiseDimension(H,N1).
	
% Form the intersection of solutions for given predicates
	
meetSolutions([P/N|Ps],Soln0,Soln1,Soln3) :-
	functor(A,P,N),
	member(fact(A,H0,J0),Soln0),
	member(fact(A,H1,J1),Soln1),
	ppl_Polyhedron_intersection_assign(H0,H1),
	(J0>J1 -> J=J0; J=J1),
	updateFactSimple(A,H0,J,Soln0,Soln2),
	meetSolutions(Ps,Soln2,Soln1,Soln3).
meetSolutions([],Soln0,_,Soln0).  % Copy solutions from Soln0

mergeOptions(Options1,Options2,Options3) :-
	get(operatorCount,N1,Options1),
	get(operatorCount,N2,Options2),
	(N1>N2 -> N=N1; N=N2),
	put(operatorCount,N,Options1,Options3).
	
% Solve an SCC with a ranking function

pClauses([clause(H,B,Id)|Cls],P/N,[clause(H,B,Id)|PCls]) :-
	functor(H,P,N),
	!,
	pClauses(Cls,P/N,PCls).
pClauses([_|Cls],P/N,PCls) :-
	pClauses(Cls,P/N,PCls).
pClauses([],_,[]).

linkClause(P/N,R,clause(H,[K=<R+1,HK],PId)) :-
	functor(H,P,N),
	H=..[P|Xs],
	append(Xs,[K],XsK),
	HK=..[P|XsK],
	numbervars((H,K),0,_),
	atom_concat(P,k,PId).

hasRankingFunction(P,Ps1,PCls,Soln,R) :-
	hasStaticRankingFunction(P,Ps1,PCls,Soln,R),
	!.
hasRankingFunction(P,Ps1,PCls,Soln,R) :-
	hasDynamicRankingFunction(P,Ps1,PCls,Soln,R).
	
hasStaticRankingFunction(P,_Ps1,PCls,_Soln,R) :-
	singleRecursion(PCls,P,H,Bs,B),
	separate_constraints(Bs,Cs1,_),
	melt((H,Cs1,B),(MH,Cs,MB)),
	rankingFunction(MH,Cs,MB,R).
	
hasDynamicRankingFunction(P,Ps1,PCls,Soln,R) :-
	singleRecursion(PCls,P,H,Bs,B),
	sameScc(Bs,Ps1,Bs1),
	melt((H,Bs1,B),(MH,MBs,MB)),
	prove(MBs,Cs,_,Soln),
	rankingFunction(MH,Cs,MB,R).
	
sameScc([B|Bs],Ps,Bs1) :-
	functor(B,Q,M),
	member(Q/M,Ps),	% call to same SCC - treat as if true
	!,
	sameScc(Bs,Ps,Bs1).
sameScc([B|Bs],Ps,[B|Bs1]) :-
	sameScc(Bs,Ps,Bs1).
sameScc([],_,[]).

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
	N2 is 2*N,
	raiseDimension(H,N2),
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
	
% Modify the SCC clauses, adding a counter to the clause with the RF
% and adding the ranking function constraint to calls from within the SCC

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

% Check whether the ranking function constraint is already derived
% after solving the SCC
    
check_entailed(clause(_H,[K=<R+1,HK],_),Soln,Opts) :-
	member(fact(HK,H0,_),Soln),
	makePolyhedron([K=<R+1],H1),
	functor(HK,_,N1),
	raiseDimension(H1,N1),
	(contains(H0,H1) -> 
		debug_message(['Rank constraint implied'],Opts); 
		debug_message(['Rank constraint not implied'],Opts)). 






% ensure polyhedron has dim N
raiseDimension(H,N) :-
	ppl_Polyhedron_space_dimension(H,Dim),
	J is N-Dim,
	ppl_Polyhedron_add_space_dimensions_and_embed(H,J).

prove([],[],[],_).
prove([true],[],[],_).
prove([B|Bs],[C|Cs],Ts,Soln):-
    constraint(B,C),
    !,
    prove(Bs,Cs,Ts,Soln).
prove([B|Bs],Cs,[T|Ts],Soln):-
    getFact(B,CsOld,T,Soln),
    prove(Bs,Cs2,Ts,Soln),
    append(CsOld,Cs2,Cs).
    
getFact(B,Cs1,_T,Soln) :-
    functor(B,F,N),
    functor(B1,F,N),
    member(fact(B1,H,J),Soln),
    J>0,
    ppl_Polyhedron_get_minimized_constraints(H,Cs2),
    melt((B1,Cs2),(B,Cs1)).
    


%%%%%%%%%%%%%
% Widening
%%%%%%%%%%%%%

widen(Options1,Options2,Soln1,NewSols,NewSols1) :-
	get(operatorCount,J,Options1),
    get(widenpoints,WPs,Options1),
    widenlist(WPs,Options1,Options2,J,Soln1,NewSols,NewSols1).
    
% Find the applicable widening points
widenlist([],Options,Options,_,_,NewSols,NewSols).
widenlist([widening_point(A,Delay)|Ws],Options0,Options2,J,Soln0,NewSols,NewSols2) :-
	member(fact(A,_,_),NewSols),
	member(fact(A,_,I),Soln0), I>0,	% Ignore initial empty fact
    !,
    widenAfterDelay(Delay,A,Options0,Options1,J,Soln0,NewSols,NewSols1),
    widenlist(Ws,Options1,Options2,J,Soln0,NewSols1,NewSols2).
widenlist([_|Ws],Options0,Options2,J,Soln0,NewSols,NewSols1) :-
    widenlist(Ws,Options0,Options2,J,Soln0,NewSols,NewSols1).
    
    
% For each applicable widening point, either perform the widening
% or decrement the delay

widenAfterDelay(D,A,Options0,Options1,_,Soln0,NewSols,NewSols1) :-
	D>0,
	decrementDelay(A,Options0,Options1),
	updateWithHull(A,Soln0,NewSols,NewSols1).
widenAfterDelay(0,A,Options0,Options0,J,Soln0,NewSols,NewSols1) :-
	functor(A,P,N),
	debug_message(['Widening at ',P/N],Options0),
	member(fact(A,OldH,_),Soln0),
	member(fact(A,NewH,J),NewSols),
	convhull(OldH,NewH,Hull),
    widenWRToptions(A,Hull,OldH,Options0),
    updateFact(A,Hull,J,NewSols,NewSols1).
    

decrementDelay(A,Options0,Options1) :-
	get(widenpoints,WPs,Options0),
	append(WPs0,[widening_point(A,D)|WPs1],WPs),
	D1 is D-1,
	append(WPs0,[widening_point(A,D1)|WPs1],WPs2),
	put(widenpoints,WPs2,Options0,Options1).

widenWRToptions(_,H0,H1,Options) :-
    get(withwut,no,Options),
    !,
    widenPolyhedra(H0,H1,Options).
widenWRToptions(F,H0,H1,Options) :-
    getThresholds(F,Cns,Options),
    debug_message(['Widen upto constraints: ',Cns],Options),
    widenUpto(H0,H1,Cns,Options).

widenPolyhedra(H0,H1,Options) :-
	get(widenf,WF,Options),
    ( WF=bhrz03 -> widenPolyhedraBHRZ03(H0,H1)
    ; widenPolyhedraH79(H0,H1)
    ).
            
widenUpto(H0,H1,Cs,Options) :-
	get(widenf,WF,Options),
    ( WF=bhrz03 -> widenUptoBHRZ03(H0,H1,Cs)
    ; widenUptoH79(H0,H1,Cs)
    ).

getThresholds(F,Cout,Options) :-
	get(invariants,CList,Options),
	findall(C,member(invariant(F,C),CList),Cs),
	flattenList(Cs,Cout).
	
    
%%-----------%%  
%% narrowing %%
%%-----------%% 

narrow(Cls,Options,Soln0,Soln1) :-
	get(operatorCount,J,Options),
	get(narrowiterations,NitN,Options),
	narrow1(NitN,Cls,J,Soln0,Soln1).
	
narrow1(0,_,_,Solns,Solns).
narrow1(X,Cls,J,Solns0,Solns2):-
    X > 0,
    tp_cpa(firstpass,Cls,J,Solns0,NewSolns),
    updateSolnsSimple(NewSolns,Solns0,Solns1),
    X1 is X-1,
    J1 is J+1,
    narrow1(X1,Cls,J1,Solns1,Solns2).



    
% Add a widening point for P/N+1 is there exists one for P/N

addWideningPoint(P/N,Options0,Options1) :-
	get(widenpoints,WPs,Options0),
	functor(A,P,N),
	select(widening_point(A,Delays),WPs,WPs1),
	!,
	N1 is N+1,
	functor(A1,P,N1),
	numbervars(A1,0,_),
	update(widenpoints,[widening_point(A1,Delays)|WPs1],Options0,Options1).
addWideningPoint(_,Opts,Opts).

% Add a threshold constraint for P/N+1 if there exists one for P/N
addThresholds(P/N,Options0,Options1) :-
	functor(A,P,N),
	N1 is N+1,
	functor(A1,P,N1),
	numbervars(A1,0,_),
	get(invariants,Ts,Options0),
	newThresholds(Ts,A,A1,Ts1),
	update(invariants,Ts1,Options0,Options1).
	
newThresholds([invariant(A,C)|Ts],A,A1,[invariant(A1,C),invariant(A,C)|Ts1]) :-
	!,
	newThresholds(Ts,A,A1,Ts1).
newThresholds([T|Ts],A,A1,[T|Ts1]) :-
	newThresholds(Ts,A,A1,Ts1).
newThresholds([],_,_,[]).

addWidenpoint([(Dg,P,N)|WPs],P/N,[(Dg,count(P),N1)|WPs1]) :-
	!,
	N1 is N+1,
	addWidenpoint(WPs,P/N,WPs1).
addWidenpoint([WP|WPs],P/N,[WP|WPs1]) :-
	addWidenpoint(WPs,P/N,WPs1).
addWidenpoint([],_,[]).


flattenList([],[]).
flattenList([L|Ls],Lout) :-
    flattenList(Ls,Lpre),
    append(L,Lpre,Lout).
    
%%% input threshold constraints %%%%

readWutfacts('$NOTHRESHOLD',Opts0,Opts1) :-
	put(invariants,[],Opts0,Opts1),
    !.
readWutfacts(F,Opts0,Opts1) :-
    open(F,read,S),
    read(S,C),
    readWutFacts(C,S,Ts),
    put(invariants,Ts,Opts0,Opts1),
    close(S).
    
readWutFacts(end_of_file,_,[]) :-
    !.
readWutFacts((H :- C), S,[invariant(H,C)|Ts]) :-
    numbervars((H :- C),0,_),
    read(S,C1),
    readWutFacts(C1,S,Ts).
    
%%% input widening points %%%%
    
load_widenpoints(WPfile,Options0,Options1) :-
    open(WPfile,read,WP),
    read(WP,W),
    get(delaywiden,D,Options0),
    read_widenpoints(W,WP,D,WPs),
    put(widenpoints,WPs,Options0,Options1).
    %collect_wps.
    
read_widenpoints(end_of_file,WP,_,[]) :-
    !,
    close(WP).
read_widenpoints(widening_point(P/N),WP,D,[widening_point(A,D)|WPs]) :-
	functor(A,P,N),
	numbervars(A,0,_),
    read(WP,W1),
    read_widenpoints(W1,WP,D,WPs).
    
    

    
%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Predicate dependency graph
%%%%%%%%%%%%%%%%%%%%%%%%%%%%

standardClauses([predicates(_)|Prog],Cls) :-
	myClauses(Prog,Cls,1).
	
myClauses([Cl|Prog],[clause(H1,Cs0,CJ)|Cls],J) :-
	melt(Cl,clause((H:-B),_Ws)),
	!,
	J1 is J+1,
	atom_number(I,J),
	atom_concat(c,I,CJ),
	atomConstraints(H,H1,Cs0,Cs1),
	conj2List(B,Bs),
	bodyConstraints(Bs,Bs1,Cs1,Bs1),
	numbervars((H1,Cs0),0,_),
	myClauses(Prog,Cls,J1).
myClauses([_|Prog],Cls,J) :- 	% Ignore anything else
	myClauses(Prog,Cls,J).
myClauses([],[],_).

atomConstraints(H,H1,Cs0,Cs1) :-
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
    
bodyConstraints([],[],Cs,Cs).
bodyConstraints([B|Bs],[B|Bs1],Cs0,Cs1) :-
    constraint0(B,_),
    !,
    bodyConstraints(Bs,Bs1,Cs0,Cs1).
bodyConstraints([B|Bs],[B1|Bs1],Cs0,Cs1) :-
    atomConstraints(B,B1,Cs0,Es1),
    bodyConstraints(Bs,Bs1,Es1,Cs1).

dependency_graph(Cls,Es,Vs) :-
    findall(P/N-Q/M, (
                    member(Cl,Cls),
                    melt(Cl,clause(H,Bs,_)),
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
    findall(P/N, (member(clause(H,_,_),Cls),functor(H,P,N)), Vs2),
    append(Vs1,Vs2,Vs).             
    

%%%% Getting and setting options

% get_options/3 provided by Michael Leuschel
get_options([],[],[]).
get_options([X|T],Options,Args) :-
    ( recognised_option(X,Opt,Values) ->
        append(Values, Rest, T),
        RT = Rest,
        Options = [Opt|OT], Args = AT
    ; Options = OT, Args = [X|AT],
      RT = T
    ),
    get_options(RT,OT,AT).


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

set_options(Opts,O1,O13,File,FactFile) :-
    member(programO(File),Opts),
    ( member(verbose,Opts) -> put(verbose,yes,O1,O2)
    ; O2=O1
    ),
    ( member(debug_print,Opts) -> put(debug_print,yes,O2,O3)
    ; O3=O2
    ),
    ( member(singlepoint,Opts) -> put(widenAt,singlepoint,O3,O4)
    ; put(widenAt,allpoints,O3,O4)
    ),
    ( member(widenO(WOutput),Opts) -> put(outputFile,WOutput,O4,O5)
    ; put(outputFile,widencns,O4,O5)
    ),
    ( member(widenF(WFunc),Opts) -> put(widenf,WFunc,O5,O6)
    ; put(widenf,h79,O5,O6)
    ),
    ( member(detectwps(M),Opts) -> put(detectwps,M,O6,O7)
    ; put(detectwps,feedback,O6,O7)
    ),
    ( member(thresholdFile(TFile),Opts) -> put(threshold,TFile,O7,O8)
    ; put(threshold,'$NOTHRESHOLD',O7,O8)
    ),
    ( member(withwut,Opts) -> put(withwut,yes,O8,O9)
    ; put(withwut,nowut,O8,O9)
    ),
    ( member(narrowiterationsO(Nit),Opts) -> 
    		atom_number(Nit,NitN),put(narrowiterations,NitN,O9,O10)
    ; put(narrowiterations,0,O9,O10)
    ),
    ( member(delaywiden(DWit),Opts) -> 
    	atom_number(DWit,DWitN),put(delaywiden,DWitN,O10,O11)
    ; put(delaywiden,0,O10,O11)
    ),
    ( member(widenP(WPoints),Opts) -> put(widenP,WPoints,O11,O12)
    ; put(widenP,widenpoints,O11,O12)
    ),
    ( member(factFile(FactFile),Opts) -> true
    ; true
    ),
    ( member(nowpscalc,Opts) -> put(nowpscalc,yes,O12,O13)
    ; O13=O12
    ).
    
%%%% clean workspace


factFile(Soln,File) :-
    (File=user_output -> Sout=user_output; open(File,write,Sout)),
    writeFacts(Soln,Sout),
    close(Sout).
    
writeFacts([fact(F,H,_)|Soln],Sout) :-  
    ppl_Polyhedron_get_minimized_constraints(H,C),
    numbervars(F,0,_),
    (C=[0=1] -> true; 
      writeq(Sout,F), write(Sout,' :- '), 
      writeq(Sout,C),
      write(Sout,'.'),
      nl(Sout)),
	writeFacts(Soln,Sout).
writeFacts([],_).

% ---------------------------------------------------------------------------
% Messages 

verbose_opts(Opts,Options) :-
    ( member((verbose,yes),Options) -> Opts = ['-v'|Opts1]
    ; Opts = Opts1
    ),
    ( member((debug_print,yes),Options) -> Opts1 = ['-debug-print'|Opts2]
    ; Opts1 = Opts2
    ),
    Opts2 = [].


verbose_message(Xs,Opts) :-
    ( member((verbose,yes),Opts) -> write_list(Xs)
    ; true
    ).

debug_message(Xs,Opts) :-
    ( member((debug_print,yes),Opts) -> write_list(Xs)
    ; true
    ).

write_list([]) :- nl.
write_list([X|Xs]) :- write(X), write_list(Xs).

% Option list handling

get(Prop,Value,Options) :-
	member((Prop,Value),Options),
	!.
	
put(Prop,Value,Opts0,[(Prop,Value)|Opts1]) :-
	select((Prop,_),Opts0,Opts1),
	!.
put(Prop,Value,Opts0,[(Prop,Value)|Opts0]).
	
update(P,V,Opts0,[(P,V)|Opts1]) :-
	select((P,_),Opts0,Opts1).
	

incrementCount(Options0,Options1,J) :-
	get(operatorCount,J1,Options0),
	J is J1+1,
	put(operatorCount,J,Options0,Options1).
