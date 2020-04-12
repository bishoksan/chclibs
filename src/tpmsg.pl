:- module(tpmsg,_,[dynamic]).

:- use_module(chclibs(common)).
:- use_module(chclibs(canonical)).
:- use_module(chclibs(builtins)).
:- use_module(library(terms_check)).
:- use_module(chclibs(timer_ciao)).
:- use_module(chclibs(program_loader)).
:- use_module(chclibs(scc)).

:- use_module(library(lists)).
:- use_module(library(streams)).
:- use_module(library(write)).
:- use_module(library(aggregates)).

:- dynamic flag/1.
:- dynamic currentflag/1.
:- dynamic nextflag/1.
:- dynamic operatorcount/1.
:- dynamic newfact/1.
:- dynamic oldfact/1.

%% tpmsg - computes an over-approximation of the minimal model
%% Domain is the lattice of atoms
%% Least upper bound of A and B is the most specific generalisation of A and B
		
main(ArgV) :-
    get_options(ArgV,Options,_),
    cleanWorkspace,
    set_options(Options,File,FactFile),
    verbose_write(['Starting analysis ...', File]),
    initialise,
    %start_time,
    load_file(File),
    dependency_graph(Es,Vs),
    scc_graph(Es,Vs,G),
    iterate(G),
    %end_time(user_output),
    verbose_write(['Analysis complete',File]),
    !,
    factFile(FactFile).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Iterate solves each component 
% recursive components involve iterative fixpoint
% non-recursive components solved in one step.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

iterate([(non_recursive,P)|SCCs]) :-
    verbose_write(['Non-recursive component ',P]),
    ( flag(first) -> true ; assert(flag(first)) ),
    non_recursive_scc(P),
    iterate(SCCs).
iterate([(recursive,Ps)|SCCs]) :-
    verbose_write(['Recursive component ',Ps]),
    ( flag(first) -> true ; assert(flag(first)) ),
    recursive_scc(Ps),
    iterate(SCCs).
iterate([]).

non_recursive_scc(P) :-
    msg_operation(P),
    retract(operatorcount(X)),
    Y is X + 1,
    assert(operatorcount(Y)),
    verbose_write(['-',X]),
    newoldfacts,
    switch_flags.

recursive_scc(Ps) :-
    msg_operation(Ps),
    retract(operatorcount(X)),
    Y is X + 1,
    assert(operatorcount(Y)),
    verbose_write(['-',X]),
    retractall(flag(first)),
    fail.
recursive_scc(Ps) :-
    newoldfacts,
    not_converged, 
    !,
    switch_flags,
    recursive_scc(Ps).
recursive_scc(_).

not_converged :-
    nextflag(_).

msg_operation(Ps) :-
    member(P/N,Ps),
    functor(H,P,N),
    my_clause(H,B,_),
    operator(H,B),
    fail.
msg_operation(_).

operator(Head,B):-
    ( changed(B) -> true ; flag(first) ),
    prove(B),
    record(Head).

changed(Bs) :- 
    member(B,Bs),
    isflagset(B),
    !.

prove([]).
prove([X=Y|Bs]):-
    !,
    X=Y,
    prove(Bs).
prove([B|Bs]):-
    builtin(B),
    !,
    prove(Bs).
prove([B|Bs]):-
    getoldfact(B),
    prove(Bs).


%%%%%%%%%%%%%%%%%
%  new/old facts
%%%%%%%%%%%%%%%%%

switch_flags :-
    retractall(currentflag(_/_)),
    retract(nextflag(F/N)),
    assert(currentflag(F/N)),
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
    ; assert(nextflag(Fn/N))
    ).

%% assert the upper bound of the newly derived fact with any existing facts
%% with the same predicate name
%% Upper bound is the msg operation

record(F) :-
    cond_assert(F).

cond_assert(F):-
    \+ existingSubsumingFact(F),
    (getExistingFact(F,F1) -> true; F1=F),
    most_specific_generalization(F1,F,F2),
    numbervars(F2,0,_),
    assert(newfact(F2)),
    raise_flag(F).

existingSubsumingFact(F) :-
    functor(F,P,N),
    functor(F1,P,N),
    fact(F1),
    melt(F1,F2),
    subsumes_term(F2,F).

getExistingFact(F,F2) :-
    functor(F,P,N),
    functor(F1,P,N),
    fact(F1),
    melt(F1,F2).

getoldfact(B) :-
    functor(B,F,N),
    functor(B1,F,N),
    oldfact(B1),
    melt(B1,B).

fact(X) :-
    newfact(X),
    !.
fact(X) :-
    oldfact(X).

newoldfacts :-
    retract(newfact(F)),
    functor(F,P,N),
    functor(F1,P,N),
    retractall(oldfact(F1)),
    assert(oldfact(F)),
    fail.
newoldfacts.


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
    ), Es),
    findall(A, (
        member(X-Y,Es),
        (A=X; A=Y)
    ), Vs1),
    findall(P/N, (my_clause(H,_,_),functor(H,P,N)), Vs2),
    append(Vs1,Vs2,Vs).	

%%%% Getting and setting options

% get_options/3 provided by Michael Leuschel
get_options([],[],[]).
get_options([X|T],Options,Args) :-
    ( recognised_option(X,Opt,Values) ->
        append(Values, Rest, T),
        RT = Rest,
        Options = [Opt|OT], Args = AT
    ; Options = OT,
      Args = [X|AT],
      RT = T
    ),
    get_options(RT,OT,AT).

recognised_option('-prg',programO(R),[R]).
recognised_option('-v',verbose,[]).
recognised_option('-o',factFile(F),[F]).

set_options(Options,File,FactFile) :-
    member(programO(File),Options),
    ( member(verbose,Options) -> assert(flag(verbose))
    ; retractall(flag(verbose))
    ),
    ( member(factFile(FactFile),Options) -> true
    ; FactFile = user_output
    ).

%%%% initialise and clean workspace

initialise :-
    assert(operatorcount(0)),
    assert(flag(first)).

cleanWorkspace :-
    retractall(newfact(_)),
    retractall(oldfact(_)),
    retractall(flag(_)),
    retractall(currentflag(_)),
    retractall(nextflag(_)),
    retractall(operatorcount(_)).

verbose_write(Xs) :-
    ( flag(verbose) ->
        verbose_write_list(Xs)
    ; true
    ).

verbose_write_list([]) :-
    nl.
verbose_write_list([X|Xs]) :-
    write(X),
    verbose_write_list(Xs).

factFile(File) :-
    ( File = user_output -> 
        Sout = user_output
    ; open(File,write,Sout)
    ),
    ( oldfact(F),
      numbervars(F,0,_),
      writeq(Sout,F),
      write(Sout,'.'),
      nl(Sout),
      fail
    ; close(Sout)
    ).
