:- module(yices2_sat, [
    yices_sat/2,
    yices_unsat/2,
    yices_model/3,
    yices_model_keepsubst/3,
    true_in_model/2,
    get_value_as_term/3,
    yices_vars/3,
    expr2yices/2,
    yices_declare_var/2
   ], [assertions, isomodes, doccomments, dcg]).

%! \title Higher level interface to Yices SMT solver
%
%  \module
%    See `expr2yices/2` code for the accepted expressions.

%:- use_module(library(format)).
:- use_module(library(lists)).
:- use_module(library(strings)).

:- use_module(ciao_yices(ciao_yices_2)).

% E: a yices expression (see expr2yices/2)
% Vars: list of (V,Tau) where Tau is a yices type
yices_sat(E,Vars) :-
    yices_check_formula(E, Vars, satisfiable).
    
% E: a yices expression (see expr2yices/2)
% Vars: list of (V,Tau) where Tau is a yices type
yices_unsat(E,Vars) :-
    yices_check_formula(E, Vars, unsatisfiable).

yices_check_formula(E,Vars,StatusName) :-
    expr2yices(E,Y),
    declareVars(Vars),
    yices_context(Ctx),
    yices_parse_term(Y,T),
    check_no_error(T),
    yices_assert_formula(Ctx,T,_Status),
    yices_check(Ctx,StatusName0),
    yices_free_context(Ctx),
    StatusName = StatusName0.

% (do not include eliminated variables)
yices_model(E,Vars,M) :-
    yices_model_(E,Vars,0,M).
    
% (may include eliminated variables)
yices_model_keepsubst(E,Vars,M) :-
    yices_model_(E,Vars,1,M).

yices_model_(E,Vars,KeepSubst, M) :-
    expr2yices(E,Y),
    declareVars(Vars),
    yices_context(Ctx), % TODO: Ctx leaked?
    yices_parse_term(Y,T),
    yices_assert_formula(Ctx,T,_Status),
    yices_check(Ctx,StatusName),
    StatusName==satisfiable,
    % (the model should include eliminated variables)
    yices_get_model(Ctx,KeepSubst,M).

    
true_in_model(E,M) :-
    expr2yices(E,Y),
    yices_parse_term(Y,T),
    yices_formula_true_in_model(M,T,Status),
    Status==1.

get_value_as_term(M, E, Term) :-
    expr2yices(E,Y),
    yices_parse_term(Y,T),
    yices_get_value_as_term(M,T,Term).

expr2yices(E,S) :-
    exp_(E,S,[]).
%   format(user_error, "[~w: ~s]~n", [E,S]).
    
exp_([X1,X2|Y]) --> !,
    "(","and ",exp_(X1)," ",exp_([X2|Y]),")".
exp_([false]) --> !, "false".
exp_([X]) --> !, exp_(X).
exp_([]) --> !, "true".
exp_((X;Y)) --> !, "(","or ",exp_(X)," ",exp_(Y),")".
exp_((X,Y)) --> !,
    "(","and ",exp_(X)," ",exp_(Y),")".
exp_((X->Y)) --> !, % TODO: what is this?
    "(","=> ",exp_(X)," ",exp_(Y),")".
exp_(neg(X)) --> !,
    "(","not ",exp_(X),")".
% Equality
exp_((X=Y)) --> !,
    "(","= ",exp_(X)," ",exp_(Y),")".
% Constraints for arrays
% TODO: apply1, update1 avoids temporary variables (is it better?)
exp_(read(F,X,V)) --> !,
    exp_((V = apply1(F,X))).
exp_(write(F,X,V,F2)) --> !,
    exp_((F2 = update1(F,X,V))).
% Constraints for LIA
exp_((X<Y)) --> !,
    "(","< ",exp_(X)," ",exp_(Y),")".
exp_((X>Y)) --> !,
    "(","> ",exp_(X)," ",exp_(Y),")".
exp_((X=<Y)) --> !,
    "(","<= ",exp_(X)," ",exp_(Y),")".
exp_((X>=Y)) --> !,
    "(",">= ",exp_(X)," ",exp_(Y),")".
% (expressions) % TODO: do not merge?
exp_((X*Y)) --> !,
    "(","* ",exp_(X)," ",exp_(Y),")".
exp_((X+Y)) --> !,
    "(","+ ",exp_(X)," ",exp_(Y),")".
exp_((X-Y)) --> !,
    "(","- ",exp_(X)," ",exp_(Y),")".
exp_(-(X)) --> !,
    "(","- ",exp_(X),")".
exp_(xor(X,Y)) --> !,
    "(","xor ",exp_(X)," ",exp_(Y),")".
exp_(apply1(Fun, X)) --> !, % apply to a function1
    "(",exp_(Fun)," ",exp_(X),")".
exp_(update1(Fun, X, Y)) --> !, % update a function1
    "(","update"," ",exp_(Fun)," ","(",exp_(X),")",exp_(Y),")".
exp_('$VAR'(N)) --> !,
    { name(N,I) },
    str("x"||I).
exp_(A) --> { atomic(A) }, !,
    { name(A,S) },
    str(S).
exp_(A) -->
    { throw(error(wrong_expr(A), expr2yices/2)) }.

str(X,S,S0) :- append(X,S0,S).


declareVars([(X,Tau)|Vars]) :- !,
    expr2yices(X,V),
    yices_declare_var(Tau,V),
    declareVars(Vars).
declareVars([]).

yices_declare_var(real, V) :- yices_declare_real(V).
yices_declare_var(int, V) :- yices_declare_int(V).
yices_declare_var(bool, V) :- yices_declare_bool(V).
yices_declare_var(function1(Tau,Range), V) :-
    yices_declare_function1(Tau,Range,V).

check_no_error(S) :-
    ( S<0 -> report_error
    ; true
    ).
    
report_error :-
    yices_error_string(E),
    throw(yices_error(E)).


yices_vars([], _Type, []).
yices_vars([V|Vs], Type, [(V,Type)|VTs]):-
    yices_vars(Vs, Type, VTs).
