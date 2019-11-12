%:- module(lcm, [transf/2], [assertions, isomodes, doccomments]).
:- module(lcm, _, [assertions, isomodes, doccomments]).


:- use_module(library(lists)).

% test:-
%       numbervars(C, 0, _),
%       transf(-(1/9)*C=< -(1), R),
%       write(R).

lcmList([],1).
lcmList([X],X).
lcmList([X,Y|Xs],N) :-
    lcmList([Y|Xs],M),
    lcm(X,M,N).

gcd(X,X,X).
gcd(X,Y,Z) :-
    X > Y,
    X1 is X-Y,
    gcd(X1,Y,Z).
gcd(X,Y,Z) :-
    Y > X,
    Y1 is Y-X,
    gcd(X,Y1,Z).

lcm(X,Y,Z) :-
    gcd(X,Y,U),
    Z is X*(Y//U).
    
coeffs(C*'$VAR'(_),[C]) :-
    !.
coeffs('$VAR'(_)*C,[C]):-
    !.
coeffs('$VAR'(_),[]):-
    !.
coeffs(C,[C]):-
    rationalNum(C),
    !.
coeffs(Expr,Cs) :-
    Expr =.. [Op|Ts],
    member(Op, ['+','-','>','<','>=','=<','=','is']),
    coeffList(Ts,Cs).
    
coeffList([],[]).
coeffList([X|Xs],Cs) :-
    coeffs(X,C1),
    coeffList(Xs,Cs1),
    append(C1,Cs1,Cs).
    
    
rationalNum(C) :-
    number(C),
    !.
rationalNum(C1/C2) :-
    number(C1),
    number(C2),
    !.
rationalNum(-(C)) :-
    number(C),
    !.
    

transf(C1,C2) :-
    coeffs(C1,Cs),
    denominators(Cs,Ds),
    lcmList(Ds,LCM),
    normalizeCoeffs(C1,LCM,C2).
    
normalizeCoeffs(C*'$VAR'(K),LCM,C1*'$VAR'(K)) :-
    !,
    ratVal(C,N,D),
    C1 is (N*LCM)//D.
normalizeCoeffs('$VAR'(K)*C,LCM,C1*'$VAR'(K)) :-
    !,
    ratVal(C,N,D),
    C1 is (N*LCM)//D.
normalizeCoeffs('$VAR'(K),LCM,LCM*'$VAR'(K)):-
    !.
normalizeCoeffs(C,LCM,C1):-
    rationalNum(C),
    !,
    ratVal(C,N,D),
    C1 is (N*LCM)//D.
normalizeCoeffs(Expr1,LCM,Expr2) :-
    Expr1 =.. [Op|Ts],
    member(Op, ['+','-','>','<','>=','=<','=','is']),
    normalizeCoeffList(Ts,LCM,Ts1),
    Expr2 =.. [Op|Ts1].
    
normalizeCoeffList([],_,[]).
normalizeCoeffList([T|Ts],LCM,[T1|Ts1]) :-
    normalizeCoeffs(T,LCM,T1),
    normalizeCoeffList(Ts,LCM,Ts1).

denominators([X|Xs],[D|Ds]) :-
    ratVal(X,_,D),
    denominators(Xs,Ds).
denominators([],[]).

ratVal(-(C1/C2),-C1,C2) :-
    !.
ratVal(C1/C2,C1,C2) :-
    !.
ratVal(-(C),-C,1).
ratVal(C,C,1).

    
    

