:- module(timer_ciao, [start_time/0, end_time/1, end_time/2], [assertions, isomodes, doccomments]).

%! \title Statistics for Ciao
%

% TODO: Add more functionality

:- use_module(library(streams)).
:- use_module(library(write)).
:- use_module(engine(runtime_control), [statistics/2]).

start_time :-
    statistics(runtime,_).

end_time(Message, S) :- 
    statistics(runtime,[_,T1]),
    Time is T1/1000,
    write(S, Message),
    write(S, Time),
    write(S, ' secs.'),
    nl(S).

end_time(S) :-
    end_time('Time: ',S).
