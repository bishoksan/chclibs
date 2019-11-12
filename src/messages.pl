% ---------------------------------------------------------------------------
% Messages (based on flag/1 options)

verbose_message(Xs) :-
    ( flag(verbose) -> write_list(Xs)
    ; true
    ).

debug_message(Xs) :-
    ( flag(debug_print) -> write_list(Xs)
    ; true
    ).

write_list([]) :- nl.
write_list([X|Xs]) :- write(X), write_list(Xs).

