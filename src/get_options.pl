% (included file, needs recognized_option/3)

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

% ---------------------------------------------------------------------------

% Obtain verbosity options from current values in flags/1
verbose_opts(Opts) :-
    ( flag(verbose) -> Opts = ['-v'|Opts1]
    ; Opts = Opts1
    ),
    ( flag(debug_print) -> Opts1 = ['-debug-print'|Opts2]
    ; Opts1 = Opts2
    ),
    Opts2 = [].
