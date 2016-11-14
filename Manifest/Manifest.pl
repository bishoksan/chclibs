:- bundle(chclibs).
version('1.0').
depends([
    core,
    % ciao_ppl, % TODO: still in Ciao
    ciao_yices
]).
alias_paths([
    chclibs = 'src'
]).


