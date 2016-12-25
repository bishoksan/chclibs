:- bundle(chclibs).
version('1.0').
depends([
    core,
    % ciao_ppl, % TODO: still in Ciao
    'github.com/jfmc/ciao_yices'
]).
alias_paths([
    chclibs = 'src'
]).
lib('src').
manual('chclibs', [main='doc/SETTINGS.pl']).


