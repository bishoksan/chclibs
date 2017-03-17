:- bundle(chclibs).
version('1.0').
depends([
    core,
    'github.com/ciao-lang/ciao_ppl',
    'github.com/jfmc/ciao_yices'
]).
alias_paths([
    chclibs = 'src'
]).
lib('src').
manual('chclibs', [main='doc/SETTINGS.pl']).


