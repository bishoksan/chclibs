:- bundle(chclibs).
version('1.0').
depends([
    core-[version>='1.18'],
    'github.com/ciao-lang/ciao_ppl',
    'github.com/jfmc/ciao_yices'
]).
alias_paths([
    chclibs = 'src'
]).

cmd('chclibs-tpmsg', [main='src/tpmsg']).
cmd('chclibs-qa', [main='src/qa']).
cmd('chclibs-thresholds1', [main='src/thresholds1']).
cmd('chclibs-unfoldForward', [main='src/unfoldForward']).
cmd('chclibs-raf', [main='src/raf']).
cmd('chclibs-far', [main='src/far']).
cmd('chclibs-cpascc', [main='src/cpascc']).

lib('src').

manual('chclibs', [main='doc/SETTINGS.pl']).


