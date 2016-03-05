% Manifest file for CHCLibs
bundle_name(chclibs).
bundle_packname('CHCLibs').
bundle_requires([
    core,
    % ciao_ppl, % TODO: still in Ciao
    ciao_yices
]).
bundle_alias_paths([
    chclibs = 'src'
]).


