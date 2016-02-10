:- module(_, [], [ciaobld(bundlehooks)]).

:- doc(title,  "Bundle Hooks for CHCLibs").

'$builder_hook'(desc_name('CHCLibs')).

% ============================================================================

:- use_module(ciaobld(ciaoc_aux), [build_libs/2]).

'$builder_hook'(build_libraries) :-
	build_libs(chclibs, 'src').

'$builder_hook'(install) :- bundleitem_do(only_global_ins(~chclibs_desc), chclibs, install).

'$builder_hook'(uninstall) :- bundleitem_do(only_global_ins(~chclibs_desc), chclibs, uninstall).

chclibs_desc := [
  lib(chclibs, 'src')
].
