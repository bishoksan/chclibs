:- module(_, [], [ciaobld(bundlehooks)]).

:- doc(title, "Bundle Hooks for CHCLibs").

'$builder_hook'(bundle_def([
  lib('src'),
  manual('chclibs', [main='doc/SETTINGS.pl'])
])).
