:- module(_, [], [lpdoclib(doccfg)]).

%! \title Configuration for chclibs manual
%  \author Jose F. Morales

filepath := '../src'.

doc_structure := 'chclibs_doc'-[
	% Transformations and analysis
	'cpascc',
	'qa',
	'scc',
	'thresholds1',
	'wto',
	'linearize',
	% Program readers, writers, and internal representation
	'load_simple',
	'input_ppl',
	'input_ppl_clausenum',
	'readprog',
	'builtins',
	% Program internal representation
	'canonical',
	'myterms',
	'flatnames',
	% Solvers
	'ppl_ops',
	'yices2_sat',
	'interpolant'-[
	  'normalize_constraints',
	  'lcm'
	],
	% Auxiliary, data structures, etc.
	% 'get_options',
	'common',
	'balanced_tree',
	'setops',
	'timer_ciao'].

docformat := html.
