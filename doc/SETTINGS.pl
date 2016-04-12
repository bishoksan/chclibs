:- module(_, [], [lpdoclib(doccfg)]).

%! \title Configuration for chclibs manual
%  \author Jose F. Morales

filepath := '../src'.

doc_structure := 'chclibs_doc'-[
	'balanced_tree',
	'builtins',
	'canonical',
	'common',
	'cpascc',
	'duplVar',
	'flatnames',
	% 'get_options',
	'input_ppl',
	'input_ppl_clausenum',
	'interpolant',
	'lcm',
	'linearize',
	'load_simple',
	'myterms',
	'normalize_constraints',
	'ppl_ops',
	'qa',
	'readprog',
	'scc',
	'setops',
	'thresholds1',
	'timer_ciao',
	'wto',
	'yices2_sat'].

