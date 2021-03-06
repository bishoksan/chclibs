:- module(builtins, [sp_builtin/1, builtin/1],
    [assertions, isomodes, doccomments]).

:- use_module(chclibs(common), [prg_theory/1]).

%! \title Builtin table
%
%  \module Fake module table for partially deal with Ciao programs
%
% TODO: Redefine modules for specific theories (linear arithmetic,
%   arrays, etc.) The input language is not Prolog.

sp_builtin(G) :-
    functor(G,F,N),
    builtin_export(_,F,N,_),
    !.
sp_builtin(G) :-
    functor(G,F,N),
    is_module_expanded(F,MP,Module),
    builtin_export(Module,MP,N,_),
    !.
    
is_module_expanded(Goal,PGoal,Module):-
    atom_concat(Module,Post,Goal),
    atom_concat(':',PGoal,Post),!.
    
builtin(G) :-
    functor(G,F,N),
    builtin_export(_,F,N,_).

builtin_export(arrays,read,3,0) :- prg_theory(array). % (fake module for array theories)
builtin_export(arrays,write,4,0) :- prg_theory(array). % (fake module for array theories)
builtin_export(arithmetic,is,2,0) .
builtin_export(arithmetic,<,2,0) .
builtin_export(arithmetic,=<,2,0) .
builtin_export(arithmetic,>,2,0) .
builtin_export(arithmetic,>=,2,0) .
builtin_export(arithmetic,=:=,2,0) .
builtin_export(arithmetic,=\=,2,0) .
builtin_export(arithmetic,arithexpression,1,0) .
builtin_export(atomic_basic,name,2,0) .
builtin_export(atomic_basic,atom_codes,2,0) .
builtin_export(atomic_basic,number_codes,2,0) .
builtin_export(atomic_basic,number_codes,3,0) .
builtin_export(atomic_basic,atom_length,2,0) .
builtin_export(atomic_basic,atom_concat,3,0) .
builtin_export(atomic_basic,sub_atom,4,0) .
builtin_export(attributes,attach_attribute,2,0) .
builtin_export(attributes,get_attribute,2,0) .
builtin_export(attributes,update_attribute,2,0) .
builtin_export(attributes,detach_attribute,1,0) .
builtin_export(basic_props,term,1,0) .
builtin_export(basic_props,int,1,0) .
builtin_export(basic_props,nnegint,1,0) .
builtin_export(basic_props,flt,1,0) .
builtin_export(basic_props,num,1,0) .
builtin_export(basic_props,atm,1,0) .
builtin_export(basic_props,struct,1,0) .
builtin_export(basic_props,gnd,1,0) .
builtin_export(basic_props,constant,1,0) .
builtin_export(basic_props,callable,1,0) .
builtin_export(basic_props,operator_specifier,1,0) .
builtin_export(basic_props,list,1,0) .
builtin_export(basic_props,list,2,list(?,pred(1))) .
builtin_export(basic_props,member,2,0) .
builtin_export(basic_props,sequence,2,sequence(?,pred(1))) .
builtin_export(basic_props,sequence_or_list,2,sequence_or_list(?,pred(1))) .
builtin_export(basic_props,character_code,1,0) .
builtin_export(basic_props,string,1,0) .
builtin_export(basic_props,predname,1,0) .
builtin_export(basic_props,atm_or_atm_list,1,0) .
builtin_export(basic_props,compat,2,compat(?,pred(1))) .
builtin_export(basic_props,iso,1,0) .
builtin_export(basic_props,not_further_inst,2,0) .
builtin_export(basic_props,regtype,1,0) .
builtin_export(basiccontrol,',',2,0) .
builtin_export(basiccontrol,;,2,0) .
builtin_export(basiccontrol,->,2,0) .
builtin_export(basiccontrol,!,0,0) .
builtin_export(basiccontrol,\+,1,0) .
builtin_export(basiccontrol,if,3,0) .
builtin_export(basiccontrol,true,0,0) .
builtin_export(basiccontrol,fail,0,0) .
builtin_export(basiccontrol,repeat,0,0) .
builtin_export(basiccontrol,call,1,call(goal)) .
builtin_export(basiccontrol,srcdbg_spy,6,srcdbg_spy(goal,?,?,?,?,?)) .
builtin_export(data_facts,asserta_fact,1,asserta_fact(fact)) .
builtin_export(data_facts,asserta_fact,2,asserta_fact(fact,?)) .
builtin_export(data_facts,assertz_fact,1,assertz_fact(fact)) .
builtin_export(data_facts,assertz_fact,2,assertz_fact(fact,?)) .
builtin_export(data_facts,current_fact,1,current_fact(fact)) .
builtin_export(data_facts,current_fact,2,current_fact(fact,?)) .
builtin_export(data_facts,retract_fact,1,retract_fact(fact)) .
builtin_export(data_facts,retractall_fact,1,retractall_fact(fact)) .
builtin_export(data_facts,current_fact_nb,1,current_fact_nb(fact)) .
builtin_export(data_facts,retract_fact_nb,1,retract_fact_nb(fact)) .
builtin_export(data_facts,close_predicate,1,close_predicate(fact)) .
builtin_export(data_facts,open_predicate,1,open_predicate(fact)) .
builtin_export(data_facts,set_fact,1,set_fact(fact)) .
builtin_export(data_facts,erase,1,0) .
builtin_export(exceptions,catch,3,catch(goal,?,goal)) .
builtin_export(exceptions,intercept,3,intercept(goal,?,goal)) .
builtin_export(exceptions,throw,1,0) .
builtin_export(exceptions,halt,0,0) .
builtin_export(exceptions,halt,1,0) .
builtin_export(exceptions,abort,0,0) .
builtin_export(io_aux,message,2,0) .
builtin_export(io_aux,message_lns,4,0) .
builtin_export(io_aux,error,1,0) .
builtin_export(io_aux,warning,1,0) .
builtin_export(io_aux,note,1,0) .
builtin_export(io_aux,message,1,0) .
builtin_export(io_aux,debug,1,0) .
builtin_export(io_aux,inform_user,1,0) .
builtin_export(io_aux,display_string,1,0) .
builtin_export(io_aux,display_list,1,0) .
builtin_export(io_aux,display_term,1,0) .
builtin_export(io_basic,get_code,2,0) .
builtin_export(io_basic,get_code,1,0) .
builtin_export(io_basic,get1_code,2,0) .
builtin_export(io_basic,get1_code,1,0) .
builtin_export(io_basic,peek_code,2,0) .
builtin_export(io_basic,peek_code,1,0) .
builtin_export(io_basic,skip_code,2,0) .
builtin_export(io_basic,skip_code,1,0) .
builtin_export(io_basic,put_code,2,0) .
builtin_export(io_basic,put_code,1,0) .
builtin_export(io_basic,nl,1,0) .
builtin_export(io_basic,nl,0,0) .
builtin_export(io_basic,tab,2,0) .
builtin_export(io_basic,tab,1,0) .
builtin_export(io_basic,code_class,2,0) .
builtin_export(io_basic,getct,2,0) .
builtin_export(io_basic,getct1,2,0) .
builtin_export(io_basic,display,2,0) .
builtin_export(io_basic,display,1,0) .
builtin_export(io_basic,displayq,2,0) .
builtin_export(io_basic,displayq,1,0) .
builtin_export(prolog_flags,set_prolog_flag,2,0) .
builtin_export(prolog_flags,current_prolog_flag,2,0) .
builtin_export(prolog_flags,prolog_flag,3,0) .
builtin_export(prolog_flags,push_prolog_flag,2,0) .
builtin_export(prolog_flags,pop_prolog_flag,1,0) .
builtin_export(prolog_flags,prompt,2,0) .
builtin_export(prolog_flags,gc,0,0) .
builtin_export(prolog_flags,nogc,0,0) .
builtin_export(prolog_flags,fileerrors,0,0) .
builtin_export(prolog_flags,nofileerrors,0,0) .
builtin_export(stream_basic,open,3,0) .
builtin_export(stream_basic,close,1,0) .
builtin_export(stream_basic,set_input,1,0) .
builtin_export(stream_basic,current_input,1,0) .
builtin_export(stream_basic,set_output,1,0) .
builtin_export(stream_basic,current_output,1,0) .
builtin_export(stream_basic,character_count,2,0) .
builtin_export(stream_basic,line_count,2,0) .
builtin_export(stream_basic,line_position,2,0) .
builtin_export(stream_basic,flush_output,1,0) .
builtin_export(stream_basic,flush_output,0,0) .
builtin_export(stream_basic,clearerr,1,0) .
builtin_export(stream_basic,current_stream,3,0) .
builtin_export(stream_basic,stream_code,2,0) .
builtin_export(stream_basic,absolute_file_name,2,0) .
builtin_export(stream_basic,absolute_file_name,7,0) .
builtin_export(stream_basic,sourcename,1,0) .
builtin_export(stream_basic,stream,1,0) .
builtin_export(stream_basic,stream_alias,1,0) .
builtin_export(stream_basic,io_mode,1,0) .
builtin_export(system_info,get_arch,1,0) .
builtin_export(system_info,get_os,1,0) .
builtin_export(system_info,this_module,1,this_module(addmodule)) .
builtin_export(system_info,current_module,1,0) .
builtin_export(system_info,ciaolibdir,1,0) .
builtin_export(term_basic,=,2,0) .
builtin_export(term_basic,arg,3,0) .
builtin_export(term_basic,functor,3,0) .
builtin_export(term_basic,=..,2,0) .
builtin_export(term_basic,copy_term,2,0) .
builtin_export(term_basic,'C',3,0) .
builtin_export(term_compare,==,2,0) .
builtin_export(term_compare,\==,2,0) .
builtin_export(term_compare,\=,2,0) .
builtin_export(term_compare,@<,2,0) .
builtin_export(term_compare,@=<,2,0) .
builtin_export(term_compare,@>,2,0) .
builtin_export(term_compare,@>=,2,0) .
builtin_export(term_compare,compare,3,0) .
builtin_export(term_typing,var,1,0) .
builtin_export(term_typing,nonvar,1,0) .
builtin_export(term_typing,atom,1,0) .
builtin_export(term_typing,integer,1,0) .
builtin_export(term_typing,float,1,0) .
builtin_export(term_typing,number,1,0) .
builtin_export(term_typing,atomic,1,0) .
builtin_export(term_typing,ground,1,0) .
builtin_export(term_typing,type,2,0) .
builtin_export(read,read,1,0).
builtin_export(write,write,1,0).
