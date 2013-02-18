/*
 * Console.g
 *
 * ANTLR grammar specification for the command-line input 
 * of the interactive console.
 * 
 * @author Christian Simon based on an original work of Stefan Wehr 
 *	(http://proglang.informatik.uni-freiburg.de/teaching/konzepte/2009ss/)
 *
 */


grammar Console;

// uncomment this, if your grammar runs into LL-conflicts
//options {
//	backtrack = true;
//}

@header {
package local.stalin.interactiveconsole;
}

@lexer::header {
package local.stalin.interactiveconsole;
}


/* command tokens */
HELP_T	:  ('help' 
		|  'HELP');
EXIT_T	: ('exit'
		|  'EXIT');
LIST_T	: ('list'
		|  'LIST');
USE_T	: ('use'
		|  'USE');
ON_T	: ('on'
		|  'ON');
SETPRELUDE_T	:	('set prelude'
				|	 'SET PRELUDE');
DELETEMM_T	:	('deletemm'
			|	 'DELETEMM');
LISTMM_T	:	('listmm'
			|	 'LISTMM');
RERUN_T		:	'rerun';
SETRESULTOUTPUT_T	: ('output result to'
					|  'OUTPUT RESULT TO');
					
LOADPREFS_T		: ('load preferences from')
				| ('LOAD PREFERENCES FROM');
				
fragment LETTER     :  ('a'..'z' | 'A'..'Z') ;
fragment DIGIT      :  '0'..'9' ;
// path separator for Win and Unix
fragment PATHSEPARATOR	:	('\/' | '\\');
// what characters are allowed in a filename?
fragment FILECHAR	:	( LETTER | DIGIT | '_' | '-' | ',' | ':' | '.');

NUMBER     : DIGIT+ ;

// very generous file name matching for Unix and Win32
FILE_NAME : PATHSEPARATOR? (FILECHAR PATHSEPARATOR?)+;

WS         :  (' ' | '\t' | '\r' | '\n')+     { skip(); } ;

cmdline returns [Stmt s]
    :	HELP_T
    	{ $s = new HelpStmt();  }
    |	EXIT_T
    	{ $s = new ExitStmt(); }
    |	LIST_T
    	{ $s = new ListStmt(); }
    |	USE_T t=tcd ON_T f=FILE_NAME
    	{ $s = new UseStmt($t.tcd, $f.text); }
    |	SETPRELUDE_T f=FILE_NAME
    	{ $s = new SetPreludeStmt($f.text); }
    |	LISTMM_T
    	{ $s = new ListMMStmt(); }
    |	DELETEMM_T n=NUMBER
    	{ $s = new DeleteMMStmt($n.text); }
    |	RERUN_T
    	{ $s = new RerunStmt(); }
    |	SETRESULTOUTPUT_T f=FILE_NAME
    	{ $s = new SetResultOutputStmt($f.text); }
    |	LOADPREFS_T f=FILE_NAME
    	{ $s = new LoadPrefsStmt($f.text); }
    ;

// toolchain grammar
tcd returns [TC tcd]
	:	'current'
		{ $tcd = new TCcurrent(); }
	|	f=FILE_NAME
		{ $tcd = new TCfile($f.text); }
	|	n = ntcd
		{ $tcd = $n.ntcd; }
	;
	

// descriptor for new toolchain made up of integers 
ntcd returns [TCnew ntcd]
	:	nmb = NUMBER  (next = ntcd)?
		{ $ntcd = new TCPlugin($nmb.text, $next.ntcd); }
	|	'(' sbc = ntcd ')*'  (next = ntcd)?
		{ $ntcd = new TCSubchain($sbc.ntcd, $next.ntcd); }
	;
