package de.uni_freiburg.informatik.ultimate.LTL2aut;

import java_cup.runtime.*;

%%

%cupsym symbolsAP
%class LexerAP
%unicode
%cup
%cupdebug
%line
%column
%public


%{
  private Symbol symbol(int type) {
    return new Symbol(type, yyline, yycolumn);
  }
  private Symbol symbol(int type, Object value) {
    return new Symbol(type, yyline, yycolumn, value);
  }
    private Symbol symbol(int type, String value) {
    return new Symbol(type, yyline, yycolumn, value);
  }
  
      private Symbol symbol(int type, int value) {
    return new Symbol(type, yyline, yycolumn, value);
  }
%} 

LineTerminator = \r|\n|\r\n
InputCharacter = [^\r\n]
WhiteSpace     = {LineTerminator} | [ \t\f]

/* comments */
Identifier = [a-zA-Z][a-zA-Z0-9_-]*
Int = [0-9]+
 
%%

/**
 * LEXICAL RULES:
 */

<YYINITIAL>{ 
	":"				{ return symbol(symbolsAP.COLON); }

	"("				{ return symbol(symbolsAP.LPAR); }
	")"				{ return symbol(symbolsAP.RPAR); }
	
	"+"				{ return symbol(symbolsAP.PLUS); }
	"-"				{ return symbol(symbolsAP.MINUS); }
	"*"				{ return symbol(symbolsAP.TIMES); }

	"="				{ return symbol(symbolsAP.EQUALS); }
	">"				{ return symbol(symbolsAP.GREATER); }
	">="			{ return symbol(symbolsAP.GEQ); }
	
	"true"			{ return symbol(symbolsAP.TRUE); }
	"false"			{ return symbol(symbolsAP.FALSE); }

	
	{Int}			{ return symbol(symbolsAP.INT, Integer.parseInt(yytext())); }
	{WhiteSpace}    { /* ignore */ }
	
	{Identifier}    { return symbol(symbolsAP.NAME, yytext()); }

	

 }

 
 
 
 
 
 
 
 
 
 
 
 
 
 