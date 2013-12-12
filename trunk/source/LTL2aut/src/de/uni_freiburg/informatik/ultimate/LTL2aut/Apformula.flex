package de.uni_freiburg.informatik.ultimate.LTL2aut;

import java_cup.runtime.*;

%%

%cupsym SymbolsAP
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

Identifier = [a-zA-Z~][a-zA-Z0-9_-~]*
Int = [0-9]+
 
%%

/**
 * LEXICAL RULES:
 */

<YYINITIAL>{ 
	":"				{ return symbol(SymbolsAP.COLON); }

	"("				{ return symbol(SymbolsAP.LPAR); }
	")"				{ return symbol(SymbolsAP.RPAR); }
	
	"+"				{ return symbol(SymbolsAP.PLUS); }
	"-"				{ return symbol(SymbolsAP.MINUS); }
	"*"				{ return symbol(SymbolsAP.TIMES); }

	"="				{ return symbol(SymbolsAP.EQUALS); }
	">"				{ return symbol(SymbolsAP.GREATER); }
	">="			{ return symbol(SymbolsAP.GEQ); }
	
	"true"			{ return symbol(SymbolsAP.TRUE); }
	"false"			{ return symbol(SymbolsAP.FALSE); }

	
	{Int}			{ return symbol(SymbolsAP.INT, Integer.parseInt(yytext())); }
	{WhiteSpace}    { /* ignore */ }
	
	{Identifier}    { return symbol(SymbolsAP.NAME, yytext()); }

	

 }

 
 
 
 
 
 
 
 
 
 
 
 
 
 