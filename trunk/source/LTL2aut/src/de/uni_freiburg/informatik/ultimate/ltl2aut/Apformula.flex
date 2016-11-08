package de.uni_freiburg.informatik.ultimate.ltl2aut;

import com.github.jhoenicke.javacup.runtime.*;

%%

%class LexerAP
%unicode
%implements com.github.jhoenicke.javacup.runtime.Scanner
%type com.github.jhoenicke.javacup.runtime.Symbol
%function next_token
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

Identifier = [a-zA-Z~][a-zA-Z0-9_-~#]*
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
	"/"				{ return symbol(SymbolsAP.DIVIDE); }

	"="				{ return symbol(SymbolsAP.EQUALS); }
	">"				{ return symbol(SymbolsAP.GREATER); }
	">="			{ return symbol(SymbolsAP.GEQ); }
	
	"true"			{ return symbol(SymbolsAP.TRUE); }
	"false"			{ return symbol(SymbolsAP.FALSE); }

	
	{Int}			{ return symbol(SymbolsAP.INT, Integer.parseInt(yytext())); }
	{WhiteSpace}    { /* ignore */ }
	
	{Identifier}    { return symbol(SymbolsAP.NAME, yytext()); }

	

 }
<<EOF>>                          { return symbol(SymbolsAP.EOF); }
 