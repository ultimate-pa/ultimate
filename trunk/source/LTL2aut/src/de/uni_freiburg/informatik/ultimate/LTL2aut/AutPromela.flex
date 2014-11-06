package de.uni_freiburg.informatik.ultimate.ltl2aut;

import java_cup.runtime.*;

%%

%cupsym Symbols
%class Lexer
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

/* comments */
Comment = {TraditionalComment} | {EndOfLineComment} | {DocumentationComment}

TraditionalComment   = "/*" [^*] ~"*/" | "/*" "*"+ "/"
EndOfLineComment     = "//" {InputCharacter}* {LineTerminator}
DocumentationComment = "/**" {CommentContent} "*"+ "/"
CommentContent       = ( [^*] | \*+ [^/*] )*
 
%%

/**
 * LEXICAL RULES:
 */

<YYINITIAL>{ 
	"never"  		{ return symbol(Symbols.NEVER); }
	"{"    			{ return symbol(Symbols.LCB); }
	"}"    			{ return symbol(Symbols.RCB); }
	"if" 	   		{ return symbol(Symbols.IF); }
	"fi" 			{ return symbol(Symbols.FI); }
	"skip"			{ return symbol(Symbols.SKIP); }
	"goto"			{ return symbol(Symbols.GOTO); }
	"->"			{ return symbol(Symbols.TO); }
	";"				{ return symbol(Symbols.SEMICOLON); }
	":"				{ return symbol(Symbols.COLON); }
	
	"&&"			{ return symbol(Symbols.AND); }
	"||"			{ return symbol(Symbols.OR); }
	"!"				{ return symbol(Symbols.NOT); }

	"("				{ return symbol(Symbols.LPAR); }
	")"				{ return symbol(Symbols.RPAR); }
	
	"1"				{ return symbol(Symbols.TRUE); }
	
	{WhiteSpace}    { /* ignore */ }
	
	{Identifier}    { return symbol(Symbols.NAME, yytext()); }
	{Comment}		{ /* ignore */ }

	

 } 
 