package de.uni_freiburg.informatik.ultimate.LTL2aut;

import java_cup.runtime.*;

%%

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
	"never"  		{ return symbol(sym.NEVER); }
	"{"    			{ return symbol(sym.LCB); }
	"}"    			{ return symbol(sym.RCB); }
	"if" 	   		{ return symbol(sym.IF); }
	"fi" 			{ return symbol(sym.FI); }
	"skip"			{ return symbol(sym.SKIP); }
	"goto"			{ return symbol(sym.GOTO); }
	"->"			{ return symbol(sym.TO); }
	";"				{ return symbol(sym.SEMICOLON); }
	":"				{ return symbol(sym.COLON); }
	
	"&&"			{ return symbol(sym.AND); }
	"||"			{ return symbol(sym.OR); }
	"!"				{ return symbol(sym.NOT); }

	"("				{ return symbol(sym.LPAR); }
	")"				{ return symbol(sym.RPAR); }
	
	"1"				{ return symbol(sym.TRUE); }
	
	{WhiteSpace}    { /* ignore */ }
	
	{Identifier}    { return symbol(sym.NAME, yytext()); }
	{Comment}		{ /* ignore */ }

	

 }

 
 
 
 
 
 
 
 
 
 
 
 
 
 