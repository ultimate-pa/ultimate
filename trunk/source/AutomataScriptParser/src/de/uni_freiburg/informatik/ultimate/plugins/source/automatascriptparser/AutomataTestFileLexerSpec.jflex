/* Author: Betim Musa
   Date: 25.11.2012
   This file is the specification for the Automata TestFile Scanner */

package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser;
import java_cup.runtime.*;

/* ------------------------Macro Declarations  ---------------------- */ 
%%

%public
%class Lexer

%line
%column

%cup
%cupdebug

%{   
    StringBuffer string = new StringBuffer();
    /* To create a new java_cup.runtime.Symbol with information about
       the current token, the token will have no value in this
       case. */
    private Symbol symbol(int type) {
        return new Symbol(type, yyline, yycolumn);
    }
    
    /* Also creates a new java_cup.runtime.Symbol with information
       about the current token, but this object has a value. */
    private Symbol symbol(int type, Object value) {
        return new Symbol(type, yyline, yycolumn, value);
    }

    public String getLastToken(int sym) {
      return getTokenName(sym);
    }
%}

/* Some useful character classes */
LineTerminator = \r|\n|\r\n

InputCharacter = [^\r\n]

WhiteSpace = {LineTerminator} | [ \t\f]

/* comments */
/* traditional comment */
/* // line comment */
Comment = {TraditionalComment} | {EndOfLineComment}

TraditionalComment = "/*" [^*] ~"*/" | "/*" "*"+ "/"
EndOfLineComment = "//" {InputCharacter}* {LineTerminator}?

/* identifiers */
Identifier = [a-zA-Z_][a-zA-Z0-9]*

/* integer literals */
IntegerLiteral = 0 | [1-9][0-9]*

/* string and character literals */
StringCharacter = [^\r\n\"\\]

%state STRING
%%

/* ------------------------Lexical Rules Section---------------------- */

<YYINITIAL> {
  /* keywords */
  "boolean"                      { return symbol(sym.BOOLEAN); }
  "break"                        { return symbol(sym.BREAK); }
  "continue"                     { return symbol(sym.CONTINUE); }
  "else"                         { return symbol(sym.ELSE); }
  "for"                          { return symbol(sym.FOR); }
  "int"                          { return symbol(sym.INT); }
  "if"                           { return symbol(sym.IF); }
  "return"                       { return symbol(sym.RETURN); }
  "while"                        { return symbol(sym.WHILE); }
  
  /* keywords for Words */
  "nw"                           { return symbol(sym.NESTED_WORD); }
  "nlw"                          { return symbol(sym.NESTED_LASSO_WORD); }

  /* keywords for AutomataDefinitionFile */
  "nwa"                         { return symbol(sym.NESTEDWORD_AUTOMATA); }
  "net"                         { return symbol(sym.PETRINET_AUTOMATA); }
  "alphabet"                    { return symbol(sym.ALPHABET); }
  "callAlphabet"                { return symbol(sym.CALL_ALPHABET); }
  "internalAlphabet"            { return symbol(sym.INTERNAL_ALPHABET); }
  "returnAlphabet"              { return symbol(sym.RETURN_ALPHABET); }
  "states"                      { return symbol(sym.STATES); }
  "initialStates"               { return symbol(sym.INITIAL_STATES); }
  "finalStates"                 { return symbol(sym.FINAL_STATES); }
  "callTransitions"             { return symbol(sym.CALL_TRANSITIONS); }
  "internalTransitions"         { return symbol(sym.INTERNAL_TRANSITIONS); }
  "returnTransitions"           { return symbol(sym.RETURN_TRANSITIONS); }
  "places"                      { return symbol(sym.PLACES); }

  // Net transitions  
  "transitions"                     { return symbol(sym.NET_TRANSITIONS); }
  "initialMarking"                  { return symbol(sym.INITIAL_MARKINGS); }
  "acceptingMarkings"               { return symbol(sym.ACCEPTING_MARKINGS); }
  "acceptingPlaces"                 { return symbol(sym.ACCEPTING_PLACES); }
  /* boolean literals */
  "true"                         { return symbol(sym.BOOLEAN_LITERAL, new Boolean(true)); }
  "false"                        { return symbol(sym.BOOLEAN_LITERAL, new Boolean(false)); }
  

  /* separators */
  "("                            { return symbol(sym.LPAREN); }
  ")"                            { return symbol(sym.RPAREN); }
  "{"                            { return symbol(sym.LBRACE); }
  "}"                            { return symbol(sym.RBRACE); }
  "["                            { return symbol(sym.LBRACK); }
  "]"                            { return symbol(sym.RBRACK); }
  ";"                            { return symbol(sym.SEMICOLON); }
  ","                            { return symbol(sym.COMMA); }
  "."                            { return symbol(sym.DOT); }


  /* operators */
  "="                            { return symbol(sym.EQ); }
  ">"                            { return symbol(sym.GT); }
  "<"                            { return symbol(sym.LT); }
  "!"                            { return symbol(sym.NOT); }
  "?"                            { return symbol(sym.QUESTION); }
  ":"                            { return symbol(sym.COLON); }
  "=="                           { return symbol(sym.EQEQ); }
  "<="                           { return symbol(sym.LTEQ); }
  ">="                           { return symbol(sym.GTEQ); }
  "!="                           { return symbol(sym.NOTEQ); }
  "&&"                           { return symbol(sym.ANDAND); }
  "||"                           { return symbol(sym.OROR); }
  "++"                           { return symbol(sym.PLUSPLUS); }
  "--"                           { return symbol(sym.MINUSMINUS); }
  "+"                            { return symbol(sym.PLUS); }
  "-"                            { return symbol(sym.MINUS); }
  "*"                            { return symbol(sym.MULT); }
  "/"                            { return symbol(sym.DIV); }
  "+="                           { return symbol(sym.PLUSEQ); }
  "-="                           { return symbol(sym.MINUSEQ); }
  "*="                           { return symbol(sym.MULTEQ); }
  "/="                           { return symbol(sym.DIVEQ); }

  /* string literal */
  \"                             { yybegin(STRING); string.setLength(0); }

  /* numeric literals */
  {IntegerLiteral}               { return symbol(sym.INTEGER_LITERAL, new Integer(yytext())); }


  /* comments */
  {Comment}                      { /* ignore */ }

  /* whitespace */
  {WhiteSpace}                   { /* ignore */ }

  /* identifiers */ 
  {Identifier}                   { return symbol(sym.IDENTIFIER, yytext()); }  

}
<STRING> {
  \"                             { yybegin(YYINITIAL); return symbol(sym.IDENTIFIER, string.toString()); }
  
  {StringCharacter}+             { string.append( yytext() ); }
  
  /* escape sequences */
  "\\b"                          { string.append( '\b' ); }
  "\\t"                          { string.append( '\t' ); }
  "\\n"                          { string.append( '\n' ); }
  "\\f"                          { string.append( '\f' ); }
  "\\r"                          { string.append( '\r' ); }
  "\\\""                         { string.append( '\"' ); }
  "\\'"                          { string.append( '\'' ); }
  "\\\\"                         { string.append( '\\' ); }
  
  /* error cases */ /* (Betim): No error, because paths can have '\' followed by an arbitrary   character. */
  \\.                            { /*throw new RuntimeException("Illegal escape sequence   \""+yytext()+"\""); */}
 
  {LineTerminator}               { throw new RuntimeException("Unterminated string at end of line"); }
}

/* error fallback */
.|\n                             { throw new RuntimeException("ErrorFallback: Illegal character \""+yytext()+ "\" at line "+(yyline + 1) + ", column "+( yycolumn + 1)); }
/* EndOfFile */
<<EOF>>                          { return symbol(sym.EOF); }
