
package de.uni_freiburg.informatik.ultimate.crocotta.parser;
import com.github.jhoenicke.javacup.runtime.Symbol;

%%

%class CrocLexer
%public
%unicode
%implements com.github.jhoenicke.javacup.runtime.Scanner
%type com.github.jhoenicke.javacup.runtime.Symbol
%function next_token
%line
%column


%{
  private CrocSymbolFactory mSymFactory = new CrocSymbolFactory();
  
  private Symbol symbol(int type) {
    return mSymFactory.newSymbol(yytext(), type, yyline+1, yycolumn, yyline+1, yycolumn+yylength());
  }
  private Symbol symbol(int type, String value) {
    return mSymFactory.newSymbol(value, type, yyline+1, yycolumn, yyline+1, yycolumn+yylength(), value);
  }
%}



LineTerminator = \r|\n|\r\n
InputCharacter = [^\r\n]
WhiteSpace     = {LineTerminator} | [ \t\f]

/* comments */
Comment = {TraditionalComment} | {EndOfLineComment}

TraditionalComment   = "/*" ~"*/" 
EndOfLineComment     = "//" {InputCharacter}* {LineTerminator}?
BoogieLetter = [:letter:] | ['~#$\^_?\\]
BoogieLetterDigit = {BoogieLetter} | [:digit:]
Identifier = {BoogieLetter} {BoogieLetterDigit}*

DecIntegerLiteral = 0 | [1-9][0-9]*
RealIntegerLiteral = {DecIntegerLiteral} "." [0-9]+

%%

<YYINITIAL>  {
  "("                    { return symbol(CrocSymbols.LPAR); }
  ")"                    { return symbol(CrocSymbols.RPAR); }

  /* Predefined Symbols */
  "="                    { return symbol(CrocSymbols.EQUALS, yytext()); }
  "pair"                 { return symbol(CrocSymbols.PAIR, yytext()); }
  "concat"               { return symbol(CrocSymbols.CONCAT, yytext()); }
  "union"                { return symbol(CrocSymbols.UNION, yytext()); }
  "isect"                { return symbol(CrocSymbols.ISECT, yytext()); }
  "constraints"          { return symbol(CrocSymbols.CONSTRAINTS, yytext()); }
  "ev"                   { return symbol(CrocSymbols.EV, yytext()); }


  /* Predefined Keywords */
  /*":named"               { return symbol(CrocSymbols.CNAMED, yytext()); }*/

  /* Other Symbols */
  "("             { return symbol(CrocSymbols.LPAR); }
  ")"             { return symbol(CrocSymbols.RPAR); }

  "\""            { return symbol(CrocSymbols.QUOTE); }

  /* Numbers, Ids and Strings */

  /* identifiers */ 
  {Identifier}                   { return symbol(CrocSymbols.ID, yytext().intern()); }
 

  /* comments */
  {Comment}                      { /* ignore */ }
 
  /* whitespace */
  {WhiteSpace}                   { /* ignore */ }
}


/* error fallback */
.|\n                             { return symbol(CrocSymbols.error, yytext()); }

<<EOF>>                          { return symbol(CrocSymbols.EOF); }