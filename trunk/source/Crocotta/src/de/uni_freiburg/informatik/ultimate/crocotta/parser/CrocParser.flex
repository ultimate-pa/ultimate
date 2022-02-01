/*
 * Copyright (C) 2018 Eric Koskinen
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
 *
 * This file is part of the ULTIMATE Crocotta plug-in.
 *
 * The ULTIMATE Crocotta plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Crocotta plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Crocotta plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Crocotta plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Crocotta plug-in grant you additional permission
 * to convey the resulting work.
 */

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
  "<="                   { return symbol(CrocSymbols.INCLUSION, yytext()); }
  "pair"                 { return symbol(CrocSymbols.PAIR, yytext()); }
  "concat"               { return symbol(CrocSymbols.CONCAT, yytext()); }
  "union"                { return symbol(CrocSymbols.UNION, yytext()); }
  "isect"                { return symbol(CrocSymbols.ISECT, yytext()); }
//  "set"                  { return symbol(CrocSymbols.SET, yytext()); }
  "constraints"          { return symbol(CrocSymbols.CONSTRAINTS, yytext()); }
//  "ev"                   { return symbol(CrocSymbols.EV, yytext()); }


  /* Predefined Keywords */
  /*":named"               { return symbol(CrocSymbols.CNAMED, yytext()); }*/

  /* Other Symbols */
  "("             { return symbol(CrocSymbols.LPAR); }
  ")"             { return symbol(CrocSymbols.RPAR); }
  "["             { return symbol(CrocSymbols.LBRAK); }
  "]"             { return symbol(CrocSymbols.RBRAK); }

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
