package de.uni_freiburg.informatik.ultimate.eca.parser.lexer.generated;

import com.github.jhoenicke.javacup.runtime.Symbol;
import com.github.jhoenicke.javacup.runtime.SimpleSymbolFactory;
import de.uni_freiburg.informatik.ultimate.eca.parser.cup.generated.EcaSymbols;

%%

%class EcaLexer
%public
%unicode
%implements com.github.jhoenicke.javacup.runtime.Scanner
%type com.github.jhoenicke.javacup.runtime.Symbol
%function next_token
%line
%column

%{
    private final SimpleSymbolFactory mSymbols = new SimpleSymbolFactory();

    private Symbol symbol(final int kind) {
        return mSymbols.newSymbol(yytext(), kind,
                yyline + 1, yycolumn, yyline + 1, yycolumn + yylength());
    }

    private Symbol symbol(final int kind, final String value) {
        return mSymbols.newSymbol(yytext(), kind,
                yyline + 1, yycolumn, yyline + 1, yycolumn + yylength(), value);
    }
%}

LineTerminator = \r\n|\r|\n
WhiteSpace = {LineTerminator}|[ \t\f]
InputCharacter = [^\r\n]
LineComment = "//" {InputCharacter}*
BlockComment = "/*" ~"*/"

Identifier = [A-Za-z_][A-Za-z_0-9]*
NaturalNumber = 0|[1-9][0-9]*

%%

<YYINITIAL> {
    /* Declarations, e.g. var age : integer [0:120] or event alarm : extern. */
    "var"                 { return symbol(EcaSymbols.VAR); }
    "event"               { return symbol(EcaSymbols.EVENT); }
    "integer"             { return symbol(EcaSymbols.TYPE_INTEGER); }
    "bool"                { return symbol(EcaSymbols.TYPE_BOOL); }

    /* Rule, event, and action keywords. */
    "on"                  { return symbol(EcaSymbols.ON); }
    "if"                  { return symbol(EcaSymbols.IF); }
    "do"                  { return symbol(EcaSymbols.DO); }
    "intern"              { return symbol(EcaSymbols.INTERN); }
    "extern"              { return symbol(EcaSymbols.EXTERN); }
    "onetime"             { return symbol(EcaSymbols.ONETIME); }
    "repeat"              { return symbol(EcaSymbols.REPEAT); }
    "every"               { return symbol(EcaSymbols.EVERY); }
    "until"               { return symbol(EcaSymbols.UNTIL); }
    "after"               { return symbol(EcaSymbols.AFTER); }
    "for"                 { return symbol(EcaSymbols.FOR); }
    "par"                 { return symbol(EcaSymbols.PAR); }
    "ror"                 { return symbol(EcaSymbols.ROR); }
    "ms"|"s"|"min"|"h"|"month"|"months"|"year"|"years"
                          { return symbol(EcaSymbols.TIME_UNIT, yytext()); }

    /* Boolean literals and programming-language operators. */
    "true"                { return symbol(EcaSymbols.TRUE); }
    "false"               { return symbol(EcaSymbols.FALSE); }
    "&&"                  { return symbol(EcaSymbols.AND); }
    "||"                  { return symbol(EcaSymbols.OR); }
    "!"                   { return symbol(EcaSymbols.NOT); }
    "==>"                 { return symbol(EcaSymbols.IMPLIES); }
    "=="                  { return symbol(EcaSymbols.EQ); }
    "!="                  { return symbol(EcaSymbols.NEQ); }
    "<="                  { return symbol(EcaSymbols.LE); }
    ">="                  { return symbol(EcaSymbols.GE); }
    "<"                   { return symbol(EcaSymbols.LT); }
    ">"                   { return symbol(EcaSymbols.GT); }
    "+"                   { return symbol(EcaSymbols.PLUS); }
    "-"                   { return symbol(EcaSymbols.MINUS); }
    "*"                   { return symbol(EcaSymbols.TIMES); }
    "/"                   { return symbol(EcaSymbols.DIVIDE); }
    "%"                   { return symbol(EcaSymbols.MOD); }

    /* Punctuation and grouping. */
    "("                   { return symbol(EcaSymbols.LPAR); }
    ")"                   { return symbol(EcaSymbols.RPAR); }
    "["                   { return symbol(EcaSymbols.LBRACKET); }
    "]"                   { return symbol(EcaSymbols.RBRACKET); }
    ":"                   { return symbol(EcaSymbols.COLON); }
    ";"                   { return symbol(EcaSymbols.SEMI); }
    ","                   { return symbol(EcaSymbols.COMMA); }

    {NaturalNumber}       { return symbol(EcaSymbols.NATURAL_NUMBER, yytext()); }
    {Identifier}          { return symbol(EcaSymbols.ID, yytext()); }

    {LineComment}         { /* Skip comment. */ }
    {BlockComment}        { /* Skip comment. */ }
    {WhiteSpace}          { /* Skip whitespace. */ }
}

.|\n                     { return symbol(EcaSymbols.error, yytext()); }
<<EOF>>                 { return symbol(EcaSymbols.EOF); }
