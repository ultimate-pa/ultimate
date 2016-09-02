package de.uni_freiburg.informatik.ultimate.acsl.parser;

import com.github.jhoenicke.javacup.runtime.ComplexSymbolFactory;
import com.github.jhoenicke.javacup.runtime.Symbol;
%%
%class Scanner
%unicode
%implements com.github.jhoenicke.javacup.runtime.Scanner
%type com.github.jhoenicke.javacup.runtime.Symbol
%function next_token
%line
%column

%{
	public Scanner(java.io.InputStream r, ComplexSymbolFactory sf){
		this(r);
		this.sf=sf;
	}
	private ComplexSymbolFactory sf;
	
	private Symbol symbol(String text, int type) {
		ComplexSymbolFactory.Location left = new ComplexSymbolFactory.Location(yyline-1, yycolumn);
		ComplexSymbolFactory.Location right = new ComplexSymbolFactory.Location(yyline-1, yycolumn+yylength());
    	return sf.newSymbol(text, type, left, right);
  	}
  
  	private Symbol symbol(String text, int type, String value) {
    	ComplexSymbolFactory.Location left = new ComplexSymbolFactory.Location(yyline-1, yycolumn);
		ComplexSymbolFactory.Location right = new ComplexSymbolFactory.Location(yyline-1, yycolumn+yylength());
    	return sf.newSymbol(text, type, left, right, value);
    }
%}

space = [\032 \t \012 \r @ ]
rD = [0-9]
rO = [0-7]
rL = [a-zA-Z_]
rH = [a-fA-F0-9]
rE = [Ee][+-]? {rD}+
rP = [Pp][+-]? {rD}+
rFS	= (f|F|l|L)
rIS = (u|U|l|L)*

comment_line = "//" [^\n]*
escape = [\\ | \? | \a | \b | \f | \n | \r | \t | \v]
hex_escape = "\\" [xX] {rH}+
oct_escape = "\\" {rO} {rO}? {rO}?
utf8_char = [\128 - \254]+

/* Definition changed from Frama-C */
Identifier = {rL}({rL}|{rD})*
Constant1 = (0[xX] {rH}+ {rIS}?)
Constant2 = (0{rD}+{rIS}?)
Constant10 = {rD}+
Constant3 = {rD}+{rIS}	
Constant4 = {rD}+{rE}{rFS}?
Constant5 = {rD}*"."{rD}+({rE})? {rFS}?
Constant6 = {rD}+ "." {rD}* ({rE})? {rFS}? 
Constant7 = 0[xX]{rH}+ . {rH}* {rP} {rFS}? 
Constant8 = 0[xX]{rH}*.{rH}+ {rP} {rFS}? 
Constant9 = 0[xX]{rH}+ {rP} {rFS}? 

LineTerminator = \r|\n|\r\n
WhiteSpace     = {LineTerminator}* | {space}* 

%%
	"assert"		{ return symbol("assert",sym.ASSERT); }
    "assigns"		{ return symbol("assigns",sym.ASSIGNS); }
    "assumes"       { return symbol("assumes",sym.ASSUMES); }
    "at"			{ return symbol("at",sym.EXT_AT); }
    "axiom"         { return symbol("axiom",sym.AXIOM); } 
    "axiomatic"		{ return symbol("axiomatic",sym.AXIOMATIC); }
    "behavior"		{ return symbol("behavior",sym.BEHAVIOR); }
    "behaviors"		{ return symbol("behaviors",sym.BEHAVIORS); }
    "breaks"		{ return symbol("breaks",sym.BREAKS); }
	"case"			{ return symbol("case",sym.CASE); }
    "char"			{ return symbol("char",sym.CHAR, yytext()); }
    "complete"		{ return symbol("complete",sym.COMPLETE); }
    "const"         { return symbol("const",sym.CONST); }
    "continues"		{ return symbol("continues",sym.CONTINUES); }
    "contract"		{ return symbol("contract",sym.CONTRACT); }
    "decreases"		{ return symbol("decreases",sym.DECREASES); }
    "disjoint"		{ return symbol("disjoint",sym.DISJOINT); }
    "double"		{ return symbol("double",sym.DOUBLE, yytext()); }
    "else"          { return symbol("else",sym.ELSE); }
    "ensures"       { return symbol("ensures",sym.ENSURES); }
    "enum"			{ return symbol("enum",sym.ENUM); }
    "exists"        { return symbol("exists",sym.EXISTS); }
  	"function"      { return symbol("function",sym.FUNCTION); }
    "float"			{ return symbol("float",sym.FLOAT, yytext()); }
    "for"			{ return symbol("for",sym.FOR); }
    "global"		{ return symbol("global",sym.GLOBAL); } 
    "ltl"			{ return symbol("global",sym.LTL); }
    "if"            { return symbol("if",sym.IF); }
	"impact"		{ return symbol("impact",sym.IMPACT); }
	"inductive"		{ return symbol("inductive",sym.INDUCTIVE); }
	"include"		{ return symbol("include",sym.INCLUDE); }
	"int"           { return symbol("int",sym.INT, yytext()); }
    "invariant"		{ return symbol("invariant",sym.INVARIANT); }
    "label"			{ return symbol("label",sym.LABEL); }
    "lemma"			{ return symbol("lemma",sym.LEMMA); }
    "let"			{ return symbol("let",sym.EXT_LET); }
    "logic"			{ return symbol("logic",sym.LOGIC); }
    "long"			{ return symbol("long",sym.LONG, yytext()); }
    "loop"			{ return symbol("loop",sym.LOOP); }
    "modelfield"	{ return symbol("modelfield",sym.MODEL); }
    "module"		{ return symbol("module",sym.MODULE); }
    "pragma"		{ return symbol("pragma",sym.PRAGMA); }
    "predicate"		{ return symbol("predicate",sym.PREDICATE); }
    "reads"			{ return symbol("reads",sym.READS); }
    "requires"		{ return symbol("requires",sym.REQUIRES); }
    "returns"		{ return symbol("returns",sym.RETURNS); }
    "short"			{ return symbol("short",sym.SHORT, yytext()); }
    "signed"		{ return symbol("signed",sym.SIGNED, yytext()); }
    "sizeof"		{ return symbol("sizeof",sym.SIZEOF); }
    "slice"			{ return symbol("slice",sym.SLICE); }
    "struct"		{ return symbol("struct",sym.STRUCT); }
   	"terminates"	{ return symbol("terminates",sym.TERMINATES); }
    "type"			{ return symbol("type",sym.TYPE); }
	"unsigned"		{ return symbol("unsigned",sym.UNSIGNED, yytext()); }
    "variant"		{ return symbol("variant",sym.VARIANT); }
    "void"			{ return symbol("void",sym.VOID); }
    "writes"		{ return symbol("writes",sym.WRITES); }
    "integer"		{ return symbol("integer",sym.INTEGER, yytext()); } 
    "real"			{ return symbol("real",sym.REAL, yytext()); }
    "boolean"		{ return symbol("boolean",sym.BOOLEAN, yytext()); }
    "\\at"			{ return symbol("at",sym.AT); }
    "\\base_addr"	{ return symbol("base_addr",sym.BASE_ADDR); }
    "\\block_length"	{ return symbol("block_length",sym.BLOCK_LENGTH); }
    "\\empty"		{ return symbol("empty",sym.EMPTY); }
    "\\exists"		{ return symbol("exists",sym.EXISTS); }
    "\\false"		{ return symbol("false",sym.FALSE); }
    "\\forall"		{ return symbol("forall",sym.FORALL); }
    "\\fresh"		{ return symbol("fresh",sym.FRESH); }
    "\\freeable"      { return symbol("freeable",sym.FREEABLE); }
    "\\from"		{ return symbol("from",sym.FROM); }
    "\\initialized"	{ return symbol("initialized",sym.INITIALIZED); }
    "\\inter"		{ return symbol("inter",sym.INTER); }
    "\\lambda"		{ return symbol("lambda",sym.LAMBDA); }
    "\\let"			{ return symbol("let",sym.LET); }
    "\\mallocable"    { return symbol("mallocable",sym.MALLOCABLE);}
    "\\nothing"		{ return symbol("nothing",sym.NOTHING); }
    "\\null"		{ return symbol("null",sym.NULL); }
    "\\old"			{ return symbol("old",sym.OLD); }
    "\\result"		{ return symbol("result",sym.RESULT); }
    "\\separated"	{ return symbol("separated",sym.SEPARATED); }
    "\\true"		{ return symbol("true",sym.TRUE); }
    "\\type"		{ return symbol("type",sym.BSTYPE); }
    "\\typeof"		{ return symbol("typeof",sym.TYPEOF); }
    "\\union"		{ return symbol("union",sym.BSUNION); }
    "\\valid"		{ return symbol("valid",sym.VALID); }
    "\\valid_index"	{ return symbol("valid_index",sym.VALID_INDEX); }
    "\\valid_range"	{ return symbol("valid_range",sym.VALID_RANGE); }
    "\\with"		{ return symbol("with",sym.WITH); }
    "==>"			{ return symbol("implies",sym.IMPLIES); }
    "<==>"          { return symbol("iff",sym.IFF); }
  	"-->"           { return symbol("bimplies",sym.BIMPLIES); }
    "<-->"          { return symbol("biff",sym.BIFF); }
  	"&&"            { return symbol("and",sym.AND); }
  	"||"            { return symbol("or",sym.OR); }
  	"!"             { return symbol("not",sym.NOT); }
  	"$"             { return symbol("dollar",sym.DOLLAR); }
  	","             { return symbol("comma",sym.COMMA); }
  	"->"            { return symbol("arrow",sym.ARROW); }
  	"?"             { return symbol("question",sym.QUESTION); }
  	";"             { return symbol("semicolon",sym.SEMICOLON); }
  	":"             { return symbol("colon",sym.COLON); }
  	"::"            { return symbol("coloncolon",sym.COLONCOLON); }
    "."             { return symbol("dot",sym.DOT); }
    ".."            { return symbol("dotdot",sym.DOTDOT); }
    "..."           { return symbol("dotdotdot",sym.DOTDOTDOT); }
    "-"             { return symbol("minus",sym.MINUS); }
    "+"             { return symbol("plus",sym.PLUS); }
    "*"             { return symbol("star",sym.STAR); }
    "&"             { return symbol("amp",sym.AMP); }
    "^^"            { return symbol("hathat",sym.HATHAT); }
    "^"             { return symbol("hat",sym.HAT); }
    "|"             { return symbol("pipe",sym.PIPE); }
    "~"             { return symbol("tilde",sym.TILDE); }
    "/"             { return symbol("slash",sym.SLASH); }
    "%"             { return symbol("percent",sym.PERCENT); }
    "<"             { return symbol("lt",sym.LT); }
    ">"             { return symbol("gt",sym.GT); }
    "<="            { return symbol("le",sym.LE); }
    ">="            { return symbol("ge",sym.GE); }
    "=="           	{ return symbol("eq",sym.EQ); }
    "="             { return symbol("equal",sym.EQUAL); }
    "!="            { return symbol("ne",sym.NE); }
    "("             { return symbol("lpar",sym.LPAR); }
    ")"             { return symbol("rpar",sym.RPAR); }
    "{"             { return symbol("lbrace",sym.LBRACE); }
    "}"             { return symbol("rbrace",sym.RBRACE); }
    "["             { return symbol("lsquare",sym.LSQUARE); }
    "]"             { return symbol("rsquare",sym.RSQUARE); }
    "<:"          	{ return symbol("ltcolon",sym.LTCOLON); }
    ":>"            { return symbol("colongt",sym.COLONGT); }
    "<<"            { return symbol("ltlt",sym.LTLT); }
    ">>"            { return symbol("gtgt",sym.GTGT); }
    "[]"            { return symbol("globally",sym.GLOBALLY); }
    "<>"            { return symbol("finally",sym.FINALLY); }
    "X"             { return symbol("next",sym.NEXT); }
    "U"             { return symbol("until",sym.UNTIL); }
    "WU"             { return symbol("until",sym.WEAKUNTIL); }
    "R"             { return symbol("until",sym.RELEASE); }
    "AP"            { return symbol("ap",sym.AP); }
    
    space+			{}
	"\n"			{}
	{comment_line}"\n" {}
    
    "lstart"	{ return sf.newSymbol("lstart", sym.LSTART); }
	"gstart"		{ return sf.newSymbol("gstart", sym.GSTART); }
	{Identifier}	{ return symbol(yytext(), sym.IDENTIFIER, yytext()); }
	{Constant1}	{ return symbol(yytext(), sym.CONSTANT, yytext()); }
	{Constant2}	{ return symbol(yytext(), sym.CONSTANT, yytext()); }
	{Constant10}	{ return symbol(yytext(), sym.CONSTANT10, yytext()); }
	{Constant3}	{ return symbol(yytext(), sym.CONSTANT, yytext()); }
	{Constant4}	{ return symbol(yytext(), sym.CONSTANT, yytext()); }
	{Constant5}	{ return symbol(yytext(), sym.CONSTANT_FLOAT, yytext()); }
	{Constant6}	{ return symbol(yytext(), sym.CONSTANT_FLOAT, yytext()); }
	{Constant7}	{ return symbol(yytext(), sym.CONSTANT_FLOAT, yytext()); }
	{Constant8}	{ return symbol(yytext(), sym.CONSTANT_FLOAT, yytext()); }
	{Constant9}	{ return symbol(yytext(), sym.CONSTANT_FLOAT, yytext()); }
	
	/*String Literal missing */

	{WhiteSpace}	{ /* ignore */ }
/* error fallback */
.|\n		        { return symbol("error",sym.error, yytext()); }
<<EOF>>             { return symbol("eof",sym.EOF); }