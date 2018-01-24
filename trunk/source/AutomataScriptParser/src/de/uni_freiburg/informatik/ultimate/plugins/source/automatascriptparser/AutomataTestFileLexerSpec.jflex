/* Author: Betim Musa
   Date: 25.11.2012
   This file is the specification for the Automata TestFile Scanner */

package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser;
import com.github.jhoenicke.javacup.runtime.*;

/* ------------------------Macro Declarations  ---------------------- */ 
%%

%public
%class Lexer

%line
%column

%implements com.github.jhoenicke.javacup.runtime.Scanner
%type com.github.jhoenicke.javacup.runtime.Symbol
%function next_token

%{   
    StringBuffer stringBuffer = new StringBuffer();
    private String m_LastToken = new String();
    private String m_CurToken = new String();
    private StringBuffer idBuffer = new StringBuffer();

    /* To create a new com.github.jhoenicke.javacup.runtime.Symbol with information about
       the current token, the token will have no value in this
       case. */
    private Symbol symbol(int type) {
        return new Symbol(type, yyline, yycolumn);
    }
    
    /* Also creates a new com.github.jhoenicke.javacup.runtime.Symbol with information
       about the current token, but this object has a value. */
    private Symbol symbol(int type, Object value) {
        return new Symbol(type, yyline, yycolumn, value);
    }

    public String getLastToken() {
      return m_LastToken;
    }

    public String getCurrentToken() {
      return m_CurToken;
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
SimpleIdentifier = [a-zA-Z_0-9]*[a-zA-Z][a-zA-Z_0-9]*

/* integer literals */
IntegerLiteral = 0 | [1-9][0-9]*

/* string and character literals */
StringCharacter = [^\r\n\"\\]

%state STRING
%%

/* ------------------------Lexical Rules Section---------------------- */

<YYINITIAL> {
  /* keywords */
  "boolean"                      { m_LastToken = m_CurToken; m_CurToken = "boolean"; return symbol(sym.BOOLEAN); }
  "break"                        { m_LastToken = m_CurToken; m_CurToken = "break"; return symbol(sym.BREAK); }
  "continue"                     { m_LastToken = m_CurToken; m_CurToken = "continue"; return symbol(sym.CONTINUE); }
  "else"                         { m_LastToken = m_CurToken; m_CurToken = "else"; return symbol(sym.ELSE); }
  "for"                          { m_LastToken = m_CurToken; m_CurToken = "for"; return symbol(sym.FOR); }
  "int"                          { m_LastToken = m_CurToken; m_CurToken = "int"; return symbol(sym.INT); }
  "if"                           { m_LastToken = m_CurToken; m_CurToken = "if"; return symbol(sym.IF); }
  "return"                       { m_LastToken = m_CurToken; m_CurToken = "return"; return symbol(sym.RETURN); }
  "String"                       { m_LastToken = m_CurToken; m_CurToken = "String"; return symbol(sym.STRING); }
  "while"                        { m_LastToken = m_CurToken; m_CurToken = "while"; return symbol(sym.WHILE); }
  
  /* keywords for Words */
  /* Word */
  "Word"                         { m_LastToken = m_CurToken; m_CurToken = "Word"; return symbol(sym.WORD); }
  /* NestedWord */
  "NestedWord"                   { m_LastToken = m_CurToken; m_CurToken = "NestedWord"; return symbol(sym.NESTED_WORD); }
    /* LassoWord */
  "LassoWord"                    { m_LastToken = m_CurToken; m_CurToken = "LassoWord"; return symbol(sym.NESTED_LASSO_WORD); }
  /* NestedLassoWord */
  "NestedLassoWord"              { m_LastToken = m_CurToken; m_CurToken = "NestedLassoWord"; return symbol(sym.NESTED_LASSO_WORD); }
  /* Tree */
  "Tree"                         { m_LastToken = m_CurToken; m_CurToken = "Tree"; return symbol(sym.TREE); }

  /* keywords for AutomataDefinitionFile */
  /* NestedWordAutomaton */
  "NestedWordAutomaton"         { m_LastToken = m_CurToken; m_CurToken = "NestedWordAutomaton"; return symbol(sym.NESTEDWORD_AUTOMATA); }
  "EpsilonNestedWordAutomaton"  { m_LastToken = m_CurToken; m_CurToken = "EpsilonNestedWordAutomaton"; return symbol(sym.EPSILON_NESTEDWORD_AUTOMATA); }
  "FiniteAutomaton"             { m_LastToken = m_CurToken; m_CurToken = "FiniteAutomaton"; return symbol(sym.FINITE_AUTOMATON); }
  "PetriNet"                    { m_LastToken = m_CurToken; m_CurToken = "PetriNet"; return symbol(sym.PETRINET_AUTOMATA); }
  "BranchingProcess"            { m_LastToken = m_CurToken; m_CurToken = "PetriNet"; return symbol(sym.BRANCHINGPROCESS_AUTOMATA); }
  "alphabet"                    { m_LastToken = m_CurToken; m_CurToken = "alphabet"; return symbol(sym.ALPHABET); }
  "callAlphabet"                { m_LastToken = m_CurToken; m_CurToken = "callAlphabet"; return symbol(sym.CALL_ALPHABET); }
  "internalAlphabet"            { m_LastToken = m_CurToken; m_CurToken = "internalAlphabet"; return symbol(sym.INTERNAL_ALPHABET); }
  "returnAlphabet"              { m_LastToken = m_CurToken; m_CurToken = "returnAlphabet"; return symbol(sym.RETURN_ALPHABET); }
  "states"                      { m_LastToken = m_CurToken; m_CurToken = "states"; return symbol(sym.STATES); }
  "initialStates"               { m_LastToken = m_CurToken; m_CurToken = "initialStates"; return symbol(sym.INITIAL_STATES); }
  "finalStates"                 { m_LastToken = m_CurToken; m_CurToken = "finalStates"; return symbol(sym.FINAL_STATES); }
  "transitions"                 { m_LastToken = m_CurToken; m_CurToken = "transitions"; return symbol(sym.TRANSITIONS); }
  "callTransitions"             { m_LastToken = m_CurToken; m_CurToken = "callTransitions"; return symbol(sym.CALL_TRANSITIONS); }
  "internalTransitions"         { m_LastToken = m_CurToken; m_CurToken = "internalTransitions"; return symbol(sym.INTERNAL_TRANSITIONS); }
  "returnTransitions"           { m_LastToken = m_CurToken; m_CurToken = "returnTransitions"; return symbol(sym.RETURN_TRANSITIONS); }
  "epsilonTransitions"          { m_LastToken = m_CurToken; m_CurToken = "epsilonTransitions"; return symbol(sym.EPSILON_TRANSITIONS); }
  "places"                      { m_LastToken = m_CurToken; m_CurToken = "places"; return symbol(sym.PLACES); }


  /* AlternatingAutomata */
  "AlternatingAutomaton"        { m_LastToken = m_CurToken; m_CurToken = "AlternatingAutomaton"; return symbol(sym.ALTERNATING_AUTOMATON); }
  "transitionTable"		  	 	{ m_LastToken = m_CurToken; m_CurToken = "transitionTable"; return symbol(sym.TRANSITION_TABLE); }
  "acceptingFunction"		    { m_LastToken = m_CurToken; m_CurToken = "acceptingFunction"; return symbol(sym.ACCEPTING_FUNCTION); }
  "~"		    				{ m_LastToken = m_CurToken; m_CurToken = "~"; return symbol(sym.EXPR_STATE_NEGATE); }
  "&"		    				{ m_LastToken = m_CurToken; m_CurToken = "~"; return symbol(sym.EXPR_STATE_AND); }
  "|"		    				{ m_LastToken = m_CurToken; m_CurToken = "~"; return symbol(sym.EXPR_STATE_OR); }
  "isReversed"		    		{ m_LastToken = m_CurToken; m_CurToken = "isReversed"; return symbol(sym.IS_REVERSED); }
  
  /* Tree Automata */
  "TreeAutomaton"               { m_LastToken = m_CurToken; m_CurToken = "TreeAutomaton"; return symbol(sym.TREE_AUTOMATON); }
  "rankedAlphabet"              { m_LastToken = m_CurToken; m_CurToken = "rankedAlphabet"; return symbol(sym.RANKED_ALPHABET); }
  
  // Net transitions  
  "initialMarking"                  { m_LastToken = m_CurToken; m_CurToken = "initialMarking"; return symbol(sym.INITIAL_MARKINGS); }
  "acceptingPlaces"                 { m_LastToken = m_CurToken; m_CurToken = "acceptingPlaces"; return symbol(sym.ACCEPTING_PLACES); }
  /* boolean literals */
  "true"                         { m_LastToken = m_CurToken; m_CurToken = "true"; return symbol(sym.BOOLEAN_LITERAL, new Boolean(true)); }
  "false"                        { m_LastToken = m_CurToken; m_CurToken = "false"; return symbol(sym.BOOLEAN_LITERAL, new Boolean(false)); }
  

  /* separators */
  "("                            { m_LastToken = m_CurToken; m_CurToken = "("; return symbol(sym.LPAREN); }
  ")"                            { m_LastToken = m_CurToken; m_CurToken = ")"; return symbol(sym.RPAREN); }
  "{"                            { m_LastToken = m_CurToken; m_CurToken = "{"; return symbol(sym.LBRACE); }
  "}"                            { m_LastToken = m_CurToken; m_CurToken = "}"; return symbol(sym.RBRACE); }
  "["                            { m_LastToken = m_CurToken; m_CurToken = "["; return symbol(sym.LBRACK); }
  "]"                            { m_LastToken = m_CurToken; m_CurToken = "]"; return symbol(sym.RBRACK); }
  ";"                            { m_LastToken = m_CurToken; m_CurToken = ";"; return symbol(sym.SEMICOLON); }
  ","                            { m_LastToken = m_CurToken; m_CurToken = ","; return symbol(sym.COMMA); }


  /* operators */
  "="                            { m_LastToken = m_CurToken; m_CurToken = "="; return symbol(sym.EQ); }
  ">"                            { m_LastToken = m_CurToken; m_CurToken = ">"; return symbol(sym.GT); }
  "<"                            { m_LastToken = m_CurToken; m_CurToken = "<"; return symbol(sym.LT); }
  "!"                            { m_LastToken = m_CurToken; m_CurToken = "!"; return symbol(sym.NOT); }
  "?"                            { m_LastToken = m_CurToken; m_CurToken = "?"; return symbol(sym.QUESTION); }
  ":"                            { m_LastToken = m_CurToken; m_CurToken = ":"; return symbol(sym.COLON); }
  "=="                           { m_LastToken = m_CurToken; m_CurToken = "=="; return symbol(sym.EQEQ); }
  "<="                           { m_LastToken = m_CurToken; m_CurToken = "<="; return symbol(sym.LTEQ); }
  ">="                           { m_LastToken = m_CurToken; m_CurToken = ">="; return symbol(sym.GTEQ); }
  "!="                           { m_LastToken = m_CurToken; m_CurToken = "!="; return symbol(sym.NOTEQ); }
  "&&"                           { m_LastToken = m_CurToken; m_CurToken = "&&"; return symbol(sym.ANDAND); }
  "||"                           { m_LastToken = m_CurToken; m_CurToken = "||"; return symbol(sym.OROR); }
  "++"                           { m_LastToken = m_CurToken; m_CurToken = "++"; return symbol(sym.PLUSPLUS); }
  "--"                           { m_LastToken = m_CurToken; m_CurToken = "--"; return symbol(sym.MINUSMINUS); }
  "+"                            { m_LastToken = m_CurToken; m_CurToken = "+"; return symbol(sym.PLUS); }
  "-"                            { m_LastToken = m_CurToken; m_CurToken = "-"; return symbol(sym.MINUS); }
  "*"                            { m_LastToken = m_CurToken; m_CurToken = "*"; return symbol(sym.MULT); }
  "/"                            { m_LastToken = m_CurToken; m_CurToken = "/"; return symbol(sym.DIV); }
  "+="                           { m_LastToken = m_CurToken; m_CurToken = "+="; return symbol(sym.PLUSEQ); }
  "-="                           { m_LastToken = m_CurToken; m_CurToken = "-="; return symbol(sym.MINUSEQ); }
  "*="                           { m_LastToken = m_CurToken; m_CurToken = "*="; return symbol(sym.MULTEQ); }
  "/="                           { m_LastToken = m_CurToken; m_CurToken = "/="; return symbol(sym.DIVEQ); }

  /* string literal */
  \"                             { yybegin(STRING); stringBuffer.setLength(0); }

  /* numeric literals */
  {IntegerLiteral}               { m_LastToken = m_CurToken; m_CurToken = yytext(); return symbol(sym.INTEGER_LITERAL, new Integer(yytext())); }


  /* comments */
  {Comment}                      { /* ignore */ }

  /* whitespace */
  {WhiteSpace}                   { /* ignore */ }

  /* identifiers */ 
  {SimpleIdentifier}                   { m_LastToken = m_CurToken; m_CurToken = yytext(); return symbol(sym.SIMPLE_IDENTIFIER, yytext()); }  

}
<STRING> {
  \"                             { yybegin(YYINITIAL); m_LastToken = m_CurToken; m_CurToken = stringBuffer.toString(); return symbol(sym.STRING_LITERAL, stringBuffer.toString()); }
  
  {StringCharacter}+             { stringBuffer.append( yytext() ); }
  
  /* escape sequences */
  "\\b"                          { stringBuffer.append( '\b' ); }
  "\\t"                          { stringBuffer.append( '\t' ); }
  "\\n"                          { stringBuffer.append( '\n' ); }
  "\\f"                          { stringBuffer.append( '\f' ); }
  "\\r"                          { stringBuffer.append( '\r' ); }
  "\\\""                         { stringBuffer.append( '\"' ); }
  "\\'"                          { stringBuffer.append( '\'' ); }
  "\\\\"                         { stringBuffer.append( '\\' ); }
  
  {LineTerminator}               { throw new RuntimeException("Unterminated string at end of line"); }
}

/* error fallback */
.|\n                             { m_LastToken = m_CurToken; m_CurToken = yytext(); return symbol(sym.error, "Syntax error: Illegal character \""+yytext()+ "\" at line "+(yyline + 1) + ", column "+( yycolumn + 1)); }
/* EndOfFile */
<<EOF>>                          { m_LastToken = m_CurToken; m_CurToken ="EOF"; return symbol(sym.EOF); }
