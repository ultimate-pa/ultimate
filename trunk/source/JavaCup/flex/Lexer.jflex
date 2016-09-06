package com.github.jhoenicke.javacup;
import com.github.jhoenicke.javacup.runtime.ComplexSymbolFactory;
import com.github.jhoenicke.javacup.runtime.ComplexSymbolFactory.Location;
import com.github.jhoenicke.javacup.runtime.Symbol;
import java.io.InputStream;
import java.io.InputStreamReader;

%%

%class Lexer
%implements sym, com.github.jhoenicke.javacup.runtime.Scanner
%function next_token
%type com.github.jhoenicke.javacup.runtime.Symbol
%eofclose
%public
%unicode
%line
%column
%{
    public Lexer(InputStream is, ComplexSymbolFactory sf){
	this(new InputStreamReader(is));
	symbolFactory = sf;
    }
    private StringBuffer sb;
    private ComplexSymbolFactory symbolFactory;
    private int csline,cscolumn;
    public Symbol symbol(String name, int code){
//	System.out.println("code:"+code+" "+yytext());
	return symbolFactory.newSymbol(name, code,new Location(yyline+1,yycolumn+1-yylength()),new Location(yyline+1,yycolumn+1));
    }
    public Symbol symbol(String name, int code, String lexem){
//	System.out.println("code:"+code+", lexem :"+lexem);
	return symbolFactory.newSymbol(name, code, new Location(yyline+1, yycolumn +1), new Location(yyline+1,yycolumn+yylength()), lexem);
    }
    protected void emit_warning(String message){
	ErrorManager.getManager().emit_warning("Scanner at " + (yyline+1) + "(" + (yycolumn+1) + "): " + message);
    }
    protected void emit_error(String message){
	ErrorManager.getManager().emit_error("Scanner at " + (yyline+1) + "(" + (yycolumn+1) +  "): " + message);
    }
%}

Newline = \r | \n | \r\n
Whitespace = [ \t\f] | {Newline}

/* comments */
Comment = {TraditionalComment} | {EndOfLineComment}
TraditionalComment = "/*" {CommentContent} \*+ "/"
EndOfLineComment = "//" [^\r\n]* {Newline}
CommentContent = ( [^*] | \*+[^*/] )*

ident = ([:jletter:] | "_" ) ([:jletterdigit:] | [:jletter:] | "_" )*
      | [:jletterdigit:]*  // Parse number as ident for options


%eofval{
    return symbolFactory.newSymbol("EOF",sym.EOF);
%eofval}

%state CODESEG

%%  

<YYINITIAL> {

  {Whitespace}  {                                              }
  "?"           { return symbol("QUESTION",QUESTION);          }
  ";"           { return symbol("SEMI",SEMI);                  }
  ","           { return symbol("COMMA",COMMA);                }
  "*"           { return symbol("STAR",STAR);                  }
  "+"           { return symbol("PLUS",PLUS);                  }
  "."           { return symbol("DOT",DOT);                    }
  "|"           { return symbol("BAR",BAR);                    }
  "["           { return symbol("LBRACK",LBRACK);              }
  "]"           { return symbol("RBRACK",RBRACK);              }
  ":"           { return symbol("COLON",COLON);                }
  "="           { return symbol("EQUALS",EQUALS);              }
  "::="         { return symbol("COLON_COLON_EQUALS",COLON_COLON_EQUALS);   }
  "%prec"       { return symbol("PERCENT_PREC",PERCENT_PREC);  }
  ">"           { return symbol("GT",GT);                      }
  "<"           { return symbol("LT",LT);                      }
  {Comment}     {                                              }
  "{:"          { sb = new StringBuffer(); csline=yyline+1; cscolumn=yycolumn+1; yybegin(CODESEG); }
  "package"     { return symbol("PACKAGE",PACKAGE,yytext());   } 
  "import"      { return symbol("IMPORT",IMPORT,yytext());     }
  "option"      { return symbol("OPTION",OPTION,yytext());     }
  "code"        { return symbol("CODE",CODE,yytext());         }
  "action"      { return symbol("ACTION",ACTION,yytext());     }
  "parser"      { return symbol("PARSER",PARSER,yytext());     }
  "terminal"    { return symbol("PARSER",TERMINAL,yytext());   }
  "non"         { return symbol("NON",NON,yytext());           }
  "nonterminal" { return symbol("NONTERMINAL",NONTERMINAL,yytext()); }
  "init"        { return symbol("INIT",INIT,yytext());         }
  "scan"        { return symbol("SCAN",SCAN,yytext());         }
  "with"        { return symbol("WITH",WITH,yytext());         }
  "start"       { return symbol("START",START,yytext());       }
  "precedence"  { return symbol("PRECEDENCE",PRECEDENCE,yytext()); }
  "left"        { return symbol("LEFT",LEFT,yytext());         }
  "right"       { return symbol("RIGHT",RIGHT,yytext());       }
  "nonassoc"    { return symbol("NONASSOC",NONASSOC,yytext()); }
  "extends"     { return symbol("EXTENDS",EXTENDS,yytext());   }
  "super"       { return symbol("SUPER",SUPER,yytext());       }
  {ident}       { return symbol("ID",ID,yytext());             }
  
}

<CODESEG> {
  ":}"          { yybegin(YYINITIAL); return symbolFactory.newSymbol("CODE_STRING",CODE_STRING, new Location(csline, cscolumn),new Location(yyline+1,yycolumn+1+yylength()), sb.toString()); }
  .|\n          { sb.append(yytext()); }
}

// error fallback
.|\n          { emit_warning("Unrecognized character '" +yytext()+"' -- ignored"); }
