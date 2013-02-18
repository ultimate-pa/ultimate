package java_cup;
import java_cup.runtime.ComplexSymbolFactory;
import java_cup.runtime.ComplexSymbolFactory.Location;
import java_cup.runtime.Symbol;
import java.io.InputStream;
import java.io.InputStreamReader;

%%

%class Lexer
%implements sym
%public
%unicode
%line
%column
%cup
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
  "?"           { return symbol("QESTION",QUESTION);           }
  ";"           { return symbol("SEMI",SEMI);                  }
  ","           { return symbol("COMMA",COMMA);                }
  "*"           { return symbol("STAR",STAR);                  }
  "."           { return symbol("DOT",DOT);                    }
  "|"           { return symbol("BAR",BAR);                    }
  "["           { return symbol("LBRACK",LBRACK);              }
  "]"           { return symbol("RBRACK",RBRACK);              }
  ":"           { return symbol("COLON",COLON);                }
  "="      	{ return symbol("EQUALS",EQUALS);              }
  "::="         { return symbol("COLON_COLON_EQUALS",COLON_COLON_EQUALS);   }
  "%prec"       { return symbol("PERCENT_PREC",PERCENT_PREC);  }
  ">"           { return symbol("GT",GT);                      }
  "<"           { return symbol("LT",LT);                      }
  {Comment}     {                                              }
  "{:"          { sb = new StringBuffer(); csline=yyline+1; cscolumn=yycolumn+1; yybegin(CODESEG);    }
  "package"     { return symbol("PACKAGE",PACKAGE);            } 
  "import"      { return symbol("IMPORT",IMPORT);	       }
  "option"      { return symbol("OPTION",OPTION);	       }
  "code"        { return symbol("CODE",CODE);		       }
  "action"      { return symbol("ACTION",ACTION);	       }
  "parser"      { return symbol("PARSER",PARSER);	       }
  "terminal"    { return symbol("PARSER",TERMINAL);	       }
  "non"         { return symbol("NON",NON);		       }
  "nonterminal" { return symbol("NONTERMINAL",NONTERMINAL);    }
  "init"        { return symbol("INIT",INIT);		       }
  "scan"        { return symbol("SCAN",SCAN);		       }
  "with"        { return symbol("WITH",WITH);		       }
  "start"       { return symbol("START",START);		       }
  "precedence"  { return symbol("PRECEDENCE",PRECEDENCE);      }
  "left"        { return symbol("LEFT",LEFT);		       }
  "right"       { return symbol("RIGHT",RIGHT);		       }
  "nonassoc"    { return symbol("NONASSOC",NONASSOC);          }
  "extends"     { return symbol("EXTENDS",EXTENDS);            }
  "super"       { return symbol("SUPER",SUPER);                }
  {ident}       { return symbol("ID",ID,yytext());             }
  
}

<CODESEG> {
  ":}"         { yybegin(YYINITIAL); return symbolFactory.newSymbol("CODE_STRING",CODE_STRING, new Location(csline, cscolumn),new Location(yyline+1,yycolumn+1+yylength()), sb.toString()); }
  .|\n            { sb.append(yytext()); }
}

// error fallback
.|\n          { emit_warning("Unrecognized character '" +yytext()+"' -- ignored"); }
