package de.uni_freiburg.informatik.ultimate.astbuilder;
import java.io.Reader;
import java.io.IOException;
import java_cup.runtime.Symbol;
import java_cup.runtime.Scanner;

public class Lexer implements Scanner {
    boolean eof = false;
    char lookahead;
    int line;
    int col;
    boolean lastCR;
    Reader reader;

    public Lexer (Reader r) throws IOException {
        this.reader = r;
        line = 1;
        col = 0;
        advance();
    }

    public int getLineCol() {
        return (line << 16) | col;
    }

    public void advance() throws IOException {
        int i = reader.read();
        if (lookahead == '\n') {
            line++;
            col = 1;
        } else
            col++;

        if (i < 0)
            eof = true;
        else
            lookahead = (char) i;

        if (lastCR && lookahead == '\n') {
            /* Ignore LF after CR */
            lastCR = false;
            advance();
            return;
        } 
        lastCR = (lookahead == '\r');
        if (lastCR)
            /* map CR to LF */
            lookahead = '\n';
    }

    private void skipWhiteSpace() throws IOException {
        while (Character.isWhitespace(lookahead) && !eof)
            advance();
    }

    private String parseIdentifier() throws IOException {
        StringBuffer sb = new StringBuffer();
        do {
            sb.append(lookahead);
            advance();
        } while (Character.isUnicodeIdentifierPart(lookahead) && !eof);
        return sb.toString();
    }

    private String parseComment() throws IOException {
        advance();
        if (lookahead != '*') {
            do {
                while (lookahead != '*' && !eof)
                    advance();
                advance();
            } while (lookahead != '/' && !eof);
            advance();
            return null;
        }
        while (lookahead == '*' && !eof)
            advance();
        skipWhiteSpace();

        StringBuffer sb = new StringBuffer();
        boolean needsSpace = false;
        boolean lastWord = false;
        do {
            while (lookahead != '*' && !eof) {
                if (Character.isWhitespace(lookahead)) {
                    needsSpace = lastWord;
                    while (Character.isWhitespace(lookahead)) {
                        if (lookahead == '\n') {
                            sb.append('\n');
                            needsSpace = false;
                        }
                        advance();
                    }
                    lastWord = false;
                } else {
                    if (needsSpace)
                        sb.append(' ');
                    sb.append(lookahead);
                    needsSpace = false;
                    lastWord = true;
                    advance();
                }
            }
            advance();
        } while (lookahead != '/' && !eof);
        if (eof)
          return null;

        while (Character.isWhitespace(sb.charAt(sb.length()-1)))
            sb.setLength(sb.length()-1);
        advance();
        return sb.toString();
    }

    public Symbol next_token() throws IOException {
        for (;;) {
            skipWhiteSpace();
            if (eof)
                return new Symbol(sym.EOF, getLineCol(), getLineCol());
            
            int left = getLineCol();
            switch (lookahead) {
            case '*':
                advance();
                return new Symbol(sym.STAR, left, getLineCol());
            case '(':
                advance();
                return new Symbol(sym.LPAREN, left, getLineCol());
            case ')':
                advance();
                return new Symbol(sym.RPAREN, left, getLineCol());
            case '{':
                advance();
                return new Symbol(sym.LBRACE, left, getLineCol());
            case '}':
                advance();
                return new Symbol(sym.RBRACE, left, getLineCol());
            case '[':
                advance();
                return new Symbol(sym.LBRACKET, left, getLineCol());
            case ']':
                advance();
                return new Symbol(sym.RBRACKET, left, getLineCol());
            case '<':
                advance();
                return new Symbol(sym.LANGLE, left, getLineCol());
            case '>':
                advance();
                return new Symbol(sym.RANGLE, left, getLineCol());
            case ':':
                advance();
                if (lookahead == ':') {
                    advance();
                    if (lookahead == '=') {
                        advance();
                        return new Symbol(sym.DDEF, left, getLineCol());
                    }
                    return new Symbol(sym.error, left, getLineCol());
                }
                return new Symbol(sym.COLON, left, getLineCol());
            case ';':
                advance();
                return new Symbol(sym.SEMI, left, getLineCol());
            case ',':
                advance();
                return new Symbol(sym.COMMA, left, getLineCol());
            case '|':
                advance();
                return new Symbol(sym.BAR, left, getLineCol());
            case '.':
                advance();
                return new Symbol(sym.DOT, left, getLineCol());
            case '/':
                {
                    advance();
                    if (lookahead != '*')
                        return new Symbol(sym.error, left, getLineCol());
                    String comment = parseComment();
                    if (comment == null)
                        continue;
                    return new Symbol(sym.DOCCOMMENT, left, getLineCol(),
                                      comment);
                }
            case '!':
            	advance();
                return new Symbol(sym.WRITEABLE_ONCE, left, getLineCol());
            case '&':
                advance();
                return new Symbol(sym.WRITEABLE, left, getLineCol());
            case '?':
                advance();
                return new Symbol(sym.OPTIONAL, left, getLineCol());
            default:
                if (Character.isUnicodeIdentifierStart(lookahead)) {
                    String ident = parseIdentifier();
                    if (ident.equals("package"))
                        return new Symbol(sym.PACKAGE, left, getLineCol());
                    else if (ident.equals("import"))
                        return new Symbol(sym.IMPORT, left, getLineCol());
                    else if (ident.equals("implements"))
                        return new Symbol(sym.IMPLEMENTS, left, getLineCol());
                    else
                        return new Symbol(sym.IDENT, left, getLineCol(), 
                                          ident);
                }
                System.err.println("Unexpected Character: "+lookahead
                                   +" ("+(int)lookahead+")");
                advance();
                return new Symbol(sym.error, left, getLineCol());
            }
        }
    }
}
