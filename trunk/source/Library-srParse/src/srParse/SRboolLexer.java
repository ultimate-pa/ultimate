// $ANTLR 3.2 Sep 23, 2009 12:02:23 C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g 2010-08-20 10:31:48


package srParse;


import org.antlr.runtime.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;

public class SRboolLexer extends Lexer {
    public static final int DPKT=23;
    public static final int SC_UNTIL=20;
    public static final int KW_WHICH=35;
    public static final int KOM=78;
    public static final int KW_AND=18;
    public static final int KW_BECOMES=64;
    public static final int KW_ONCE=63;
    public static final int KW_PREV=47;
    public static final int ID=22;
    public static final int BR_OPEN=12;
    public static final int KW_WHERE=53;
    public static final int EOF=-1;
    public static final int PKT=21;
    public static final int KW_VAR=27;
    public static final int KW_THAT=43;
    public static final int QUOTE=9;
    public static final int KW_PREC=50;
    public static final int EOL=74;
    public static final int KW_NEVER=40;
    public static final int KW_TIME=57;
    public static final int SC_BEFORE=16;
    public static final int KW_WAS=49;
    public static final int KW_FOR=59;
    public static final int KW_AFTER=56;
    public static final int KW_LEAST=60;
    public static final int KW_SEQ=72;
    public static final int KW_THAN=67;
    public static final int KW_THEN=46;
    public static final int KW_IN=26;
    public static final int SC_GLOBALLY=14;
    public static final int NOT_1=10;
    public static final int KW_IS=31;
    public static final int SC_BETWEEN=17;
    public static final int KW_IT=30;
    public static final int KW_IF=45;
    public static final int KW_SAT=65;
    public static final int SC_AFTER=19;
    public static final int KW_ONE=70;
    public static final int KW_HOLDS=29;
    public static final int KW_THERE=69;
    public static final int KW_BETW=76;
    public static final int KW_MOST=38;
    public static final int T__81=81;
    public static final int KW_WELL=62;
    public static final int KW_SUCH=73;
    public static final int T__82=82;
    public static final int OTHER=80;
    public static final int KW_EVENTUALLY=28;
    public static final int KW_LESS=66;
    public static final int KW_HELD=48;
    public static final int KW_SUCC=52;
    public static final int AND_1=4;
    public static final int KW_HOLD=55;
    public static final int AND_2=5;
    public static final int K=15;
    public static final int INT=25;
    public static final int KW_TWICE=39;
    public static final int KW_CASE=42;
    public static final int KW_EXEC=71;
    public static final int KW_TRANS=32;
    public static final int KW_ALWAYS=44;
    public static final int KW_UNITS=58;
    public static final int WS=77;
    public static final int KW_EVERY=68;
    public static final int OP=24;
    public static final int KW_TO=33;
    public static final int KW_BY=51;
    public static final int KW_STATES=34;
    public static final int KW_AS=61;
    public static final int KW_AT=37;
    public static final int KW_OCCUR=36;
    public static final int KOM_2=79;
    public static final int KW_THE=41;
    public static final int OR_1=6;
    public static final int BR_CLOSE=13;
    public static final int KW_DOES=54;
    public static final int NODECLARE=75;
    public static final int OR_3=8;
    public static final int OR_2=7;
    public static final int KW_NOT=11;

    // delegates
    // delegators

    public SRboolLexer() {;} 
    public SRboolLexer(CharStream input) {
        this(input, new RecognizerSharedState());
    }
    public SRboolLexer(CharStream input, RecognizerSharedState state) {
        super(input,state);

    }
    public String getGrammarFileName() { return "C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g"; }

    // $ANTLR start "T__81"
    public final void mT__81() throws RecognitionException {
        try {
            int _type = T__81;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:3:7: ( '{' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:3:9: '{'
            {
            match('{'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__81"

    // $ANTLR start "T__82"
    public final void mT__82() throws RecognitionException {
        try {
            int _type = T__82;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:4:7: ( '}' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:4:9: '}'
            {
            match('}'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__82"

    // $ANTLR start "EOL"
    public final void mEOL() throws RecognitionException {
        try {
            int _type = EOL;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:582:5: ( ( '\\n' | '\\r\\n' | ';' ) )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:582:7: ( '\\n' | '\\r\\n' | ';' )
            {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:582:7: ( '\\n' | '\\r\\n' | ';' )
            int alt1=3;
            switch ( input.LA(1) ) {
            case '\n':
                {
                alt1=1;
                }
                break;
            case '\r':
                {
                alt1=2;
                }
                break;
            case ';':
                {
                alt1=3;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("", 1, 0, input);

                throw nvae;
            }

            switch (alt1) {
                case 1 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:582:9: '\\n'
                    {
                    match('\n'); 

                    }
                    break;
                case 2 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:582:15: '\\r\\n'
                    {
                    match("\r\n"); 


                    }
                    break;
                case 3 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:582:24: ';'
                    {
                    match(';'); 

                    }
                    break;

            }


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "EOL"

    // $ANTLR start "K"
    public final void mK() throws RecognitionException {
        try {
            int _type = K;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:584:3: ( ',' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:584:5: ','
            {
            match(','); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "K"

    // $ANTLR start "PKT"
    public final void mPKT() throws RecognitionException {
        try {
            int _type = PKT;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:585:5: ( '.' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:585:7: '.'
            {
            match('.'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "PKT"

    // $ANTLR start "DPKT"
    public final void mDPKT() throws RecognitionException {
        try {
            int _type = DPKT;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:586:6: ( ':' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:586:8: ':'
            {
            match(':'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "DPKT"

    // $ANTLR start "NODECLARE"
    public final void mNODECLARE() throws RecognitionException {
        try {
            int _type = NODECLARE;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:588:11: ( 'nodeclare' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:588:13: 'nodeclare'
            {
            match("nodeclare"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "NODECLARE"

    // $ANTLR start "SC_GLOBALLY"
    public final void mSC_GLOBALLY() throws RecognitionException {
        try {
            int _type = SC_GLOBALLY;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:590:13: ( 'Globally' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:590:15: 'Globally'
            {
            match("Globally"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "SC_GLOBALLY"

    // $ANTLR start "SC_BEFORE"
    public final void mSC_BEFORE() throws RecognitionException {
        try {
            int _type = SC_BEFORE;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:591:11: ( 'Before' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:591:13: 'Before'
            {
            match("Before"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "SC_BEFORE"

    // $ANTLR start "SC_AFTER"
    public final void mSC_AFTER() throws RecognitionException {
        try {
            int _type = SC_AFTER;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:592:10: ( 'After' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:592:12: 'After'
            {
            match("After"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "SC_AFTER"

    // $ANTLR start "SC_UNTIL"
    public final void mSC_UNTIL() throws RecognitionException {
        try {
            int _type = SC_UNTIL;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:593:10: ( 'until' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:593:12: 'until'
            {
            match("until"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "SC_UNTIL"

    // $ANTLR start "SC_BETWEEN"
    public final void mSC_BETWEEN() throws RecognitionException {
        try {
            int _type = SC_BETWEEN;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:594:12: ( 'Between' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:594:14: 'Between'
            {
            match("Between"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "SC_BETWEEN"

    // $ANTLR start "KW_WHERE"
    public final void mKW_WHERE() throws RecognitionException {
        try {
            int _type = KW_WHERE;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:596:10: ( 'where' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:596:12: 'where'
            {
            match("where"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_WHERE"

    // $ANTLR start "KW_AFTER"
    public final void mKW_AFTER() throws RecognitionException {
        try {
            int _type = KW_AFTER;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:597:10: ( 'after' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:597:12: 'after'
            {
            match("after"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_AFTER"

    // $ANTLR start "KW_AND"
    public final void mKW_AND() throws RecognitionException {
        try {
            int _type = KW_AND;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:598:9: ( 'and' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:598:11: 'and'
            {
            match("and"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_AND"

    // $ANTLR start "KW_IT"
    public final void mKW_IT() throws RecognitionException {
        try {
            int _type = KW_IT;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:599:8: ( 'it' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:599:10: 'it'
            {
            match("it"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_IT"

    // $ANTLR start "KW_IS"
    public final void mKW_IS() throws RecognitionException {
        try {
            int _type = KW_IS;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:600:8: ( 'is' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:600:10: 'is'
            {
            match("is"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_IS"

    // $ANTLR start "KW_NEVER"
    public final void mKW_NEVER() throws RecognitionException {
        try {
            int _type = KW_NEVER;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:601:10: ( 'never' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:601:12: 'never'
            {
            match("never"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_NEVER"

    // $ANTLR start "KW_THE"
    public final void mKW_THE() throws RecognitionException {
        try {
            int _type = KW_THE;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:602:9: ( 'the' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:602:11: 'the'
            {
            match("the"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_THE"

    // $ANTLR start "KW_CASE"
    public final void mKW_CASE() throws RecognitionException {
        try {
            int _type = KW_CASE;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:603:10: ( 'case' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:603:12: 'case'
            {
            match("case"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_CASE"

    // $ANTLR start "KW_THAT"
    public final void mKW_THAT() throws RecognitionException {
        try {
            int _type = KW_THAT;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:604:10: ( 'that' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:604:12: 'that'
            {
            match("that"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_THAT"

    // $ANTLR start "KW_HOLDS"
    public final void mKW_HOLDS() throws RecognitionException {
        try {
            int _type = KW_HOLDS;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:605:10: ( 'holds' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:605:12: 'holds'
            {
            match("holds"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_HOLDS"

    // $ANTLR start "KW_AS"
    public final void mKW_AS() throws RecognitionException {
        try {
            int _type = KW_AS;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:606:8: ( 'as' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:606:10: 'as'
            {
            match("as"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_AS"

    // $ANTLR start "KW_WELL"
    public final void mKW_WELL() throws RecognitionException {
        try {
            int _type = KW_WELL;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:607:10: ( 'well' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:607:12: 'well'
            {
            match("well"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_WELL"

    // $ANTLR start "KW_ALWAYS"
    public final void mKW_ALWAYS() throws RecognitionException {
        try {
            int _type = KW_ALWAYS;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:608:11: ( 'always' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:608:13: 'always'
            {
            match("always"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_ALWAYS"

    // $ANTLR start "KW_EVENTUALLY"
    public final void mKW_EVENTUALLY() throws RecognitionException {
        try {
            int _type = KW_EVENTUALLY;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:609:15: ( 'eventually' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:609:17: 'eventually'
            {
            match("eventually"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_EVENTUALLY"

    // $ANTLR start "KW_TRANS"
    public final void mKW_TRANS() throws RecognitionException {
        try {
            int _type = KW_TRANS;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:610:10: ( 'transitions' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:610:12: 'transitions'
            {
            match("transitions"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_TRANS"

    // $ANTLR start "KW_TO"
    public final void mKW_TO() throws RecognitionException {
        try {
            int _type = KW_TO;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:611:8: ( 'to' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:611:10: 'to'
            {
            match("to"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_TO"

    // $ANTLR start "KW_STATES"
    public final void mKW_STATES() throws RecognitionException {
        try {
            int _type = KW_STATES;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:612:11: ( 'states' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:612:13: 'states'
            {
            match("states"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_STATES"

    // $ANTLR start "KW_IN"
    public final void mKW_IN() throws RecognitionException {
        try {
            int _type = KW_IN;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:613:8: ( 'in' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:613:10: 'in'
            {
            match("in"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_IN"

    // $ANTLR start "KW_WHICH"
    public final void mKW_WHICH() throws RecognitionException {
        try {
            int _type = KW_WHICH;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:614:10: ( 'which' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:614:12: 'which'
            {
            match("which"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_WHICH"

    // $ANTLR start "KW_OCCUR"
    public final void mKW_OCCUR() throws RecognitionException {
        try {
            int _type = KW_OCCUR;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:615:10: ( 'occur' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:615:12: 'occur'
            {
            match("occur"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_OCCUR"

    // $ANTLR start "KW_AT"
    public final void mKW_AT() throws RecognitionException {
        try {
            int _type = KW_AT;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:616:8: ( 'at' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:616:10: 'at'
            {
            match("at"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_AT"

    // $ANTLR start "KW_MOST"
    public final void mKW_MOST() throws RecognitionException {
        try {
            int _type = KW_MOST;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:617:10: ( 'most' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:617:12: 'most'
            {
            match("most"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_MOST"

    // $ANTLR start "KW_TWICE"
    public final void mKW_TWICE() throws RecognitionException {
        try {
            int _type = KW_TWICE;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:618:10: ( 'twice' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:618:12: 'twice'
            {
            match("twice"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_TWICE"

    // $ANTLR start "KW_IF"
    public final void mKW_IF() throws RecognitionException {
        try {
            int _type = KW_IF;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:619:8: ( 'if' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:619:10: 'if'
            {
            match("if"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_IF"

    // $ANTLR start "KW_PREV"
    public final void mKW_PREV() throws RecognitionException {
        try {
            int _type = KW_PREV;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:620:10: ( 'previously' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:620:12: 'previously'
            {
            match("previously"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_PREV"

    // $ANTLR start "KW_HELD"
    public final void mKW_HELD() throws RecognitionException {
        try {
            int _type = KW_HELD;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:621:10: ( 'held' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:621:12: 'held'
            {
            match("held"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_HELD"

    // $ANTLR start "KW_SUCC"
    public final void mKW_SUCC() throws RecognitionException {
        try {
            int _type = KW_SUCC;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:622:10: ( 'succeeded' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:622:12: 'succeeded'
            {
            match("succeeded"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_SUCC"

    // $ANTLR start "KW_BY"
    public final void mKW_BY() throws RecognitionException {
        try {
            int _type = KW_BY;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:623:8: ( 'by' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:623:10: 'by'
            {
            match("by"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_BY"

    // $ANTLR start "KW_THEN"
    public final void mKW_THEN() throws RecognitionException {
        try {
            int _type = KW_THEN;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:624:10: ( 'then' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:624:12: 'then'
            {
            match("then"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_THEN"

    // $ANTLR start "KW_WAS"
    public final void mKW_WAS() throws RecognitionException {
        try {
            int _type = KW_WAS;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:625:9: ( 'was' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:625:11: 'was'
            {
            match("was"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_WAS"

    // $ANTLR start "KW_PREC"
    public final void mKW_PREC() throws RecognitionException {
        try {
            int _type = KW_PREC;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:626:10: ( 'preceded' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:626:12: 'preceded'
            {
            match("preceded"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_PREC"

    // $ANTLR start "KW_ONCE"
    public final void mKW_ONCE() throws RecognitionException {
        try {
            int _type = KW_ONCE;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:627:10: ( 'once' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:627:12: 'once'
            {
            match("once"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_ONCE"

    // $ANTLR start "KW_BECOMES"
    public final void mKW_BECOMES() throws RecognitionException {
        try {
            int _type = KW_BECOMES;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:628:12: ( 'becomes' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:628:14: 'becomes'
            {
            match("becomes"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_BECOMES"

    // $ANTLR start "KW_SAT"
    public final void mKW_SAT() throws RecognitionException {
        try {
            int _type = KW_SAT;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:629:9: ( 'satisfied' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:629:11: 'satisfied'
            {
            match("satisfied"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_SAT"

    // $ANTLR start "KW_FOR"
    public final void mKW_FOR() throws RecognitionException {
        try {
            int _type = KW_FOR;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:630:9: ( 'for' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:630:11: 'for'
            {
            match("for"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_FOR"

    // $ANTLR start "KW_LESS"
    public final void mKW_LESS() throws RecognitionException {
        try {
            int _type = KW_LESS;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:631:10: ( 'less' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:631:12: 'less'
            {
            match("less"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_LESS"

    // $ANTLR start "KW_THAN"
    public final void mKW_THAN() throws RecognitionException {
        try {
            int _type = KW_THAN;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:632:10: ( 'than' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:632:12: 'than'
            {
            match("than"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_THAN"

    // $ANTLR start "KW_DOES"
    public final void mKW_DOES() throws RecognitionException {
        try {
            int _type = KW_DOES;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:633:10: ( 'does' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:633:12: 'does'
            {
            match("does"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_DOES"

    // $ANTLR start "KW_NOT"
    public final void mKW_NOT() throws RecognitionException {
        try {
            int _type = KW_NOT;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:634:9: ( 'not' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:634:11: 'not'
            {
            match("not"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_NOT"

    // $ANTLR start "KW_HOLD"
    public final void mKW_HOLD() throws RecognitionException {
        try {
            int _type = KW_HOLD;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:635:10: ( 'hold' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:635:12: 'hold'
            {
            match("hold"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_HOLD"

    // $ANTLR start "KW_BETW"
    public final void mKW_BETW() throws RecognitionException {
        try {
            int _type = KW_BETW;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:636:10: ( 'between' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:636:12: 'between'
            {
            match("between"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_BETW"

    // $ANTLR start "KW_TIME"
    public final void mKW_TIME() throws RecognitionException {
        try {
            int _type = KW_TIME;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:637:10: ( 'time' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:637:12: 'time'
            {
            match("time"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_TIME"

    // $ANTLR start "KW_UNITS"
    public final void mKW_UNITS() throws RecognitionException {
        try {
            int _type = KW_UNITS;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:638:10: ( 'units' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:638:12: 'units'
            {
            match("units"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_UNITS"

    // $ANTLR start "KW_LEAST"
    public final void mKW_LEAST() throws RecognitionException {
        try {
            int _type = KW_LEAST;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:639:10: ( 'least' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:639:12: 'least'
            {
            match("least"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_LEAST"

    // $ANTLR start "KW_EVERY"
    public final void mKW_EVERY() throws RecognitionException {
        try {
            int _type = KW_EVERY;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:640:10: ( 'every' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:640:12: 'every'
            {
            match("every"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_EVERY"

    // $ANTLR start "KW_ONE"
    public final void mKW_ONE() throws RecognitionException {
        try {
            int _type = KW_ONE;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:641:9: ( 'one' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:641:11: 'one'
            {
            match("one"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_ONE"

    // $ANTLR start "KW_EXEC"
    public final void mKW_EXEC() throws RecognitionException {
        try {
            int _type = KW_EXEC;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:642:10: ( 'execution' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:642:12: 'execution'
            {
            match("execution"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_EXEC"

    // $ANTLR start "KW_SEQ"
    public final void mKW_SEQ() throws RecognitionException {
        try {
            int _type = KW_SEQ;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:643:9: ( 'sequence' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:643:11: 'sequence'
            {
            match("sequence"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_SEQ"

    // $ANTLR start "KW_SUCH"
    public final void mKW_SUCH() throws RecognitionException {
        try {
            int _type = KW_SUCH;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:644:10: ( 'such' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:644:12: 'such'
            {
            match("such"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_SUCH"

    // $ANTLR start "KW_THERE"
    public final void mKW_THERE() throws RecognitionException {
        try {
            int _type = KW_THERE;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:645:10: ( 'there' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:645:12: 'there'
            {
            match("there"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_THERE"

    // $ANTLR start "KW_VAR"
    public final void mKW_VAR() throws RecognitionException {
        try {
            int _type = KW_VAR;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:647:9: ( 'var' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:647:11: 'var'
            {
            match("var"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KW_VAR"

    // $ANTLR start "OR_1"
    public final void mOR_1() throws RecognitionException {
        try {
            int _type = OR_1;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:650:6: ( '\\u2228' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:650:8: '\\u2228'
            {
            match('\u2228'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "OR_1"

    // $ANTLR start "OR_2"
    public final void mOR_2() throws RecognitionException {
        try {
            int _type = OR_2;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:651:6: ( '||' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:651:8: '||'
            {
            match("||"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "OR_2"

    // $ANTLR start "OR_3"
    public final void mOR_3() throws RecognitionException {
        try {
            int _type = OR_3;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:652:6: ( 'or' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:652:8: 'or'
            {
            match("or"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "OR_3"

    // $ANTLR start "AND_1"
    public final void mAND_1() throws RecognitionException {
        try {
            int _type = AND_1;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:653:7: ( '\\u2227' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:653:9: '\\u2227'
            {
            match('\u2227'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "AND_1"

    // $ANTLR start "AND_2"
    public final void mAND_2() throws RecognitionException {
        try {
            int _type = AND_2;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:654:7: ( '&&' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:654:9: '&&'
            {
            match("&&"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "AND_2"

    // $ANTLR start "OP"
    public final void mOP() throws RecognitionException {
        try {
            int _type = OP;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:656:4: ( '>' | '<' | '>=' | '<=' | 'in' | '=' )
            int alt2=6;
            switch ( input.LA(1) ) {
            case '>':
                {
                int LA2_1 = input.LA(2);

                if ( (LA2_1=='=') ) {
                    alt2=3;
                }
                else {
                    alt2=1;}
                }
                break;
            case '<':
                {
                int LA2_2 = input.LA(2);

                if ( (LA2_2=='=') ) {
                    alt2=4;
                }
                else {
                    alt2=2;}
                }
                break;
            case 'i':
                {
                alt2=5;
                }
                break;
            case '=':
                {
                alt2=6;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("", 2, 0, input);

                throw nvae;
            }

            switch (alt2) {
                case 1 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:656:6: '>'
                    {
                    match('>'); 

                    }
                    break;
                case 2 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:656:10: '<'
                    {
                    match('<'); 

                    }
                    break;
                case 3 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:656:14: '>='
                    {
                    match(">="); 


                    }
                    break;
                case 4 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:656:19: '<='
                    {
                    match("<="); 


                    }
                    break;
                case 5 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:656:24: 'in'
                    {
                    match("in"); 


                    }
                    break;
                case 6 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:656:29: '='
                    {
                    match('='); 

                    }
                    break;

            }
            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "OP"

    // $ANTLR start "ID"
    public final void mID() throws RecognitionException {
        try {
            int _type = ID;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:659:5: ( ( 'a' .. 'z' | 'A' .. 'Z' | 'ä' | 'Ä' | 'ö' | 'Ö' | 'ü' | 'Ü' | '_' ) ( 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | 'ä' | 'Ä' | 'ö' | 'Ö' | 'ü' | 'Ü' )* )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:659:7: ( 'a' .. 'z' | 'A' .. 'Z' | 'ä' | 'Ä' | 'ö' | 'Ö' | 'ü' | 'Ü' | '_' ) ( 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | 'ä' | 'Ä' | 'ö' | 'Ö' | 'ü' | 'Ü' )*
            {
            if ( (input.LA(1)>='A' && input.LA(1)<='Z')||input.LA(1)=='_'||(input.LA(1)>='a' && input.LA(1)<='z')||input.LA(1)=='\u00C4'||input.LA(1)=='\u00D6'||input.LA(1)=='\u00DC'||input.LA(1)=='\u00E4'||input.LA(1)=='\u00F6'||input.LA(1)=='\u00FC' ) {
                input.consume();

            }
            else {
                MismatchedSetException mse = new MismatchedSetException(null,input);
                recover(mse);
                throw mse;}

            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:659:55: ( 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | 'ä' | 'Ä' | 'ö' | 'Ö' | 'ü' | 'Ü' )*
            loop3:
            do {
                int alt3=2;
                int LA3_0 = input.LA(1);

                if ( ((LA3_0>='0' && LA3_0<='9')||(LA3_0>='A' && LA3_0<='Z')||LA3_0=='_'||(LA3_0>='a' && LA3_0<='z')||LA3_0=='\u00C4'||LA3_0=='\u00D6'||LA3_0=='\u00DC'||LA3_0=='\u00E4'||LA3_0=='\u00F6'||LA3_0=='\u00FC') ) {
                    alt3=1;
                }


                switch (alt3) {
            	case 1 :
            	    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:
            	    {
            	    if ( (input.LA(1)>='0' && input.LA(1)<='9')||(input.LA(1)>='A' && input.LA(1)<='Z')||input.LA(1)=='_'||(input.LA(1)>='a' && input.LA(1)<='z')||input.LA(1)=='\u00C4'||input.LA(1)=='\u00D6'||input.LA(1)=='\u00DC'||input.LA(1)=='\u00E4'||input.LA(1)=='\u00F6'||input.LA(1)=='\u00FC' ) {
            	        input.consume();

            	    }
            	    else {
            	        MismatchedSetException mse = new MismatchedSetException(null,input);
            	        recover(mse);
            	        throw mse;}


            	    }
            	    break;

            	default :
            	    break loop3;
                }
            } while (true);


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "ID"

    // $ANTLR start "INT"
    public final void mINT() throws RecognitionException {
        try {
            int _type = INT;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:665:5: ( ( '0' .. '9' )+ )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:665:7: ( '0' .. '9' )+
            {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:665:7: ( '0' .. '9' )+
            int cnt4=0;
            loop4:
            do {
                int alt4=2;
                int LA4_0 = input.LA(1);

                if ( ((LA4_0>='0' && LA4_0<='9')) ) {
                    alt4=1;
                }


                switch (alt4) {
            	case 1 :
            	    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:665:7: '0' .. '9'
            	    {
            	    matchRange('0','9'); 

            	    }
            	    break;

            	default :
            	    if ( cnt4 >= 1 ) break loop4;
                        EarlyExitException eee =
                            new EarlyExitException(4, input);
                        throw eee;
                }
                cnt4++;
            } while (true);


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "INT"

    // $ANTLR start "WS"
    public final void mWS() throws RecognitionException {
        try {
            int _type = WS;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:669:5: ( ( ' ' | '\\t' ) )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:669:9: ( ' ' | '\\t' )
            {
            if ( input.LA(1)=='\t'||input.LA(1)==' ' ) {
                input.consume();

            }
            else {
                MismatchedSetException mse = new MismatchedSetException(null,input);
                recover(mse);
                throw mse;}

            _channel=HIDDEN;

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "WS"

    // $ANTLR start "KOM"
    public final void mKOM() throws RecognitionException {
        try {
            int _type = KOM;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:678:5: ( '//' (~ ( '\\n' | '\\r\\n' ) )* )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:678:7: '//' (~ ( '\\n' | '\\r\\n' ) )*
            {
            match("//"); 

            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:678:12: (~ ( '\\n' | '\\r\\n' ) )*
            loop5:
            do {
                int alt5=2;
                int LA5_0 = input.LA(1);

                if ( ((LA5_0>='\u0000' && LA5_0<='\t')||(LA5_0>='\u000B' && LA5_0<='\uFFFF')) ) {
                    alt5=1;
                }


                switch (alt5) {
            	case 1 :
            	    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:678:13: ~ ( '\\n' | '\\r\\n' )
            	    {
            	    if ( (input.LA(1)>='\u0000' && input.LA(1)<='\t')||(input.LA(1)>='\u000B' && input.LA(1)<='\uFFFF') ) {
            	        input.consume();

            	    }
            	    else {
            	        MismatchedSetException mse = new MismatchedSetException(null,input);
            	        recover(mse);
            	        throw mse;}


            	    }
            	    break;

            	default :
            	    break loop5;
                }
            } while (true);

            _channel=HIDDEN;

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KOM"

    // $ANTLR start "KOM_2"
    public final void mKOM_2() throws RecognitionException {
        try {
            int _type = KOM_2;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:679:7: ( '/*' (~ ( '*/' ) )* '*/' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:679:9: '/*' (~ ( '*/' ) )* '*/'
            {
            match("/*"); 

            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:679:14: (~ ( '*/' ) )*
            loop6:
            do {
                int alt6=2;
                int LA6_0 = input.LA(1);

                if ( (LA6_0=='*') ) {
                    int LA6_1 = input.LA(2);

                    if ( (LA6_1=='/') ) {
                        int LA6_3 = input.LA(3);

                        if ( ((LA6_3>='\u0000' && LA6_3<='\uFFFF')) ) {
                            alt6=1;
                        }


                    }
                    else if ( ((LA6_1>='\u0000' && LA6_1<='.')||(LA6_1>='0' && LA6_1<='\uFFFF')) ) {
                        alt6=1;
                    }


                }
                else if ( ((LA6_0>='\u0000' && LA6_0<=')')||(LA6_0>='+' && LA6_0<='\uFFFF')) ) {
                    alt6=1;
                }


                switch (alt6) {
            	case 1 :
            	    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:679:15: ~ ( '*/' )
            	    {
            	    if ( (input.LA(1)>='\u0000' && input.LA(1)<='\uFFFF') ) {
            	        input.consume();

            	    }
            	    else {
            	        MismatchedSetException mse = new MismatchedSetException(null,input);
            	        recover(mse);
            	        throw mse;}


            	    }
            	    break;

            	default :
            	    break loop6;
                }
            } while (true);

            match("*/"); 

            _channel=HIDDEN;

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "KOM_2"

    // $ANTLR start "NOT_1"
    public final void mNOT_1() throws RecognitionException {
        try {
            int _type = NOT_1;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:681:7: ( '!' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:681:9: '!'
            {
            match('!'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "NOT_1"

    // $ANTLR start "BR_OPEN"
    public final void mBR_OPEN() throws RecognitionException {
        try {
            int _type = BR_OPEN;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:683:9: ( '(' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:683:11: '('
            {
            match('('); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "BR_OPEN"

    // $ANTLR start "BR_CLOSE"
    public final void mBR_CLOSE() throws RecognitionException {
        try {
            int _type = BR_CLOSE;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:684:9: ( ')' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:684:11: ')'
            {
            match(')'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "BR_CLOSE"

    // $ANTLR start "QUOTE"
    public final void mQUOTE() throws RecognitionException {
        try {
            int _type = QUOTE;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:693:7: ( '\\\"' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:693:9: '\\\"'
            {
            match('\"'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "QUOTE"

    // $ANTLR start "OTHER"
    public final void mOTHER() throws RecognitionException {
        try {
            int _type = OTHER;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:695:7: ( . )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:695:9: .
            {
            matchAny(); 
            _channel=HIDDEN;

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "OTHER"

    public void mTokens() throws RecognitionException {
        // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:8: ( T__81 | T__82 | EOL | K | PKT | DPKT | NODECLARE | SC_GLOBALLY | SC_BEFORE | SC_AFTER | SC_UNTIL | SC_BETWEEN | KW_WHERE | KW_AFTER | KW_AND | KW_IT | KW_IS | KW_NEVER | KW_THE | KW_CASE | KW_THAT | KW_HOLDS | KW_AS | KW_WELL | KW_ALWAYS | KW_EVENTUALLY | KW_TRANS | KW_TO | KW_STATES | KW_IN | KW_WHICH | KW_OCCUR | KW_AT | KW_MOST | KW_TWICE | KW_IF | KW_PREV | KW_HELD | KW_SUCC | KW_BY | KW_THEN | KW_WAS | KW_PREC | KW_ONCE | KW_BECOMES | KW_SAT | KW_FOR | KW_LESS | KW_THAN | KW_DOES | KW_NOT | KW_HOLD | KW_BETW | KW_TIME | KW_UNITS | KW_LEAST | KW_EVERY | KW_ONE | KW_EXEC | KW_SEQ | KW_SUCH | KW_THERE | KW_VAR | OR_1 | OR_2 | OR_3 | AND_1 | AND_2 | OP | ID | INT | WS | KOM | KOM_2 | NOT_1 | BR_OPEN | BR_CLOSE | QUOTE | OTHER )
        int alt7=79;
        alt7 = dfa7.predict(input);
        switch (alt7) {
            case 1 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:10: T__81
                {
                mT__81(); 

                }
                break;
            case 2 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:16: T__82
                {
                mT__82(); 

                }
                break;
            case 3 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:22: EOL
                {
                mEOL(); 

                }
                break;
            case 4 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:26: K
                {
                mK(); 

                }
                break;
            case 5 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:28: PKT
                {
                mPKT(); 

                }
                break;
            case 6 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:32: DPKT
                {
                mDPKT(); 

                }
                break;
            case 7 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:37: NODECLARE
                {
                mNODECLARE(); 

                }
                break;
            case 8 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:47: SC_GLOBALLY
                {
                mSC_GLOBALLY(); 

                }
                break;
            case 9 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:59: SC_BEFORE
                {
                mSC_BEFORE(); 

                }
                break;
            case 10 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:69: SC_AFTER
                {
                mSC_AFTER(); 

                }
                break;
            case 11 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:78: SC_UNTIL
                {
                mSC_UNTIL(); 

                }
                break;
            case 12 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:87: SC_BETWEEN
                {
                mSC_BETWEEN(); 

                }
                break;
            case 13 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:98: KW_WHERE
                {
                mKW_WHERE(); 

                }
                break;
            case 14 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:107: KW_AFTER
                {
                mKW_AFTER(); 

                }
                break;
            case 15 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:116: KW_AND
                {
                mKW_AND(); 

                }
                break;
            case 16 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:123: KW_IT
                {
                mKW_IT(); 

                }
                break;
            case 17 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:129: KW_IS
                {
                mKW_IS(); 

                }
                break;
            case 18 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:135: KW_NEVER
                {
                mKW_NEVER(); 

                }
                break;
            case 19 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:144: KW_THE
                {
                mKW_THE(); 

                }
                break;
            case 20 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:151: KW_CASE
                {
                mKW_CASE(); 

                }
                break;
            case 21 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:159: KW_THAT
                {
                mKW_THAT(); 

                }
                break;
            case 22 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:167: KW_HOLDS
                {
                mKW_HOLDS(); 

                }
                break;
            case 23 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:176: KW_AS
                {
                mKW_AS(); 

                }
                break;
            case 24 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:182: KW_WELL
                {
                mKW_WELL(); 

                }
                break;
            case 25 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:190: KW_ALWAYS
                {
                mKW_ALWAYS(); 

                }
                break;
            case 26 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:200: KW_EVENTUALLY
                {
                mKW_EVENTUALLY(); 

                }
                break;
            case 27 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:214: KW_TRANS
                {
                mKW_TRANS(); 

                }
                break;
            case 28 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:223: KW_TO
                {
                mKW_TO(); 

                }
                break;
            case 29 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:229: KW_STATES
                {
                mKW_STATES(); 

                }
                break;
            case 30 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:239: KW_IN
                {
                mKW_IN(); 

                }
                break;
            case 31 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:245: KW_WHICH
                {
                mKW_WHICH(); 

                }
                break;
            case 32 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:254: KW_OCCUR
                {
                mKW_OCCUR(); 

                }
                break;
            case 33 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:263: KW_AT
                {
                mKW_AT(); 

                }
                break;
            case 34 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:269: KW_MOST
                {
                mKW_MOST(); 

                }
                break;
            case 35 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:277: KW_TWICE
                {
                mKW_TWICE(); 

                }
                break;
            case 36 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:286: KW_IF
                {
                mKW_IF(); 

                }
                break;
            case 37 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:292: KW_PREV
                {
                mKW_PREV(); 

                }
                break;
            case 38 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:300: KW_HELD
                {
                mKW_HELD(); 

                }
                break;
            case 39 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:308: KW_SUCC
                {
                mKW_SUCC(); 

                }
                break;
            case 40 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:316: KW_BY
                {
                mKW_BY(); 

                }
                break;
            case 41 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:322: KW_THEN
                {
                mKW_THEN(); 

                }
                break;
            case 42 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:330: KW_WAS
                {
                mKW_WAS(); 

                }
                break;
            case 43 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:337: KW_PREC
                {
                mKW_PREC(); 

                }
                break;
            case 44 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:345: KW_ONCE
                {
                mKW_ONCE(); 

                }
                break;
            case 45 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:353: KW_BECOMES
                {
                mKW_BECOMES(); 

                }
                break;
            case 46 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:364: KW_SAT
                {
                mKW_SAT(); 

                }
                break;
            case 47 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:371: KW_FOR
                {
                mKW_FOR(); 

                }
                break;
            case 48 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:378: KW_LESS
                {
                mKW_LESS(); 

                }
                break;
            case 49 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:386: KW_THAN
                {
                mKW_THAN(); 

                }
                break;
            case 50 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:394: KW_DOES
                {
                mKW_DOES(); 

                }
                break;
            case 51 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:402: KW_NOT
                {
                mKW_NOT(); 

                }
                break;
            case 52 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:409: KW_HOLD
                {
                mKW_HOLD(); 

                }
                break;
            case 53 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:417: KW_BETW
                {
                mKW_BETW(); 

                }
                break;
            case 54 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:425: KW_TIME
                {
                mKW_TIME(); 

                }
                break;
            case 55 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:433: KW_UNITS
                {
                mKW_UNITS(); 

                }
                break;
            case 56 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:442: KW_LEAST
                {
                mKW_LEAST(); 

                }
                break;
            case 57 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:451: KW_EVERY
                {
                mKW_EVERY(); 

                }
                break;
            case 58 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:460: KW_ONE
                {
                mKW_ONE(); 

                }
                break;
            case 59 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:467: KW_EXEC
                {
                mKW_EXEC(); 

                }
                break;
            case 60 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:475: KW_SEQ
                {
                mKW_SEQ(); 

                }
                break;
            case 61 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:482: KW_SUCH
                {
                mKW_SUCH(); 

                }
                break;
            case 62 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:490: KW_THERE
                {
                mKW_THERE(); 

                }
                break;
            case 63 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:499: KW_VAR
                {
                mKW_VAR(); 

                }
                break;
            case 64 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:506: OR_1
                {
                mOR_1(); 

                }
                break;
            case 65 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:511: OR_2
                {
                mOR_2(); 

                }
                break;
            case 66 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:516: OR_3
                {
                mOR_3(); 

                }
                break;
            case 67 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:521: AND_1
                {
                mAND_1(); 

                }
                break;
            case 68 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:527: AND_2
                {
                mAND_2(); 

                }
                break;
            case 69 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:533: OP
                {
                mOP(); 

                }
                break;
            case 70 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:536: ID
                {
                mID(); 

                }
                break;
            case 71 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:539: INT
                {
                mINT(); 

                }
                break;
            case 72 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:543: WS
                {
                mWS(); 

                }
                break;
            case 73 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:546: KOM
                {
                mKOM(); 

                }
                break;
            case 74 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:550: KOM_2
                {
                mKOM_2(); 

                }
                break;
            case 75 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:556: NOT_1
                {
                mNOT_1(); 

                }
                break;
            case 76 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:562: BR_OPEN
                {
                mBR_OPEN(); 

                }
                break;
            case 77 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:570: BR_CLOSE
                {
                mBR_CLOSE(); 

                }
                break;
            case 78 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:579: QUOTE
                {
                mQUOTE(); 

                }
                break;
            case 79 :
                // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:1:585: OTHER
                {
                mOTHER(); 

                }
                break;

        }

    }


    protected DFA7 dfa7 = new DFA7(this);
    static final String DFA7_eotS =
        "\4\uffff\1\55\4\uffff\25\66\1\uffff\1\55\1\uffff\1\55\6\uffff\1"+
        "\55\13\uffff\2\66\1\uffff\11\66\1\174\1\66\1\176\1\177\1\u0080\1"+
        "\u0081\1\u0082\2\66\1\u0086\15\66\1\u0095\2\66\1\u0098\5\66\15\uffff"+
        "\1\66\1\u00a1\12\66\1\u00ac\1\66\1\u00ae\1\uffff\1\66\5\uffff\1"+
        "\u00b2\2\66\1\uffff\15\66\1\u00c5\1\uffff\2\66\1\uffff\2\66\1\u00cb"+
        "\3\66\1\u00cf\1\66\1\uffff\11\66\1\u00da\1\uffff\1\66\1\uffff\1"+
        "\66\1\u00dd\1\66\1\uffff\1\u00df\1\u00e0\2\66\1\u00e3\1\u00e4\1"+
        "\u00e6\1\u00e7\5\66\1\u00ed\3\66\1\u00f1\1\uffff\1\u00f2\4\66\1"+
        "\uffff\1\u00f7\1\66\1\u00f9\1\uffff\1\66\1\u00fb\3\66\1\u00ff\1"+
        "\u0100\1\u0101\1\u0102\1\u0103\1\uffff\1\u0104\1\66\1\uffff\1\u0106"+
        "\2\uffff\1\66\1\u0108\2\uffff\1\u0109\2\uffff\1\66\1\u010b\3\66"+
        "\1\uffff\2\66\1\u0111\2\uffff\4\66\1\uffff\1\u0116\1\uffff\1\66"+
        "\1\uffff\1\66\1\u0119\1\66\6\uffff\1\u011b\1\uffff\1\66\2\uffff"+
        "\1\66\1\uffff\1\66\1\u011f\3\66\1\uffff\4\66\1\uffff\2\66\1\uffff"+
        "\1\u0129\1\uffff\3\66\1\uffff\5\66\1\u0132\1\u0133\1\66\1\u0135"+
        "\1\uffff\5\66\1\u013b\1\66\1\u013d\2\uffff\1\u013e\1\uffff\2\66"+
        "\1\u0141\1\u0142\1\u0143\1\uffff\1\66\2\uffff\1\66\1\u0146\3\uffff"+
        "\1\u0147\1\u0148\3\uffff";
    static final String DFA7_eofS =
        "\u0149\uffff";
    static final String DFA7_minS =
        "\1\0\3\uffff\1\12\4\uffff\1\145\1\154\1\145\1\146\1\156\1\141\2"+
        "\146\1\150\1\141\1\145\1\166\1\141\1\143\1\157\1\162\1\145\1\157"+
        "\1\145\1\157\1\141\1\uffff\1\174\1\uffff\1\46\6\uffff\1\52\13\uffff"+
        "\1\144\1\166\1\uffff\1\157\1\146\1\164\1\151\1\145\1\154\1\163\1"+
        "\164\1\144\1\60\1\167\5\60\2\141\1\60\1\151\1\155\1\163\2\154\2"+
        "\145\1\141\1\143\1\164\1\161\2\143\1\60\1\163\1\145\1\60\1\143\1"+
        "\162\1\141\1\145\1\162\15\uffff\1\145\1\60\1\145\1\142\1\157\1\167"+
        "\1\145\1\151\1\164\1\162\1\143\1\154\1\60\1\145\1\60\1\uffff\1\141"+
        "\5\uffff\1\60\2\156\1\uffff\1\143\2\145\2\144\1\156\1\143\1\164"+
        "\1\143\1\151\2\165\1\145\1\60\1\uffff\1\164\1\143\1\uffff\1\157"+
        "\1\167\1\60\3\163\1\60\1\143\1\uffff\1\162\1\141\1\162\1\145\1\162"+
        "\1\154\1\163\1\145\1\150\1\60\1\uffff\1\162\1\uffff\1\171\1\60\1"+
        "\145\1\uffff\2\60\1\163\1\145\4\60\1\164\1\171\1\165\2\145\1\60"+
        "\1\163\1\145\1\162\1\60\1\uffff\1\60\1\151\1\145\1\155\1\145\1\uffff"+
        "\1\60\1\164\1\60\1\uffff\1\154\1\60\1\154\2\145\5\60\1\uffff\1\60"+
        "\1\163\1\uffff\1\60\2\uffff\1\151\1\60\2\uffff\1\60\2\uffff\1\165"+
        "\1\60\1\164\1\163\1\145\1\uffff\1\146\1\156\1\60\2\uffff\1\157\1"+
        "\144\2\145\1\uffff\1\60\1\uffff\1\141\1\uffff\1\154\1\60\1\156\6"+
        "\uffff\1\60\1\uffff\1\164\2\uffff\1\141\1\uffff\1\151\1\60\1\144"+
        "\1\151\1\143\1\uffff\1\165\1\145\1\163\1\156\1\uffff\1\162\1\171"+
        "\1\uffff\1\60\1\uffff\1\151\1\154\1\157\1\uffff\3\145\1\163\1\144"+
        "\2\60\1\145\1\60\1\uffff\1\157\1\154\1\156\2\144\1\60\1\154\1\60"+
        "\2\uffff\1\60\1\uffff\1\156\1\171\3\60\1\uffff\1\171\2\uffff\1\163"+
        "\1\60\3\uffff\2\60\3\uffff";
    static final String DFA7_maxS =
        "\1\uffff\3\uffff\1\12\4\uffff\1\157\1\154\1\145\1\146\1\156\1\150"+
        "\2\164\1\167\1\141\1\157\1\170\1\165\1\162\1\157\1\162\1\171\1\157"+
        "\1\145\1\157\1\141\1\uffff\1\174\1\uffff\1\46\6\uffff\1\57\13\uffff"+
        "\1\164\1\166\1\uffff\1\157\3\164\1\151\1\154\1\163\1\164\1\144\1"+
        "\u00fc\1\167\5\u00fc\1\145\1\141\1\u00fc\1\151\1\155\1\163\2\154"+
        "\2\145\1\141\1\143\1\164\1\161\1\143\1\145\1\u00fc\1\163\1\145\1"+
        "\u00fc\1\164\1\162\1\163\1\145\1\162\15\uffff\1\145\1\u00fc\1\145"+
        "\1\142\1\157\1\167\1\145\1\151\1\164\1\162\1\143\1\154\1\u00fc\1"+
        "\145\1\u00fc\1\uffff\1\141\5\uffff\1\u00fc\1\164\1\156\1\uffff\1"+
        "\143\2\145\2\144\1\162\1\143\1\164\1\150\1\151\2\165\1\145\1\u00fc"+
        "\1\uffff\1\164\1\166\1\uffff\1\157\1\167\1\u00fc\3\163\1\u00fc\1"+
        "\143\1\uffff\1\162\1\141\1\162\1\145\1\162\1\154\1\163\1\145\1\150"+
        "\1\u00fc\1\uffff\1\162\1\uffff\1\171\1\u00fc\1\145\1\uffff\2\u00fc"+
        "\1\163\1\145\4\u00fc\1\164\1\171\1\165\2\145\1\u00fc\1\163\1\145"+
        "\1\162\1\u00fc\1\uffff\1\u00fc\1\151\1\145\1\155\1\145\1\uffff\1"+
        "\u00fc\1\164\1\u00fc\1\uffff\1\154\1\u00fc\1\154\2\145\5\u00fc\1"+
        "\uffff\1\u00fc\1\163\1\uffff\1\u00fc\2\uffff\1\151\1\u00fc\2\uffff"+
        "\1\u00fc\2\uffff\1\165\1\u00fc\1\164\1\163\1\145\1\uffff\1\146\1"+
        "\156\1\u00fc\2\uffff\1\157\1\144\2\145\1\uffff\1\u00fc\1\uffff\1"+
        "\141\1\uffff\1\154\1\u00fc\1\156\6\uffff\1\u00fc\1\uffff\1\164\2"+
        "\uffff\1\141\1\uffff\1\151\1\u00fc\1\144\1\151\1\143\1\uffff\1\165"+
        "\1\145\1\163\1\156\1\uffff\1\162\1\171\1\uffff\1\u00fc\1\uffff\1"+
        "\151\1\154\1\157\1\uffff\3\145\1\163\1\144\2\u00fc\1\145\1\u00fc"+
        "\1\uffff\1\157\1\154\1\156\2\144\1\u00fc\1\154\1\u00fc\2\uffff\1"+
        "\u00fc\1\uffff\1\156\1\171\3\u00fc\1\uffff\1\171\2\uffff\1\163\1"+
        "\u00fc\3\uffff\2\u00fc\3\uffff";
    static final String DFA7_acceptS =
        "\1\uffff\1\1\1\2\1\3\1\uffff\1\3\1\4\1\5\1\6\25\uffff\1\100\1\uffff"+
        "\1\103\1\uffff\3\105\1\106\1\107\1\110\1\uffff\1\113\1\114\1\115"+
        "\1\116\1\117\1\1\1\2\1\3\1\4\1\5\1\6\2\uffff\1\106\51\uffff\1\100"+
        "\1\101\1\103\1\104\1\105\1\107\1\110\1\111\1\112\1\113\1\114\1\115"+
        "\1\116\17\uffff\1\27\1\uffff\1\41\1\20\1\21\1\36\1\44\3\uffff\1"+
        "\34\16\uffff\1\102\2\uffff\1\50\10\uffff\1\63\12\uffff\1\52\1\uffff"+
        "\1\17\3\uffff\1\23\22\uffff\1\72\5\uffff\1\57\3\uffff\1\77\12\uffff"+
        "\1\30\2\uffff\1\51\1\uffff\1\25\1\61\2\uffff\1\66\1\24\1\uffff\1"+
        "\64\1\46\5\uffff\1\75\3\uffff\1\54\1\42\4\uffff\1\60\1\uffff\1\62"+
        "\1\uffff\1\22\3\uffff\1\12\1\13\1\67\1\15\1\37\1\16\1\uffff\1\76"+
        "\1\uffff\1\43\1\26\1\uffff\1\71\5\uffff\1\40\4\uffff\1\70\2\uffff"+
        "\1\11\1\uffff\1\31\3\uffff\1\35\11\uffff\1\14\10\uffff\1\55\1\65"+
        "\1\uffff\1\10\5\uffff\1\74\1\uffff\1\53\1\7\2\uffff\1\73\1\47\1"+
        "\56\2\uffff\1\32\1\45\1\33";
    static final String DFA7_specialS =
        "\1\0\u0148\uffff}>";
    static final String[] DFA7_transitionS = {
            "\11\55\1\47\1\3\2\55\1\4\22\55\1\47\1\51\1\54\3\55\1\41\1\55"+
            "\1\52\1\53\2\55\1\6\1\55\1\7\1\50\12\46\1\10\1\5\1\43\1\44\1"+
            "\42\2\55\1\14\1\13\4\45\1\12\23\45\4\55\1\45\1\55\1\17\1\31"+
            "\1\22\1\34\1\24\1\32\1\45\1\23\1\20\2\45\1\33\1\27\1\11\1\26"+
            "\1\30\2\45\1\25\1\21\1\15\1\35\1\16\3\45\1\1\1\37\1\2\106\55"+
            "\1\45\21\55\1\45\5\55\1\45\7\55\1\45\21\55\1\45\5\55\1\45\u212a"+
            "\55\1\40\1\36\uddd7\55",
            "",
            "",
            "",
            "\1\60",
            "",
            "",
            "",
            "",
            "\1\65\11\uffff\1\64",
            "\1\67",
            "\1\70",
            "\1\71",
            "\1\72",
            "\1\75\3\uffff\1\74\2\uffff\1\73",
            "\1\76\5\uffff\1\101\1\uffff\1\77\4\uffff\1\100\1\102",
            "\1\106\7\uffff\1\105\4\uffff\1\104\1\103",
            "\1\107\1\113\5\uffff\1\111\2\uffff\1\110\4\uffff\1\112",
            "\1\114",
            "\1\116\11\uffff\1\115",
            "\1\117\1\uffff\1\120",
            "\1\123\3\uffff\1\124\16\uffff\1\121\1\122",
            "\1\125\12\uffff\1\126\3\uffff\1\127",
            "\1\130",
            "\1\131",
            "\1\133\23\uffff\1\132",
            "\1\134",
            "\1\135",
            "\1\136",
            "\1\137",
            "",
            "\1\141",
            "",
            "\1\143",
            "",
            "",
            "",
            "",
            "",
            "",
            "\1\150\4\uffff\1\147",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "\1\155\17\uffff\1\156",
            "\1\157",
            "",
            "\1\160",
            "\1\161\15\uffff\1\162",
            "\1\163",
            "\1\165\12\uffff\1\164",
            "\1\166\3\uffff\1\167",
            "\1\170",
            "\1\171",
            "\1\172",
            "\1\173",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "\1\175",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "\1\u0084\3\uffff\1\u0083",
            "\1\u0085",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "\1\u0087",
            "\1\u0088",
            "\1\u0089",
            "\1\u008a",
            "\1\u008b",
            "\1\u008c",
            "\1\u008d",
            "\1\u008e",
            "\1\u008f",
            "\1\u0090",
            "\1\u0091",
            "\1\u0092",
            "\1\u0093\1\uffff\1\u0094",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "\1\u0096",
            "\1\u0097",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "\1\u0099\20\uffff\1\u009a",
            "\1\u009b",
            "\1\u009d\21\uffff\1\u009c",
            "\1\u009e",
            "\1\u009f",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "\1\u00a0",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "\1\u00a2",
            "\1\u00a3",
            "\1\u00a4",
            "\1\u00a5",
            "\1\u00a6",
            "\1\u00a7",
            "\1\u00a8",
            "\1\u00a9",
            "\1\u00aa",
            "\1\u00ab",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "\1\u00ad",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "",
            "\1\u00af",
            "",
            "",
            "",
            "",
            "",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\15\66\1\u00b0\3"+
            "\66\1\u00b1\10\66\111\uffff\1\66\21\uffff\1\66\5\uffff\1\66"+
            "\7\uffff\1\66\21\uffff\1\66\5\uffff\1\66",
            "\1\u00b4\5\uffff\1\u00b3",
            "\1\u00b5",
            "",
            "\1\u00b6",
            "\1\u00b7",
            "\1\u00b8",
            "\1\u00b9",
            "\1\u00ba",
            "\1\u00bb\3\uffff\1\u00bc",
            "\1\u00bd",
            "\1\u00be",
            "\1\u00bf\4\uffff\1\u00c0",
            "\1\u00c1",
            "\1\u00c2",
            "\1\u00c3",
            "\1\u00c4",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "",
            "\1\u00c6",
            "\1\u00c8\22\uffff\1\u00c7",
            "",
            "\1\u00c9",
            "\1\u00ca",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "\1\u00cc",
            "\1\u00cd",
            "\1\u00ce",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "\1\u00d0",
            "",
            "\1\u00d1",
            "\1\u00d2",
            "\1\u00d3",
            "\1\u00d4",
            "\1\u00d5",
            "\1\u00d6",
            "\1\u00d7",
            "\1\u00d8",
            "\1\u00d9",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "",
            "\1\u00db",
            "",
            "\1\u00dc",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "\1\u00de",
            "",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "\1\u00e1",
            "\1\u00e2",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\22\66\1\u00e5\7"+
            "\66\111\uffff\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21"+
            "\uffff\1\66\5\uffff\1\66",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "\1\u00e8",
            "\1\u00e9",
            "\1\u00ea",
            "\1\u00eb",
            "\1\u00ec",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "\1\u00ee",
            "\1\u00ef",
            "\1\u00f0",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "\1\u00f3",
            "\1\u00f4",
            "\1\u00f5",
            "\1\u00f6",
            "",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "\1\u00f8",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "",
            "\1\u00fa",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "\1\u00fc",
            "\1\u00fd",
            "\1\u00fe",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "\1\u0105",
            "",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "",
            "",
            "\1\u0107",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "",
            "",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "",
            "",
            "\1\u010a",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "\1\u010c",
            "\1\u010d",
            "\1\u010e",
            "",
            "\1\u010f",
            "\1\u0110",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "",
            "",
            "\1\u0112",
            "\1\u0113",
            "\1\u0114",
            "\1\u0115",
            "",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "",
            "\1\u0117",
            "",
            "\1\u0118",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "\1\u011a",
            "",
            "",
            "",
            "",
            "",
            "",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "",
            "\1\u011c",
            "",
            "",
            "\1\u011d",
            "",
            "\1\u011e",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "\1\u0120",
            "\1\u0121",
            "\1\u0122",
            "",
            "\1\u0123",
            "\1\u0124",
            "\1\u0125",
            "\1\u0126",
            "",
            "\1\u0127",
            "\1\u0128",
            "",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "",
            "\1\u012a",
            "\1\u012b",
            "\1\u012c",
            "",
            "\1\u012d",
            "\1\u012e",
            "\1\u012f",
            "\1\u0130",
            "\1\u0131",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "\1\u0134",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "",
            "\1\u0136",
            "\1\u0137",
            "\1\u0138",
            "\1\u0139",
            "\1\u013a",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "\1\u013c",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "",
            "",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "",
            "\1\u013f",
            "\1\u0140",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "",
            "\1\u0144",
            "",
            "",
            "\1\u0145",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "",
            "",
            "",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "\12\66\7\uffff\32\66\4\uffff\1\66\1\uffff\32\66\111\uffff"+
            "\1\66\21\uffff\1\66\5\uffff\1\66\7\uffff\1\66\21\uffff\1\66"+
            "\5\uffff\1\66",
            "",
            "",
            ""
    };

    static final short[] DFA7_eot = DFA.unpackEncodedString(DFA7_eotS);
    static final short[] DFA7_eof = DFA.unpackEncodedString(DFA7_eofS);
    static final char[] DFA7_min = DFA.unpackEncodedStringToUnsignedChars(DFA7_minS);
    static final char[] DFA7_max = DFA.unpackEncodedStringToUnsignedChars(DFA7_maxS);
    static final short[] DFA7_accept = DFA.unpackEncodedString(DFA7_acceptS);
    static final short[] DFA7_special = DFA.unpackEncodedString(DFA7_specialS);
    static final short[][] DFA7_transition;

    static {
        int numStates = DFA7_transitionS.length;
        DFA7_transition = new short[numStates][];
        for (int i=0; i<numStates; i++) {
            DFA7_transition[i] = DFA.unpackEncodedString(DFA7_transitionS[i]);
        }
    }

    class DFA7 extends DFA {

        public DFA7(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 7;
            this.eot = DFA7_eot;
            this.eof = DFA7_eof;
            this.min = DFA7_min;
            this.max = DFA7_max;
            this.accept = DFA7_accept;
            this.special = DFA7_special;
            this.transition = DFA7_transition;
        }
        public String getDescription() {
            return "1:1: Tokens : ( T__81 | T__82 | EOL | K | PKT | DPKT | NODECLARE | SC_GLOBALLY | SC_BEFORE | SC_AFTER | SC_UNTIL | SC_BETWEEN | KW_WHERE | KW_AFTER | KW_AND | KW_IT | KW_IS | KW_NEVER | KW_THE | KW_CASE | KW_THAT | KW_HOLDS | KW_AS | KW_WELL | KW_ALWAYS | KW_EVENTUALLY | KW_TRANS | KW_TO | KW_STATES | KW_IN | KW_WHICH | KW_OCCUR | KW_AT | KW_MOST | KW_TWICE | KW_IF | KW_PREV | KW_HELD | KW_SUCC | KW_BY | KW_THEN | KW_WAS | KW_PREC | KW_ONCE | KW_BECOMES | KW_SAT | KW_FOR | KW_LESS | KW_THAN | KW_DOES | KW_NOT | KW_HOLD | KW_BETW | KW_TIME | KW_UNITS | KW_LEAST | KW_EVERY | KW_ONE | KW_EXEC | KW_SEQ | KW_SUCH | KW_THERE | KW_VAR | OR_1 | OR_2 | OR_3 | AND_1 | AND_2 | OP | ID | INT | WS | KOM | KOM_2 | NOT_1 | BR_OPEN | BR_CLOSE | QUOTE | OTHER );";
        }
        public int specialStateTransition(int s, IntStream _input) throws NoViableAltException {
            IntStream input = _input;
        	int _s = s;
            switch ( s ) {
                    case 0 : 
                        int LA7_0 = input.LA(1);

                        s = -1;
                        if ( (LA7_0=='{') ) {s = 1;}

                        else if ( (LA7_0=='}') ) {s = 2;}

                        else if ( (LA7_0=='\n') ) {s = 3;}

                        else if ( (LA7_0=='\r') ) {s = 4;}

                        else if ( (LA7_0==';') ) {s = 5;}

                        else if ( (LA7_0==',') ) {s = 6;}

                        else if ( (LA7_0=='.') ) {s = 7;}

                        else if ( (LA7_0==':') ) {s = 8;}

                        else if ( (LA7_0=='n') ) {s = 9;}

                        else if ( (LA7_0=='G') ) {s = 10;}

                        else if ( (LA7_0=='B') ) {s = 11;}

                        else if ( (LA7_0=='A') ) {s = 12;}

                        else if ( (LA7_0=='u') ) {s = 13;}

                        else if ( (LA7_0=='w') ) {s = 14;}

                        else if ( (LA7_0=='a') ) {s = 15;}

                        else if ( (LA7_0=='i') ) {s = 16;}

                        else if ( (LA7_0=='t') ) {s = 17;}

                        else if ( (LA7_0=='c') ) {s = 18;}

                        else if ( (LA7_0=='h') ) {s = 19;}

                        else if ( (LA7_0=='e') ) {s = 20;}

                        else if ( (LA7_0=='s') ) {s = 21;}

                        else if ( (LA7_0=='o') ) {s = 22;}

                        else if ( (LA7_0=='m') ) {s = 23;}

                        else if ( (LA7_0=='p') ) {s = 24;}

                        else if ( (LA7_0=='b') ) {s = 25;}

                        else if ( (LA7_0=='f') ) {s = 26;}

                        else if ( (LA7_0=='l') ) {s = 27;}

                        else if ( (LA7_0=='d') ) {s = 28;}

                        else if ( (LA7_0=='v') ) {s = 29;}

                        else if ( (LA7_0=='\u2228') ) {s = 30;}

                        else if ( (LA7_0=='|') ) {s = 31;}

                        else if ( (LA7_0=='\u2227') ) {s = 32;}

                        else if ( (LA7_0=='&') ) {s = 33;}

                        else if ( (LA7_0=='>') ) {s = 34;}

                        else if ( (LA7_0=='<') ) {s = 35;}

                        else if ( (LA7_0=='=') ) {s = 36;}

                        else if ( ((LA7_0>='C' && LA7_0<='F')||(LA7_0>='H' && LA7_0<='Z')||LA7_0=='_'||LA7_0=='g'||(LA7_0>='j' && LA7_0<='k')||(LA7_0>='q' && LA7_0<='r')||(LA7_0>='x' && LA7_0<='z')||LA7_0=='\u00C4'||LA7_0=='\u00D6'||LA7_0=='\u00DC'||LA7_0=='\u00E4'||LA7_0=='\u00F6'||LA7_0=='\u00FC') ) {s = 37;}

                        else if ( ((LA7_0>='0' && LA7_0<='9')) ) {s = 38;}

                        else if ( (LA7_0=='\t'||LA7_0==' ') ) {s = 39;}

                        else if ( (LA7_0=='/') ) {s = 40;}

                        else if ( (LA7_0=='!') ) {s = 41;}

                        else if ( (LA7_0=='(') ) {s = 42;}

                        else if ( (LA7_0==')') ) {s = 43;}

                        else if ( (LA7_0=='\"') ) {s = 44;}

                        else if ( ((LA7_0>='\u0000' && LA7_0<='\b')||(LA7_0>='\u000B' && LA7_0<='\f')||(LA7_0>='\u000E' && LA7_0<='\u001F')||(LA7_0>='#' && LA7_0<='%')||LA7_0=='\''||(LA7_0>='*' && LA7_0<='+')||LA7_0=='-'||(LA7_0>='?' && LA7_0<='@')||(LA7_0>='[' && LA7_0<='^')||LA7_0=='`'||(LA7_0>='~' && LA7_0<='\u00C3')||(LA7_0>='\u00C5' && LA7_0<='\u00D5')||(LA7_0>='\u00D7' && LA7_0<='\u00DB')||(LA7_0>='\u00DD' && LA7_0<='\u00E3')||(LA7_0>='\u00E5' && LA7_0<='\u00F5')||(LA7_0>='\u00F7' && LA7_0<='\u00FB')||(LA7_0>='\u00FD' && LA7_0<='\u2226')||(LA7_0>='\u2229' && LA7_0<='\uFFFF')) ) {s = 45;}

                        if ( s>=0 ) return s;
                        break;
            }
            NoViableAltException nvae =
                new NoViableAltException(getDescription(), 7, _s, input);
            error(nvae);
            throw nvae;
        }
    }
 

}