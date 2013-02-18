// $ANTLR 3.2 Sep 23, 2009 12:02:23 Console.g 2011-03-21 10:47:53

package local.stalin.interactiveconsole;


import org.antlr.runtime.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;

public class ConsoleParser extends Parser {
    public static final String[] tokenNames = new String[] {
        "<invalid>", "<EOR>", "<DOWN>", "<UP>", "HELP_T", "EXIT_T", "LIST_T", "USE_T", "ON_T", "SETPRELUDE_T", "DELETEMM_T", "LISTMM_T", "RERUN_T", "SETRESULTOUTPUT_T", "LOADPREFS_T", "LETTER", "DIGIT", "PATHSEPARATOR", "FILECHAR", "NUMBER", "FILE_NAME", "WS", "'current'", "'('", "')*'"
    };
    public static final int EXIT_T=5;
    public static final int RERUN_T=12;
    public static final int T__24=24;
    public static final int SETRESULTOUTPUT_T=13;
    public static final int T__23=23;
    public static final int LETTER=15;
    public static final int T__22=22;
    public static final int LISTMM_T=11;
    public static final int SETPRELUDE_T=9;
    public static final int NUMBER=19;
    public static final int EOF=-1;
    public static final int LIST_T=6;
    public static final int WS=21;
    public static final int ON_T=8;
    public static final int USE_T=7;
    public static final int LOADPREFS_T=14;
    public static final int HELP_T=4;
    public static final int FILE_NAME=20;
    public static final int DELETEMM_T=10;
    public static final int DIGIT=16;
    public static final int PATHSEPARATOR=17;
    public static final int FILECHAR=18;

    // delegates
    // delegators


        public ConsoleParser(TokenStream input) {
            this(input, new RecognizerSharedState());
        }
        public ConsoleParser(TokenStream input, RecognizerSharedState state) {
            super(input, state);
             
        }
        

    public String[] getTokenNames() { return ConsoleParser.tokenNames; }
    public String getGrammarFileName() { return "Console.g"; }



    // $ANTLR start "cmdline"
    // Console.g:67:1: cmdline returns [Stmt s] : ( HELP_T | EXIT_T | LIST_T | USE_T t= tcd ON_T f= FILE_NAME | SETPRELUDE_T f= FILE_NAME | LISTMM_T | DELETEMM_T n= NUMBER | RERUN_T | SETRESULTOUTPUT_T f= FILE_NAME | LOADPREFS_T f= FILE_NAME );
    public final Stmt cmdline() throws RecognitionException {
        Stmt s = null;

        Token f=null;
        Token n=null;
        TC t = null;


        try {
            // Console.g:68:5: ( HELP_T | EXIT_T | LIST_T | USE_T t= tcd ON_T f= FILE_NAME | SETPRELUDE_T f= FILE_NAME | LISTMM_T | DELETEMM_T n= NUMBER | RERUN_T | SETRESULTOUTPUT_T f= FILE_NAME | LOADPREFS_T f= FILE_NAME )
            int alt1=10;
            switch ( input.LA(1) ) {
            case HELP_T:
                {
                alt1=1;
                }
                break;
            case EXIT_T:
                {
                alt1=2;
                }
                break;
            case LIST_T:
                {
                alt1=3;
                }
                break;
            case USE_T:
                {
                alt1=4;
                }
                break;
            case SETPRELUDE_T:
                {
                alt1=5;
                }
                break;
            case LISTMM_T:
                {
                alt1=6;
                }
                break;
            case DELETEMM_T:
                {
                alt1=7;
                }
                break;
            case RERUN_T:
                {
                alt1=8;
                }
                break;
            case SETRESULTOUTPUT_T:
                {
                alt1=9;
                }
                break;
            case LOADPREFS_T:
                {
                alt1=10;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("", 1, 0, input);

                throw nvae;
            }

            switch (alt1) {
                case 1 :
                    // Console.g:68:7: HELP_T
                    {
                    match(input,HELP_T,FOLLOW_HELP_T_in_cmdline405); 
                     s = new HelpStmt();  

                    }
                    break;
                case 2 :
                    // Console.g:70:7: EXIT_T
                    {
                    match(input,EXIT_T,FOLLOW_EXIT_T_in_cmdline420); 
                     s = new ExitStmt(); 

                    }
                    break;
                case 3 :
                    // Console.g:72:7: LIST_T
                    {
                    match(input,LIST_T,FOLLOW_LIST_T_in_cmdline435); 
                     s = new ListStmt(); 

                    }
                    break;
                case 4 :
                    // Console.g:74:7: USE_T t= tcd ON_T f= FILE_NAME
                    {
                    match(input,USE_T,FOLLOW_USE_T_in_cmdline450); 
                    pushFollow(FOLLOW_tcd_in_cmdline454);
                    t=tcd();

                    state._fsp--;

                    match(input,ON_T,FOLLOW_ON_T_in_cmdline456); 
                    f=(Token)match(input,FILE_NAME,FOLLOW_FILE_NAME_in_cmdline460); 
                     s = new UseStmt(t, (f!=null?f.getText():null)); 

                    }
                    break;
                case 5 :
                    // Console.g:76:7: SETPRELUDE_T f= FILE_NAME
                    {
                    match(input,SETPRELUDE_T,FOLLOW_SETPRELUDE_T_in_cmdline475); 
                    f=(Token)match(input,FILE_NAME,FOLLOW_FILE_NAME_in_cmdline479); 
                     s = new SetPreludeStmt((f!=null?f.getText():null)); 

                    }
                    break;
                case 6 :
                    // Console.g:78:7: LISTMM_T
                    {
                    match(input,LISTMM_T,FOLLOW_LISTMM_T_in_cmdline494); 
                     s = new ListMMStmt(); 

                    }
                    break;
                case 7 :
                    // Console.g:80:7: DELETEMM_T n= NUMBER
                    {
                    match(input,DELETEMM_T,FOLLOW_DELETEMM_T_in_cmdline509); 
                    n=(Token)match(input,NUMBER,FOLLOW_NUMBER_in_cmdline513); 
                     s = new DeleteMMStmt((n!=null?n.getText():null)); 

                    }
                    break;
                case 8 :
                    // Console.g:82:7: RERUN_T
                    {
                    match(input,RERUN_T,FOLLOW_RERUN_T_in_cmdline528); 
                     s = new RerunStmt(); 

                    }
                    break;
                case 9 :
                    // Console.g:84:7: SETRESULTOUTPUT_T f= FILE_NAME
                    {
                    match(input,SETRESULTOUTPUT_T,FOLLOW_SETRESULTOUTPUT_T_in_cmdline543); 
                    f=(Token)match(input,FILE_NAME,FOLLOW_FILE_NAME_in_cmdline547); 
                     s = new SetResultOutputStmt((f!=null?f.getText():null)); 

                    }
                    break;
                case 10 :
                    // Console.g:86:7: LOADPREFS_T f= FILE_NAME
                    {
                    match(input,LOADPREFS_T,FOLLOW_LOADPREFS_T_in_cmdline562); 
                    f=(Token)match(input,FILE_NAME,FOLLOW_FILE_NAME_in_cmdline566); 
                     s = new LoadPrefsStmt((f!=null?f.getText():null)); 

                    }
                    break;

            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return s;
    }
    // $ANTLR end "cmdline"


    // $ANTLR start "tcd"
    // Console.g:91:1: tcd returns [TC tcd] : ( 'current' | f= FILE_NAME | n= ntcd );
    public final TC tcd() throws RecognitionException {
        TC tcd = null;

        Token f=null;
        TCnew n = null;


        try {
            // Console.g:92:2: ( 'current' | f= FILE_NAME | n= ntcd )
            int alt2=3;
            switch ( input.LA(1) ) {
            case 22:
                {
                alt2=1;
                }
                break;
            case FILE_NAME:
                {
                alt2=2;
                }
                break;
            case NUMBER:
            case 23:
                {
                alt2=3;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("", 2, 0, input);

                throw nvae;
            }

            switch (alt2) {
                case 1 :
                    // Console.g:92:4: 'current'
                    {
                    match(input,22,FOLLOW_22_in_tcd592); 
                     tcd = new TCcurrent(); 

                    }
                    break;
                case 2 :
                    // Console.g:94:4: f= FILE_NAME
                    {
                    f=(Token)match(input,FILE_NAME,FOLLOW_FILE_NAME_in_tcd603); 
                     tcd = new TCfile((f!=null?f.getText():null)); 

                    }
                    break;
                case 3 :
                    // Console.g:96:4: n= ntcd
                    {
                    pushFollow(FOLLOW_ntcd_in_tcd616);
                    n=ntcd();

                    state._fsp--;

                     tcd = n; 

                    }
                    break;

            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return tcd;
    }
    // $ANTLR end "tcd"


    // $ANTLR start "ntcd"
    // Console.g:102:1: ntcd returns [TCnew ntcd] : (nmb= NUMBER (next= ntcd )? | '(' sbc= ntcd ')*' (next= ntcd )? );
    public final TCnew ntcd() throws RecognitionException {
        TCnew ntcd = null;

        Token nmb=null;
        TCnew next = null;

        TCnew sbc = null;


        try {
            // Console.g:103:2: (nmb= NUMBER (next= ntcd )? | '(' sbc= ntcd ')*' (next= ntcd )? )
            int alt5=2;
            int LA5_0 = input.LA(1);

            if ( (LA5_0==NUMBER) ) {
                alt5=1;
            }
            else if ( (LA5_0==23) ) {
                alt5=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 5, 0, input);

                throw nvae;
            }
            switch (alt5) {
                case 1 :
                    // Console.g:103:4: nmb= NUMBER (next= ntcd )?
                    {
                    nmb=(Token)match(input,NUMBER,FOLLOW_NUMBER_in_ntcd642); 
                    // Console.g:103:18: (next= ntcd )?
                    int alt3=2;
                    int LA3_0 = input.LA(1);

                    if ( (LA3_0==NUMBER||LA3_0==23) ) {
                        alt3=1;
                    }
                    switch (alt3) {
                        case 1 :
                            // Console.g:103:19: next= ntcd
                            {
                            pushFollow(FOLLOW_ntcd_in_ntcd650);
                            next=ntcd();

                            state._fsp--;


                            }
                            break;

                    }

                     ntcd = new TCPlugin((nmb!=null?nmb.getText():null), next); 

                    }
                    break;
                case 2 :
                    // Console.g:105:4: '(' sbc= ntcd ')*' (next= ntcd )?
                    {
                    match(input,23,FOLLOW_23_in_ntcd661); 
                    pushFollow(FOLLOW_ntcd_in_ntcd667);
                    sbc=ntcd();

                    state._fsp--;

                    match(input,24,FOLLOW_24_in_ntcd669); 
                    // Console.g:105:25: (next= ntcd )?
                    int alt4=2;
                    int LA4_0 = input.LA(1);

                    if ( (LA4_0==NUMBER||LA4_0==23) ) {
                        alt4=1;
                    }
                    switch (alt4) {
                        case 1 :
                            // Console.g:105:26: next= ntcd
                            {
                            pushFollow(FOLLOW_ntcd_in_ntcd677);
                            next=ntcd();

                            state._fsp--;


                            }
                            break;

                    }

                     ntcd = new TCSubchain(sbc, next); 

                    }
                    break;

            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ntcd;
    }
    // $ANTLR end "ntcd"

    // Delegated rules


 

    public static final BitSet FOLLOW_HELP_T_in_cmdline405 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_EXIT_T_in_cmdline420 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_LIST_T_in_cmdline435 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_USE_T_in_cmdline450 = new BitSet(new long[]{0x0000000000D80000L});
    public static final BitSet FOLLOW_tcd_in_cmdline454 = new BitSet(new long[]{0x0000000000000100L});
    public static final BitSet FOLLOW_ON_T_in_cmdline456 = new BitSet(new long[]{0x0000000000100000L});
    public static final BitSet FOLLOW_FILE_NAME_in_cmdline460 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_SETPRELUDE_T_in_cmdline475 = new BitSet(new long[]{0x0000000000100000L});
    public static final BitSet FOLLOW_FILE_NAME_in_cmdline479 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_LISTMM_T_in_cmdline494 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_DELETEMM_T_in_cmdline509 = new BitSet(new long[]{0x0000000000080000L});
    public static final BitSet FOLLOW_NUMBER_in_cmdline513 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_RERUN_T_in_cmdline528 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_SETRESULTOUTPUT_T_in_cmdline543 = new BitSet(new long[]{0x0000000000100000L});
    public static final BitSet FOLLOW_FILE_NAME_in_cmdline547 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_LOADPREFS_T_in_cmdline562 = new BitSet(new long[]{0x0000000000100000L});
    public static final BitSet FOLLOW_FILE_NAME_in_cmdline566 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_22_in_tcd592 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_FILE_NAME_in_tcd603 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ntcd_in_tcd616 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_NUMBER_in_ntcd642 = new BitSet(new long[]{0x0000000000D80002L});
    public static final BitSet FOLLOW_ntcd_in_ntcd650 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_23_in_ntcd661 = new BitSet(new long[]{0x0000000000D80000L});
    public static final BitSet FOLLOW_ntcd_in_ntcd667 = new BitSet(new long[]{0x0000000001000000L});
    public static final BitSet FOLLOW_24_in_ntcd669 = new BitSet(new long[]{0x0000000000D80002L});
    public static final BitSet FOLLOW_ntcd_in_ntcd677 = new BitSet(new long[]{0x0000000000000002L});

}