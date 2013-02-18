// $ANTLR 3.2 Sep 23, 2009 12:02:23 Console.g 2011-03-21 10:47:54

package local.stalin.interactiveconsole;


import org.antlr.runtime.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;

public class ConsoleLexer extends Lexer {
    public static final int EXIT_T=5;
    public static final int RERUN_T=12;
    public static final int SETRESULTOUTPUT_T=13;
    public static final int T__24=24;
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
    public static final int DIGIT=16;
    public static final int DELETEMM_T=10;
    public static final int PATHSEPARATOR=17;
    public static final int FILECHAR=18;

    // delegates
    // delegators

    public ConsoleLexer() {;} 
    public ConsoleLexer(CharStream input) {
        this(input, new RecognizerSharedState());
    }
    public ConsoleLexer(CharStream input, RecognizerSharedState state) {
        super(input,state);

    }
    public String getGrammarFileName() { return "Console.g"; }

    // $ANTLR start "T__22"
    public final void mT__22() throws RecognitionException {
        try {
            int _type = T__22;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Console.g:7:7: ( 'current' )
            // Console.g:7:9: 'current'
            {
            match("current"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__22"

    // $ANTLR start "T__23"
    public final void mT__23() throws RecognitionException {
        try {
            int _type = T__23;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Console.g:8:7: ( '(' )
            // Console.g:8:9: '('
            {
            match('('); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__23"

    // $ANTLR start "T__24"
    public final void mT__24() throws RecognitionException {
        try {
            int _type = T__24;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Console.g:9:7: ( ')*' )
            // Console.g:9:9: ')*'
            {
            match(")*"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__24"

    // $ANTLR start "HELP_T"
    public final void mHELP_T() throws RecognitionException {
        try {
            int _type = HELP_T;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Console.g:30:8: ( ( 'help' | 'HELP' ) )
            // Console.g:30:11: ( 'help' | 'HELP' )
            {
            // Console.g:30:11: ( 'help' | 'HELP' )
            int alt1=2;
            int LA1_0 = input.LA(1);

            if ( (LA1_0=='h') ) {
                alt1=1;
            }
            else if ( (LA1_0=='H') ) {
                alt1=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 1, 0, input);

                throw nvae;
            }
            switch (alt1) {
                case 1 :
                    // Console.g:30:12: 'help'
                    {
                    match("help"); 


                    }
                    break;
                case 2 :
                    // Console.g:31:6: 'HELP'
                    {
                    match("HELP"); 


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
    // $ANTLR end "HELP_T"

    // $ANTLR start "EXIT_T"
    public final void mEXIT_T() throws RecognitionException {
        try {
            int _type = EXIT_T;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Console.g:32:8: ( ( 'exit' | 'EXIT' ) )
            // Console.g:32:10: ( 'exit' | 'EXIT' )
            {
            // Console.g:32:10: ( 'exit' | 'EXIT' )
            int alt2=2;
            int LA2_0 = input.LA(1);

            if ( (LA2_0=='e') ) {
                alt2=1;
            }
            else if ( (LA2_0=='E') ) {
                alt2=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 2, 0, input);

                throw nvae;
            }
            switch (alt2) {
                case 1 :
                    // Console.g:32:11: 'exit'
                    {
                    match("exit"); 


                    }
                    break;
                case 2 :
                    // Console.g:33:6: 'EXIT'
                    {
                    match("EXIT"); 


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
    // $ANTLR end "EXIT_T"

    // $ANTLR start "LIST_T"
    public final void mLIST_T() throws RecognitionException {
        try {
            int _type = LIST_T;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Console.g:34:8: ( ( 'list' | 'LIST' ) )
            // Console.g:34:10: ( 'list' | 'LIST' )
            {
            // Console.g:34:10: ( 'list' | 'LIST' )
            int alt3=2;
            int LA3_0 = input.LA(1);

            if ( (LA3_0=='l') ) {
                alt3=1;
            }
            else if ( (LA3_0=='L') ) {
                alt3=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 3, 0, input);

                throw nvae;
            }
            switch (alt3) {
                case 1 :
                    // Console.g:34:11: 'list'
                    {
                    match("list"); 


                    }
                    break;
                case 2 :
                    // Console.g:35:6: 'LIST'
                    {
                    match("LIST"); 


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
    // $ANTLR end "LIST_T"

    // $ANTLR start "USE_T"
    public final void mUSE_T() throws RecognitionException {
        try {
            int _type = USE_T;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Console.g:36:7: ( ( 'use' | 'USE' ) )
            // Console.g:36:9: ( 'use' | 'USE' )
            {
            // Console.g:36:9: ( 'use' | 'USE' )
            int alt4=2;
            int LA4_0 = input.LA(1);

            if ( (LA4_0=='u') ) {
                alt4=1;
            }
            else if ( (LA4_0=='U') ) {
                alt4=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 4, 0, input);

                throw nvae;
            }
            switch (alt4) {
                case 1 :
                    // Console.g:36:10: 'use'
                    {
                    match("use"); 


                    }
                    break;
                case 2 :
                    // Console.g:37:6: 'USE'
                    {
                    match("USE"); 


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
    // $ANTLR end "USE_T"

    // $ANTLR start "ON_T"
    public final void mON_T() throws RecognitionException {
        try {
            int _type = ON_T;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Console.g:38:6: ( ( 'on' | 'ON' ) )
            // Console.g:38:8: ( 'on' | 'ON' )
            {
            // Console.g:38:8: ( 'on' | 'ON' )
            int alt5=2;
            int LA5_0 = input.LA(1);

            if ( (LA5_0=='o') ) {
                alt5=1;
            }
            else if ( (LA5_0=='O') ) {
                alt5=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 5, 0, input);

                throw nvae;
            }
            switch (alt5) {
                case 1 :
                    // Console.g:38:9: 'on'
                    {
                    match("on"); 


                    }
                    break;
                case 2 :
                    // Console.g:39:6: 'ON'
                    {
                    match("ON"); 


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
    // $ANTLR end "ON_T"

    // $ANTLR start "SETPRELUDE_T"
    public final void mSETPRELUDE_T() throws RecognitionException {
        try {
            int _type = SETPRELUDE_T;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Console.g:40:14: ( ( 'set prelude' | 'SET PRELUDE' ) )
            // Console.g:40:16: ( 'set prelude' | 'SET PRELUDE' )
            {
            // Console.g:40:16: ( 'set prelude' | 'SET PRELUDE' )
            int alt6=2;
            int LA6_0 = input.LA(1);

            if ( (LA6_0=='s') ) {
                alt6=1;
            }
            else if ( (LA6_0=='S') ) {
                alt6=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 6, 0, input);

                throw nvae;
            }
            switch (alt6) {
                case 1 :
                    // Console.g:40:17: 'set prelude'
                    {
                    match("set prelude"); 


                    }
                    break;
                case 2 :
                    // Console.g:41:8: 'SET PRELUDE'
                    {
                    match("SET PRELUDE"); 


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
    // $ANTLR end "SETPRELUDE_T"

    // $ANTLR start "DELETEMM_T"
    public final void mDELETEMM_T() throws RecognitionException {
        try {
            int _type = DELETEMM_T;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Console.g:42:12: ( ( 'deletemm' | 'DELETEMM' ) )
            // Console.g:42:14: ( 'deletemm' | 'DELETEMM' )
            {
            // Console.g:42:14: ( 'deletemm' | 'DELETEMM' )
            int alt7=2;
            int LA7_0 = input.LA(1);

            if ( (LA7_0=='d') ) {
                alt7=1;
            }
            else if ( (LA7_0=='D') ) {
                alt7=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 7, 0, input);

                throw nvae;
            }
            switch (alt7) {
                case 1 :
                    // Console.g:42:15: 'deletemm'
                    {
                    match("deletemm"); 


                    }
                    break;
                case 2 :
                    // Console.g:43:7: 'DELETEMM'
                    {
                    match("DELETEMM"); 


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
    // $ANTLR end "DELETEMM_T"

    // $ANTLR start "LISTMM_T"
    public final void mLISTMM_T() throws RecognitionException {
        try {
            int _type = LISTMM_T;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Console.g:44:10: ( ( 'listmm' | 'LISTMM' ) )
            // Console.g:44:12: ( 'listmm' | 'LISTMM' )
            {
            // Console.g:44:12: ( 'listmm' | 'LISTMM' )
            int alt8=2;
            int LA8_0 = input.LA(1);

            if ( (LA8_0=='l') ) {
                alt8=1;
            }
            else if ( (LA8_0=='L') ) {
                alt8=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 8, 0, input);

                throw nvae;
            }
            switch (alt8) {
                case 1 :
                    // Console.g:44:13: 'listmm'
                    {
                    match("listmm"); 


                    }
                    break;
                case 2 :
                    // Console.g:45:7: 'LISTMM'
                    {
                    match("LISTMM"); 


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
    // $ANTLR end "LISTMM_T"

    // $ANTLR start "RERUN_T"
    public final void mRERUN_T() throws RecognitionException {
        try {
            int _type = RERUN_T;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Console.g:46:10: ( 'rerun' )
            // Console.g:46:12: 'rerun'
            {
            match("rerun"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "RERUN_T"

    // $ANTLR start "SETRESULTOUTPUT_T"
    public final void mSETRESULTOUTPUT_T() throws RecognitionException {
        try {
            int _type = SETRESULTOUTPUT_T;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Console.g:47:19: ( ( 'output result to' | 'OUTPUT RESULT TO' ) )
            // Console.g:47:21: ( 'output result to' | 'OUTPUT RESULT TO' )
            {
            // Console.g:47:21: ( 'output result to' | 'OUTPUT RESULT TO' )
            int alt9=2;
            int LA9_0 = input.LA(1);

            if ( (LA9_0=='o') ) {
                alt9=1;
            }
            else if ( (LA9_0=='O') ) {
                alt9=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 9, 0, input);

                throw nvae;
            }
            switch (alt9) {
                case 1 :
                    // Console.g:47:22: 'output result to'
                    {
                    match("output result to"); 


                    }
                    break;
                case 2 :
                    // Console.g:48:9: 'OUTPUT RESULT TO'
                    {
                    match("OUTPUT RESULT TO"); 


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
    // $ANTLR end "SETRESULTOUTPUT_T"

    // $ANTLR start "LOADPREFS_T"
    public final void mLOADPREFS_T() throws RecognitionException {
        try {
            int _type = LOADPREFS_T;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Console.g:50:14: ( ( 'load preferences from' ) | ( 'LOAD PREFERENCES FROM' ) )
            int alt10=2;
            int LA10_0 = input.LA(1);

            if ( (LA10_0=='l') ) {
                alt10=1;
            }
            else if ( (LA10_0=='L') ) {
                alt10=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 10, 0, input);

                throw nvae;
            }
            switch (alt10) {
                case 1 :
                    // Console.g:50:16: ( 'load preferences from' )
                    {
                    // Console.g:50:16: ( 'load preferences from' )
                    // Console.g:50:17: 'load preferences from'
                    {
                    match("load preferences from"); 


                    }


                    }
                    break;
                case 2 :
                    // Console.g:51:7: ( 'LOAD PREFERENCES FROM' )
                    {
                    // Console.g:51:7: ( 'LOAD PREFERENCES FROM' )
                    // Console.g:51:8: 'LOAD PREFERENCES FROM'
                    {
                    match("LOAD PREFERENCES FROM"); 


                    }


                    }
                    break;

            }
            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "LOADPREFS_T"

    // $ANTLR start "LETTER"
    public final void mLETTER() throws RecognitionException {
        try {
            // Console.g:53:21: ( ( 'a' .. 'z' | 'A' .. 'Z' ) )
            // Console.g:53:24: ( 'a' .. 'z' | 'A' .. 'Z' )
            {
            if ( (input.LA(1)>='A' && input.LA(1)<='Z')||(input.LA(1)>='a' && input.LA(1)<='z') ) {
                input.consume();

            }
            else {
                MismatchedSetException mse = new MismatchedSetException(null,input);
                recover(mse);
                throw mse;}


            }

        }
        finally {
        }
    }
    // $ANTLR end "LETTER"

    // $ANTLR start "DIGIT"
    public final void mDIGIT() throws RecognitionException {
        try {
            // Console.g:54:21: ( '0' .. '9' )
            // Console.g:54:24: '0' .. '9'
            {
            matchRange('0','9'); 

            }

        }
        finally {
        }
    }
    // $ANTLR end "DIGIT"

    // $ANTLR start "PATHSEPARATOR"
    public final void mPATHSEPARATOR() throws RecognitionException {
        try {
            // Console.g:56:24: ( ( '\\/' | '\\\\' ) )
            // Console.g:56:26: ( '\\/' | '\\\\' )
            {
            if ( input.LA(1)=='/'||input.LA(1)=='\\' ) {
                input.consume();

            }
            else {
                MismatchedSetException mse = new MismatchedSetException(null,input);
                recover(mse);
                throw mse;}


            }

        }
        finally {
        }
    }
    // $ANTLR end "PATHSEPARATOR"

    // $ANTLR start "FILECHAR"
    public final void mFILECHAR() throws RecognitionException {
        try {
            // Console.g:58:19: ( ( LETTER | DIGIT | '_' | '-' | ',' | ':' | '.' ) )
            // Console.g:58:21: ( LETTER | DIGIT | '_' | '-' | ',' | ':' | '.' )
            {
            if ( (input.LA(1)>=',' && input.LA(1)<='.')||(input.LA(1)>='0' && input.LA(1)<=':')||(input.LA(1)>='A' && input.LA(1)<='Z')||input.LA(1)=='_'||(input.LA(1)>='a' && input.LA(1)<='z') ) {
                input.consume();

            }
            else {
                MismatchedSetException mse = new MismatchedSetException(null,input);
                recover(mse);
                throw mse;}


            }

        }
        finally {
        }
    }
    // $ANTLR end "FILECHAR"

    // $ANTLR start "NUMBER"
    public final void mNUMBER() throws RecognitionException {
        try {
            int _type = NUMBER;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Console.g:60:12: ( ( DIGIT )+ )
            // Console.g:60:14: ( DIGIT )+
            {
            // Console.g:60:14: ( DIGIT )+
            int cnt11=0;
            loop11:
            do {
                int alt11=2;
                int LA11_0 = input.LA(1);

                if ( ((LA11_0>='0' && LA11_0<='9')) ) {
                    alt11=1;
                }


                switch (alt11) {
            	case 1 :
            	    // Console.g:60:14: DIGIT
            	    {
            	    mDIGIT(); 

            	    }
            	    break;

            	default :
            	    if ( cnt11 >= 1 ) break loop11;
                        EarlyExitException eee =
                            new EarlyExitException(11, input);
                        throw eee;
                }
                cnt11++;
            } while (true);


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "NUMBER"

    // $ANTLR start "FILE_NAME"
    public final void mFILE_NAME() throws RecognitionException {
        try {
            int _type = FILE_NAME;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Console.g:63:11: ( ( PATHSEPARATOR )? ( FILECHAR ( PATHSEPARATOR )? )+ )
            // Console.g:63:13: ( PATHSEPARATOR )? ( FILECHAR ( PATHSEPARATOR )? )+
            {
            // Console.g:63:13: ( PATHSEPARATOR )?
            int alt12=2;
            int LA12_0 = input.LA(1);

            if ( (LA12_0=='/'||LA12_0=='\\') ) {
                alt12=1;
            }
            switch (alt12) {
                case 1 :
                    // Console.g:63:13: PATHSEPARATOR
                    {
                    mPATHSEPARATOR(); 

                    }
                    break;

            }

            // Console.g:63:28: ( FILECHAR ( PATHSEPARATOR )? )+
            int cnt14=0;
            loop14:
            do {
                int alt14=2;
                int LA14_0 = input.LA(1);

                if ( ((LA14_0>=',' && LA14_0<='.')||(LA14_0>='0' && LA14_0<=':')||(LA14_0>='A' && LA14_0<='Z')||LA14_0=='_'||(LA14_0>='a' && LA14_0<='z')) ) {
                    alt14=1;
                }


                switch (alt14) {
            	case 1 :
            	    // Console.g:63:29: FILECHAR ( PATHSEPARATOR )?
            	    {
            	    mFILECHAR(); 
            	    // Console.g:63:38: ( PATHSEPARATOR )?
            	    int alt13=2;
            	    int LA13_0 = input.LA(1);

            	    if ( (LA13_0=='/'||LA13_0=='\\') ) {
            	        alt13=1;
            	    }
            	    switch (alt13) {
            	        case 1 :
            	            // Console.g:63:38: PATHSEPARATOR
            	            {
            	            mPATHSEPARATOR(); 

            	            }
            	            break;

            	    }


            	    }
            	    break;

            	default :
            	    if ( cnt14 >= 1 ) break loop14;
                        EarlyExitException eee =
                            new EarlyExitException(14, input);
                        throw eee;
                }
                cnt14++;
            } while (true);


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "FILE_NAME"

    // $ANTLR start "WS"
    public final void mWS() throws RecognitionException {
        try {
            int _type = WS;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // Console.g:65:12: ( ( ' ' | '\\t' | '\\r' | '\\n' )+ )
            // Console.g:65:15: ( ' ' | '\\t' | '\\r' | '\\n' )+
            {
            // Console.g:65:15: ( ' ' | '\\t' | '\\r' | '\\n' )+
            int cnt15=0;
            loop15:
            do {
                int alt15=2;
                int LA15_0 = input.LA(1);

                if ( ((LA15_0>='\t' && LA15_0<='\n')||LA15_0=='\r'||LA15_0==' ') ) {
                    alt15=1;
                }


                switch (alt15) {
            	case 1 :
            	    // Console.g:
            	    {
            	    if ( (input.LA(1)>='\t' && input.LA(1)<='\n')||input.LA(1)=='\r'||input.LA(1)==' ' ) {
            	        input.consume();

            	    }
            	    else {
            	        MismatchedSetException mse = new MismatchedSetException(null,input);
            	        recover(mse);
            	        throw mse;}


            	    }
            	    break;

            	default :
            	    if ( cnt15 >= 1 ) break loop15;
                        EarlyExitException eee =
                            new EarlyExitException(15, input);
                        throw eee;
                }
                cnt15++;
            } while (true);

             skip(); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "WS"

    public void mTokens() throws RecognitionException {
        // Console.g:1:8: ( T__22 | T__23 | T__24 | HELP_T | EXIT_T | LIST_T | USE_T | ON_T | SETPRELUDE_T | DELETEMM_T | LISTMM_T | RERUN_T | SETRESULTOUTPUT_T | LOADPREFS_T | NUMBER | FILE_NAME | WS )
        int alt16=17;
        alt16 = dfa16.predict(input);
        switch (alt16) {
            case 1 :
                // Console.g:1:10: T__22
                {
                mT__22(); 

                }
                break;
            case 2 :
                // Console.g:1:16: T__23
                {
                mT__23(); 

                }
                break;
            case 3 :
                // Console.g:1:22: T__24
                {
                mT__24(); 

                }
                break;
            case 4 :
                // Console.g:1:28: HELP_T
                {
                mHELP_T(); 

                }
                break;
            case 5 :
                // Console.g:1:35: EXIT_T
                {
                mEXIT_T(); 

                }
                break;
            case 6 :
                // Console.g:1:42: LIST_T
                {
                mLIST_T(); 

                }
                break;
            case 7 :
                // Console.g:1:49: USE_T
                {
                mUSE_T(); 

                }
                break;
            case 8 :
                // Console.g:1:55: ON_T
                {
                mON_T(); 

                }
                break;
            case 9 :
                // Console.g:1:60: SETPRELUDE_T
                {
                mSETPRELUDE_T(); 

                }
                break;
            case 10 :
                // Console.g:1:73: DELETEMM_T
                {
                mDELETEMM_T(); 

                }
                break;
            case 11 :
                // Console.g:1:84: LISTMM_T
                {
                mLISTMM_T(); 

                }
                break;
            case 12 :
                // Console.g:1:93: RERUN_T
                {
                mRERUN_T(); 

                }
                break;
            case 13 :
                // Console.g:1:101: SETRESULTOUTPUT_T
                {
                mSETRESULTOUTPUT_T(); 

                }
                break;
            case 14 :
                // Console.g:1:119: LOADPREFS_T
                {
                mLOADPREFS_T(); 

                }
                break;
            case 15 :
                // Console.g:1:131: NUMBER
                {
                mNUMBER(); 

                }
                break;
            case 16 :
                // Console.g:1:138: FILE_NAME
                {
                mFILE_NAME(); 

                }
                break;
            case 17 :
                // Console.g:1:148: WS
                {
                mWS(); 

                }
                break;

        }

    }


    protected DFA16 dfa16 = new DFA16(this);
    static final String DFA16_eotS =
        "\1\uffff\1\24\2\uffff\17\24\1\52\2\uffff\13\24\1\66\1\24\1\66\6"+
        "\24\1\uffff\11\24\2\107\1\uffff\10\24\2\117\2\120\1\122\1\24\1\122"+
        "\1\24\1\uffff\2\24\1\uffff\4\24\2\uffff\1\24\2\uffff\5\24\1\141"+
        "\1\24\2\143\4\24\1\uffff\1\147\2\uffff\2\24\1\uffff\2\152\1\uffff";
    static final String DFA16_eofS =
        "\153\uffff";
    static final String DFA16_minS =
        "\1\11\1\165\2\uffff\1\145\1\105\1\170\1\130\1\151\1\111\1\163\1"+
        "\123\1\156\1\116\1\145\1\105\1\145\1\105\1\145\1\54\2\uffff\1\162"+
        "\1\154\1\114\1\151\1\111\1\163\1\141\1\123\1\101\1\145\1\105\1\54"+
        "\1\164\1\54\1\124\1\164\1\124\1\154\1\114\1\162\1\uffff\1\162\1"+
        "\160\1\120\1\164\1\124\1\164\1\144\1\124\1\104\2\54\1\uffff\1\160"+
        "\1\120\2\40\1\145\1\105\1\165\1\145\5\54\1\40\1\54\1\40\1\uffff"+
        "\1\165\1\125\1\uffff\1\164\1\124\2\156\2\uffff\1\155\2\uffff\1\115"+
        "\1\164\1\124\1\145\1\105\1\54\1\164\2\54\2\40\1\155\1\115\1\uffff"+
        "\1\54\2\uffff\1\155\1\115\1\uffff\2\54\1\uffff";
    static final String DFA16_maxS =
        "\1\172\1\165\2\uffff\1\145\1\105\1\170\1\130\1\157\1\117\1\163\1"+
        "\123\1\165\1\125\1\145\1\105\1\145\1\105\1\145\1\172\2\uffff\1\162"+
        "\1\154\1\114\1\151\1\111\1\163\1\141\1\123\1\101\1\145\1\105\1\172"+
        "\1\164\1\172\1\124\1\164\1\124\1\154\1\114\1\162\1\uffff\1\162\1"+
        "\160\1\120\1\164\1\124\1\164\1\144\1\124\1\104\2\172\1\uffff\1\160"+
        "\1\120\2\40\1\145\1\105\1\165\1\145\5\172\1\40\1\172\1\40\1\uffff"+
        "\1\165\1\125\1\uffff\1\164\1\124\2\156\2\uffff\1\155\2\uffff\1\115"+
        "\1\164\1\124\1\145\1\105\1\172\1\164\2\172\2\40\1\155\1\115\1\uffff"+
        "\1\172\2\uffff\1\155\1\115\1\uffff\2\172\1\uffff";
    static final String DFA16_acceptS =
        "\2\uffff\1\2\1\3\20\uffff\1\20\1\21\24\uffff\1\17\13\uffff\1\10"+
        "\20\uffff\1\7\2\uffff\1\11\4\uffff\1\4\1\5\1\uffff\1\6\1\16\15\uffff"+
        "\1\14\1\uffff\1\13\1\15\2\uffff\1\1\2\uffff\1\12";
    static final String DFA16_specialS =
        "\153\uffff}>";
    static final String[] DFA16_transitionS = {
            "\2\25\2\uffff\1\25\22\uffff\1\25\7\uffff\1\2\1\3\2\uffff\4\24"+
            "\12\23\1\24\6\uffff\3\24\1\21\1\7\2\24\1\5\3\24\1\11\2\24\1"+
            "\15\3\24\1\17\1\24\1\13\5\24\1\uffff\1\24\2\uffff\1\24\1\uffff"+
            "\2\24\1\1\1\20\1\6\2\24\1\4\3\24\1\10\2\24\1\14\2\24\1\22\1"+
            "\16\1\24\1\12\5\24",
            "\1\26",
            "",
            "",
            "\1\27",
            "\1\30",
            "\1\31",
            "\1\32",
            "\1\33\5\uffff\1\34",
            "\1\35\5\uffff\1\36",
            "\1\37",
            "\1\40",
            "\1\41\6\uffff\1\42",
            "\1\43\6\uffff\1\44",
            "\1\45",
            "\1\46",
            "\1\47",
            "\1\50",
            "\1\51",
            "\4\24\12\23\1\24\6\uffff\32\24\1\uffff\1\24\2\uffff\1\24\1"+
            "\uffff\32\24",
            "",
            "",
            "\1\53",
            "\1\54",
            "\1\55",
            "\1\56",
            "\1\57",
            "\1\60",
            "\1\61",
            "\1\62",
            "\1\63",
            "\1\64",
            "\1\65",
            "\17\24\6\uffff\32\24\1\uffff\1\24\2\uffff\1\24\1\uffff\32\24",
            "\1\67",
            "\17\24\6\uffff\32\24\1\uffff\1\24\2\uffff\1\24\1\uffff\32\24",
            "\1\70",
            "\1\71",
            "\1\72",
            "\1\73",
            "\1\74",
            "\1\75",
            "",
            "\1\76",
            "\1\77",
            "\1\100",
            "\1\101",
            "\1\102",
            "\1\103",
            "\1\104",
            "\1\105",
            "\1\106",
            "\17\24\6\uffff\32\24\1\uffff\1\24\2\uffff\1\24\1\uffff\32\24",
            "\17\24\6\uffff\32\24\1\uffff\1\24\2\uffff\1\24\1\uffff\32\24",
            "",
            "\1\110",
            "\1\111",
            "\1\112",
            "\1\112",
            "\1\113",
            "\1\114",
            "\1\115",
            "\1\116",
            "\17\24\6\uffff\32\24\1\uffff\1\24\2\uffff\1\24\1\uffff\32\24",
            "\17\24\6\uffff\32\24\1\uffff\1\24\2\uffff\1\24\1\uffff\32\24",
            "\17\24\6\uffff\32\24\1\uffff\1\24\2\uffff\1\24\1\uffff\32\24",
            "\17\24\6\uffff\32\24\1\uffff\1\24\2\uffff\1\24\1\uffff\32\24",
            "\17\24\6\uffff\32\24\1\uffff\1\24\2\uffff\1\24\1\uffff\14\24"+
            "\1\121\15\24",
            "\1\123",
            "\17\24\6\uffff\14\24\1\124\15\24\1\uffff\1\24\2\uffff\1\24"+
            "\1\uffff\32\24",
            "\1\123",
            "",
            "\1\125",
            "\1\126",
            "",
            "\1\127",
            "\1\130",
            "\1\131",
            "\1\132",
            "",
            "",
            "\1\133",
            "",
            "",
            "\1\134",
            "\1\135",
            "\1\136",
            "\1\137",
            "\1\140",
            "\17\24\6\uffff\32\24\1\uffff\1\24\2\uffff\1\24\1\uffff\32\24",
            "\1\142",
            "\17\24\6\uffff\32\24\1\uffff\1\24\2\uffff\1\24\1\uffff\32\24",
            "\17\24\6\uffff\32\24\1\uffff\1\24\2\uffff\1\24\1\uffff\32\24",
            "\1\144",
            "\1\144",
            "\1\145",
            "\1\146",
            "",
            "\17\24\6\uffff\32\24\1\uffff\1\24\2\uffff\1\24\1\uffff\32\24",
            "",
            "",
            "\1\150",
            "\1\151",
            "",
            "\17\24\6\uffff\32\24\1\uffff\1\24\2\uffff\1\24\1\uffff\32\24",
            "\17\24\6\uffff\32\24\1\uffff\1\24\2\uffff\1\24\1\uffff\32\24",
            ""
    };

    static final short[] DFA16_eot = DFA.unpackEncodedString(DFA16_eotS);
    static final short[] DFA16_eof = DFA.unpackEncodedString(DFA16_eofS);
    static final char[] DFA16_min = DFA.unpackEncodedStringToUnsignedChars(DFA16_minS);
    static final char[] DFA16_max = DFA.unpackEncodedStringToUnsignedChars(DFA16_maxS);
    static final short[] DFA16_accept = DFA.unpackEncodedString(DFA16_acceptS);
    static final short[] DFA16_special = DFA.unpackEncodedString(DFA16_specialS);
    static final short[][] DFA16_transition;

    static {
        int numStates = DFA16_transitionS.length;
        DFA16_transition = new short[numStates][];
        for (int i=0; i<numStates; i++) {
            DFA16_transition[i] = DFA.unpackEncodedString(DFA16_transitionS[i]);
        }
    }

    class DFA16 extends DFA {

        public DFA16(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 16;
            this.eot = DFA16_eot;
            this.eof = DFA16_eof;
            this.min = DFA16_min;
            this.max = DFA16_max;
            this.accept = DFA16_accept;
            this.special = DFA16_special;
            this.transition = DFA16_transition;
        }
        public String getDescription() {
            return "1:1: Tokens : ( T__22 | T__23 | T__24 | HELP_T | EXIT_T | LIST_T | USE_T | ON_T | SETPRELUDE_T | DELETEMM_T | LISTMM_T | RERUN_T | SETRESULTOUTPUT_T | LOADPREFS_T | NUMBER | FILE_NAME | WS );";
        }
    }
 

}