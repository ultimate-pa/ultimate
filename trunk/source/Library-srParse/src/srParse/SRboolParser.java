// $ANTLR 3.2 Sep 23, 2009 12:02:23 C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g 2010-08-20 10:31:47

package srParse;

import pea.CDD;
import pea.BooleanDecision;
import java.util.Vector;


import org.antlr.runtime.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;

public class SRboolParser extends Parser {
    public static final String[] tokenNames = new String[] {
        "<invalid>", "<EOR>", "<DOWN>", "<UP>", "AND_1", "AND_2", "OR_1", "OR_2", "OR_3", "QUOTE", "NOT_1", "KW_NOT", "BR_OPEN", "BR_CLOSE", "SC_GLOBALLY", "K", "SC_BEFORE", "SC_BETWEEN", "KW_AND", "SC_AFTER", "SC_UNTIL", "PKT", "ID", "DPKT", "OP", "INT", "KW_IN", "KW_VAR", "KW_EVENTUALLY", "KW_HOLDS", "KW_IT", "KW_IS", "KW_TRANS", "KW_TO", "KW_STATES", "KW_WHICH", "KW_OCCUR", "KW_AT", "KW_MOST", "KW_TWICE", "KW_NEVER", "KW_THE", "KW_CASE", "KW_THAT", "KW_ALWAYS", "KW_IF", "KW_THEN", "KW_PREV", "KW_HELD", "KW_WAS", "KW_PREC", "KW_BY", "KW_SUCC", "KW_WHERE", "KW_DOES", "KW_HOLD", "KW_AFTER", "KW_TIME", "KW_UNITS", "KW_FOR", "KW_LEAST", "KW_AS", "KW_WELL", "KW_ONCE", "KW_BECOMES", "KW_SAT", "KW_LESS", "KW_THAN", "KW_EVERY", "KW_THERE", "KW_ONE", "KW_EXEC", "KW_SEQ", "KW_SUCH", "EOL", "NODECLARE", "KW_BETW", "WS", "KOM", "KOM_2", "OTHER", "'{'", "'}'"
    };
    public static final int DPKT=23;
    public static final int SC_UNTIL=20;
    public static final int KW_WHICH=35;
    public static final int KOM=78;
    public static final int KW_BECOMES=64;
    public static final int KW_AND=18;
    public static final int KW_ONCE=63;
    public static final int KW_PREV=47;
    public static final int KW_WHERE=53;
    public static final int BR_OPEN=12;
    public static final int ID=22;
    public static final int EOF=-1;
    public static final int PKT=21;
    public static final int KW_VAR=27;
    public static final int KW_THAT=43;
    public static final int KW_PREC=50;
    public static final int QUOTE=9;
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
    public static final int KW_SUCH=73;
    public static final int KW_WELL=62;
    public static final int T__81=81;
    public static final int OTHER=80;
    public static final int T__82=82;
    public static final int KW_EVENTUALLY=28;
    public static final int KW_LESS=66;
    public static final int KW_SUCC=52;
    public static final int KW_HELD=48;
    public static final int KW_HOLD=55;
    public static final int AND_1=4;
    public static final int K=15;
    public static final int AND_2=5;
    public static final int INT=25;
    public static final int KW_TWICE=39;
    public static final int KW_CASE=42;
    public static final int KW_EXEC=71;
    public static final int KW_UNITS=58;
    public static final int KW_ALWAYS=44;
    public static final int KW_TRANS=32;
    public static final int WS=77;
    public static final int KW_EVERY=68;
    public static final int OP=24;
    public static final int KW_TO=33;
    public static final int KW_BY=51;
    public static final int KW_STATES=34;
    public static final int KW_AS=61;
    public static final int KOM_2=79;
    public static final int KW_OCCUR=36;
    public static final int KW_AT=37;
    public static final int KW_THE=41;
    public static final int BR_CLOSE=13;
    public static final int OR_1=6;
    public static final int NODECLARE=75;
    public static final int KW_DOES=54;
    public static final int OR_3=8;
    public static final int OR_2=7;
    public static final int KW_NOT=11;

    // delegates
    // delegators


        public SRboolParser(TokenStream input) {
            this(input, new RecognizerSharedState());
        }
        public SRboolParser(TokenStream input, RecognizerSharedState state) {
            super(input, state);
             
        }
        

    public String[] getTokenNames() { return SRboolParser.tokenNames; }
    public String getGrammarFileName() { return "C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g"; }



    // $ANTLR start "file"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:15:1: file : lines ;
    public final void file() throws RecognitionException, ENotDeclaredIdentifier {
        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:15:6: ( lines )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:15:8: lines
            {
            pushFollow(FOLLOW_lines_in_file19);
            lines();

            state._fsp--;


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "file"


    // $ANTLR start "eAND"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:21:1: eAND : ( AND_1 | AND_2 );
    public final void eAND() throws RecognitionException {
        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:21:6: ( AND_1 | AND_2 )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:
            {
            if ( (input.LA(1)>=AND_1 && input.LA(1)<=AND_2) ) {
                input.consume();
                state.errorRecovery=false;
            }
            else {
                MismatchedSetException mse = new MismatchedSetException(null,input);
                throw mse;
            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "eAND"


    // $ANTLR start "eOR"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:27:1: eOR : ( OR_1 | OR_2 | OR_3 );
    public final void eOR() throws RecognitionException {
        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:27:5: ( OR_1 | OR_2 | OR_3 )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:
            {
            if ( (input.LA(1)>=OR_1 && input.LA(1)<=OR_3) ) {
                input.consume();
                state.errorRecovery=false;
            }
            else {
                MismatchedSetException mse = new MismatchedSetException(null,input);
                throw mse;
            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "eOR"


    // $ANTLR start "qorExp"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:33:1: qorExp returns [ CDD result ] : ( orExp | QUOTE orExp QUOTE );
    public final CDD qorExp() throws RecognitionException {
        CDD result = null;

        CDD orExp1 = null;

        CDD orExp2 = null;


        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:34:23: ( orExp | QUOTE orExp QUOTE )
            int alt1=2;
            int LA1_0 = input.LA(1);

            if ( ((LA1_0>=NOT_1 && LA1_0<=BR_OPEN)||LA1_0==ID) ) {
                alt1=1;
            }
            else if ( (LA1_0==QUOTE) ) {
                alt1=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 1, 0, input);

                throw nvae;
            }
            switch (alt1) {
                case 1 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:35:3: orExp
                    {
                    pushFollow(FOLLOW_orExp_in_qorExp78);
                    orExp1=orExp();

                    state._fsp--;

                    result =orExp1;

                    }
                    break;
                case 2 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:36:4: QUOTE orExp QUOTE
                    {
                    match(input,QUOTE,FOLLOW_QUOTE_in_qorExp85); 
                    pushFollow(FOLLOW_orExp_in_qorExp87);
                    orExp2=orExp();

                    state._fsp--;

                    match(input,QUOTE,FOLLOW_QUOTE_in_qorExp89); 
                    result =orExp2;

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
        return result;
    }
    // $ANTLR end "qorExp"


    // $ANTLR start "orExp"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:39:1: orExp returns [ CDD result ] : andExp ( eOR ore= orExp )? ;
    public final CDD orExp() throws RecognitionException {
        CDD result = null;

        CDD ore = null;

        CDD andExp3 = null;


        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:40:23: ( andExp ( eOR ore= orExp )? )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:41:2: andExp ( eOR ore= orExp )?
            {
            pushFollow(FOLLOW_andExp_in_orExp108);
            andExp3=andExp();

            state._fsp--;

            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:41:9: ( eOR ore= orExp )?
            int alt2=2;
            int LA2_0 = input.LA(1);

            if ( ((LA2_0>=OR_1 && LA2_0<=OR_3)) ) {
                alt2=1;
            }
            switch (alt2) {
                case 1 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:41:10: eOR ore= orExp
                    {
                    pushFollow(FOLLOW_eOR_in_orExp111);
                    eOR();

                    state._fsp--;

                    pushFollow(FOLLOW_orExp_in_orExp115);
                    ore=orExp();

                    state._fsp--;


                    }
                    break;

            }

            if( ore==null )
            		result =andExp3;
            	else
            		result =andExp3.or(ore);

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return result;
    }
    // $ANTLR end "orExp"


    // $ANTLR start "eNot"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:72:1: eNot : ( NOT_1 | KW_NOT );
    public final void eNot() throws RecognitionException {
        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:72:6: ( NOT_1 | KW_NOT )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:
            {
            if ( (input.LA(1)>=NOT_1 && input.LA(1)<=KW_NOT) ) {
                input.consume();
                state.errorRecovery=false;
            }
            else {
                MismatchedSetException mse = new MismatchedSetException(null,input);
                throw mse;
            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "eNot"


    // $ANTLR start "notExp"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:76:1: notExp returns [ CDD result ] : ( eNot eExp | eExp );
    public final CDD notExp() throws RecognitionException {
        CDD result = null;

        CDD eExp4 = null;

        CDD eExp5 = null;


        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:77:23: ( eNot eExp | eExp )
            int alt3=2;
            int LA3_0 = input.LA(1);

            if ( ((LA3_0>=NOT_1 && LA3_0<=KW_NOT)) ) {
                alt3=1;
            }
            else if ( (LA3_0==BR_OPEN||LA3_0==ID) ) {
                alt3=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 3, 0, input);

                throw nvae;
            }
            switch (alt3) {
                case 1 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:78:2: eNot eExp
                    {
                    pushFollow(FOLLOW_eNot_in_notExp172);
                    eNot();

                    state._fsp--;

                    pushFollow(FOLLOW_eExp_in_notExp174);
                    eExp4=eExp();

                    state._fsp--;

                    result =eExp4.negate();

                    }
                    break;
                case 2 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:80:3: eExp
                    {
                    pushFollow(FOLLOW_eExp_in_notExp181);
                    eExp5=eExp();

                    state._fsp--;

                    result =eExp5;

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
        return result;
    }
    // $ANTLR end "notExp"


    // $ANTLR start "andExp"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:84:1: andExp returns [ CDD result ] : notExp ( eAND ande= andExp )? ;
    public final CDD andExp() throws RecognitionException {
        CDD result = null;

        CDD ande = null;

        CDD notExp6 = null;


        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:85:23: ( notExp ( eAND ande= andExp )? )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:87:2: notExp ( eAND ande= andExp )?
            {
            pushFollow(FOLLOW_notExp_in_andExp203);
            notExp6=notExp();

            state._fsp--;

            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:87:9: ( eAND ande= andExp )?
            int alt4=2;
            int LA4_0 = input.LA(1);

            if ( ((LA4_0>=AND_1 && LA4_0<=AND_2)) ) {
                alt4=1;
            }
            switch (alt4) {
                case 1 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:87:10: eAND ande= andExp
                    {
                    pushFollow(FOLLOW_eAND_in_andExp206);
                    eAND();

                    state._fsp--;

                    pushFollow(FOLLOW_andExp_in_andExp210);
                    ande=andExp();

                    state._fsp--;


                    }
                    break;

            }

            if( ande==null )
            		result =notExp6;
            	else
            		result =notExp6.and(ande);

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return result;
    }
    // $ANTLR end "andExp"


    // $ANTLR start "eExp"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:99:1: eExp returns [ CDD result ] : ( var | BR_OPEN orExp BR_CLOSE );
    public final CDD eExp() throws RecognitionException {
        CDD result = null;

        SRboolParser.var_return var7 = null;

        CDD orExp8 = null;


        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:100:23: ( var | BR_OPEN orExp BR_CLOSE )
            int alt5=2;
            int LA5_0 = input.LA(1);

            if ( (LA5_0==ID) ) {
                alt5=1;
            }
            else if ( (LA5_0==BR_OPEN) ) {
                alt5=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 5, 0, input);

                throw nvae;
            }
            switch (alt5) {
                case 1 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:101:2: var
                    {
                    pushFollow(FOLLOW_var_in_eExp240);
                    var7=var();

                    state._fsp--;

                    result =BooleanDecision.create(VarRename.getInstance().getShortName((var7!=null?input.toString(var7.start,var7.stop):null)));

                    }
                    break;
                case 2 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:111:4: BR_OPEN orExp BR_CLOSE
                    {
                    match(input,BR_OPEN,FOLLOW_BR_OPEN_in_eExp265); 
                    pushFollow(FOLLOW_orExp_in_eExp267);
                    orExp8=orExp();

                    state._fsp--;

                    match(input,BR_CLOSE,FOLLOW_BR_CLOSE_in_eExp269); 
                     result = orExp8; 

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
        return result;
    }
    // $ANTLR end "eExp"


    // $ANTLR start "qeExp"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:117:1: qeExp returns [ CDD result ] : ( orExp | QUOTE orExp QUOTE );
    public final CDD qeExp() throws RecognitionException {
        CDD result = null;

        CDD orExp9 = null;

        CDD orExp10 = null;


        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:118:24: ( orExp | QUOTE orExp QUOTE )
            int alt6=2;
            int LA6_0 = input.LA(1);

            if ( ((LA6_0>=NOT_1 && LA6_0<=BR_OPEN)||LA6_0==ID) ) {
                alt6=1;
            }
            else if ( (LA6_0==QUOTE) ) {
                alt6=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 6, 0, input);

                throw nvae;
            }
            switch (alt6) {
                case 1 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:119:2: orExp
                    {
                    pushFollow(FOLLOW_orExp_in_qeExp292);
                    orExp9=orExp();

                    state._fsp--;

                     result =orExp9; 

                    }
                    break;
                case 2 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:120:4: QUOTE orExp QUOTE
                    {
                    match(input,QUOTE,FOLLOW_QUOTE_in_qeExp299); 
                    pushFollow(FOLLOW_orExp_in_qeExp301);
                    orExp10=orExp();

                    state._fsp--;

                    match(input,QUOTE,FOLLOW_QUOTE_in_qeExp303); 
                     result = orExp10; 

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
        return result;
    }
    // $ANTLR end "qeExp"


    // $ANTLR start "pScope"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:123:1: pScope returns [ srParseScope result ] : ( SC_GLOBALLY K | SC_BEFORE cdd= qorExp K | pScopeAfter | SC_BETWEEN cdd1= qorExp KW_AND cdd2= qorExp K );
    public final srParseScope pScope() throws RecognitionException {
        srParseScope result = null;

        CDD cdd = null;

        CDD cdd1 = null;

        CDD cdd2 = null;

        srParseScope pScopeAfter11 = null;


        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:124:32: ( SC_GLOBALLY K | SC_BEFORE cdd= qorExp K | pScopeAfter | SC_BETWEEN cdd1= qorExp KW_AND cdd2= qorExp K )
            int alt7=4;
            switch ( input.LA(1) ) {
            case SC_GLOBALLY:
                {
                alt7=1;
                }
                break;
            case SC_BEFORE:
                {
                alt7=2;
                }
                break;
            case SC_AFTER:
                {
                alt7=3;
                }
                break;
            case SC_BETWEEN:
                {
                alt7=4;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("", 7, 0, input);

                throw nvae;
            }

            switch (alt7) {
                case 1 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:125:2: SC_GLOBALLY K
                    {
                    match(input,SC_GLOBALLY,FOLLOW_SC_GLOBALLY_in_pScope321); 
                    match(input,K,FOLLOW_K_in_pScope323); 
                     result =new srParseScopeGlob(); 

                    }
                    break;
                case 2 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:126:4: SC_BEFORE cdd= qorExp K
                    {
                    match(input,SC_BEFORE,FOLLOW_SC_BEFORE_in_pScope330); 
                    pushFollow(FOLLOW_qorExp_in_pScope334);
                    cdd=qorExp();

                    state._fsp--;

                    match(input,K,FOLLOW_K_in_pScope336); 
                    result =new srParseScopeBefore( cdd );

                    }
                    break;
                case 3 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:127:4: pScopeAfter
                    {
                    pushFollow(FOLLOW_pScopeAfter_in_pScope343);
                    pScopeAfter11=pScopeAfter();

                    state._fsp--;

                     result =pScopeAfter11; 

                    }
                    break;
                case 4 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:128:4: SC_BETWEEN cdd1= qorExp KW_AND cdd2= qorExp K
                    {
                    match(input,SC_BETWEEN,FOLLOW_SC_BETWEEN_in_pScope351); 
                    pushFollow(FOLLOW_qorExp_in_pScope355);
                    cdd1=qorExp();

                    state._fsp--;

                    match(input,KW_AND,FOLLOW_KW_AND_in_pScope357); 
                    pushFollow(FOLLOW_qorExp_in_pScope361);
                    cdd2=qorExp();

                    state._fsp--;

                    match(input,K,FOLLOW_K_in_pScope363); 
                     result =new srParseScopeBetween( cdd1, cdd2 ); 

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
        return result;
    }
    // $ANTLR end "pScope"


    // $ANTLR start "pScopeAfter"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:131:1: pScopeAfter returns [ srParseScope result ] : SC_AFTER cdd1= qorExp ( SC_UNTIL cdd2= qorExp )? K ;
    public final srParseScope pScopeAfter() throws RecognitionException {
        srParseScope result = null;

        CDD cdd1 = null;

        CDD cdd2 = null;


        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:132:33: ( SC_AFTER cdd1= qorExp ( SC_UNTIL cdd2= qorExp )? K )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:133:5: SC_AFTER cdd1= qorExp ( SC_UNTIL cdd2= qorExp )? K
            {
            match(input,SC_AFTER,FOLLOW_SC_AFTER_in_pScopeAfter384); 
            pushFollow(FOLLOW_qorExp_in_pScopeAfter388);
            cdd1=qorExp();

            state._fsp--;

            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:133:26: ( SC_UNTIL cdd2= qorExp )?
            int alt8=2;
            int LA8_0 = input.LA(1);

            if ( (LA8_0==SC_UNTIL) ) {
                alt8=1;
            }
            switch (alt8) {
                case 1 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:133:27: SC_UNTIL cdd2= qorExp
                    {
                    match(input,SC_UNTIL,FOLLOW_SC_UNTIL_in_pScopeAfter391); 
                    pushFollow(FOLLOW_qorExp_in_pScopeAfter395);
                    cdd2=qorExp();

                    state._fsp--;


                    }
                    break;

            }

            match(input,K,FOLLOW_K_in_pScopeAfter399); 
             result =new srParseScopeAfter( cdd1, cdd2 ); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return result;
    }
    // $ANTLR end "pScopeAfter"


    // $ANTLR start "epktId"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:137:1: epktId : ( PKT ID | DPKT ID );
    public final void epktId() throws RecognitionException {
        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:137:8: ( PKT ID | DPKT ID )
            int alt9=2;
            int LA9_0 = input.LA(1);

            if ( (LA9_0==PKT) ) {
                alt9=1;
            }
            else if ( (LA9_0==DPKT) ) {
                alt9=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 9, 0, input);

                throw nvae;
            }
            switch (alt9) {
                case 1 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:137:10: PKT ID
                    {
                    match(input,PKT,FOLLOW_PKT_in_epktId413); 
                    match(input,ID,FOLLOW_ID_in_epktId415); 

                    }
                    break;
                case 2 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:138:4: DPKT ID
                    {
                    match(input,DPKT,FOLLOW_DPKT_in_epktId420); 
                    match(input,ID,FOLLOW_ID_in_epktId422); 

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
        return ;
    }
    // $ANTLR end "epktId"


    // $ANTLR start "cid"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:141:1: cid : ID ( epktId )* ;
    public final void cid() throws RecognitionException {
        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:141:5: ( ID ( epktId )* )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:141:7: ID ( epktId )*
            {
            match(input,ID,FOLLOW_ID_in_cid432); 
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:141:10: ( epktId )*
            loop10:
            do {
                int alt10=2;
                int LA10_0 = input.LA(1);

                if ( (LA10_0==PKT) ) {
                    int LA10_2 = input.LA(2);

                    if ( (LA10_2==ID) ) {
                        alt10=1;
                    }


                }
                else if ( (LA10_0==DPKT) ) {
                    alt10=1;
                }


                switch (alt10) {
            	case 1 :
            	    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:141:11: epktId
            	    {
            	    pushFollow(FOLLOW_epktId_in_cid435);
            	    epktId();

            	    state._fsp--;


            	    }
            	    break;

            	default :
            	    break loop10;
                }
            } while (true);


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "cid"


    // $ANTLR start "eiSet"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:144:1: eiSet : ( cid | num );
    public final void eiSet() throws RecognitionException {
        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:144:7: ( cid | num )
            int alt11=2;
            int LA11_0 = input.LA(1);

            if ( (LA11_0==ID) ) {
                alt11=1;
            }
            else if ( (LA11_0==QUOTE||LA11_0==INT) ) {
                alt11=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 11, 0, input);

                throw nvae;
            }
            switch (alt11) {
                case 1 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:145:2: cid
                    {
                    pushFollow(FOLLOW_cid_in_eiSet449);
                    cid();

                    state._fsp--;


                    }
                    break;
                case 2 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:146:4: num
                    {
                    pushFollow(FOLLOW_num_in_eiSet454);
                    num();

                    state._fsp--;


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
        return ;
    }
    // $ANTLR end "eiSet"


    // $ANTLR start "eSet"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:149:1: eSet : ( cid | '{' eiSet ( ',' eiSet )* '}' );
    public final void eSet() throws RecognitionException {
        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:149:6: ( cid | '{' eiSet ( ',' eiSet )* '}' )
            int alt13=2;
            int LA13_0 = input.LA(1);

            if ( (LA13_0==ID) ) {
                alt13=1;
            }
            else if ( (LA13_0==81) ) {
                alt13=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 13, 0, input);

                throw nvae;
            }
            switch (alt13) {
                case 1 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:150:2: cid
                    {
                    pushFollow(FOLLOW_cid_in_eSet466);
                    cid();

                    state._fsp--;


                    }
                    break;
                case 2 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:151:4: '{' eiSet ( ',' eiSet )* '}'
                    {
                    match(input,81,FOLLOW_81_in_eSet471); 
                    pushFollow(FOLLOW_eiSet_in_eSet473);
                    eiSet();

                    state._fsp--;

                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:151:14: ( ',' eiSet )*
                    loop12:
                    do {
                        int alt12=2;
                        int LA12_0 = input.LA(1);

                        if ( (LA12_0==K) ) {
                            alt12=1;
                        }


                        switch (alt12) {
                    	case 1 :
                    	    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:151:16: ',' eiSet
                    	    {
                    	    match(input,K,FOLLOW_K_in_eSet477); 
                    	    pushFollow(FOLLOW_eiSet_in_eSet479);
                    	    eiSet();

                    	    state._fsp--;


                    	    }
                    	    break;

                    	default :
                    	    break loop12;
                        }
                    } while (true);

                    match(input,82,FOLLOW_82_in_eSet483); 

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
        return ;
    }
    // $ANTLR end "eSet"

    public static class var_return extends ParserRuleReturnScope {
    };

    // $ANTLR start "var"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:156:1: var : ( cid | cid OP INT | cid OP cid | cid KW_IN eSet );
    public final SRboolParser.var_return var() throws RecognitionException {
        SRboolParser.var_return retval = new SRboolParser.var_return();
        retval.start = input.LT(1);

        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:158:2: ( cid | cid OP INT | cid OP cid | cid KW_IN eSet )
            int alt14=4;
            alt14 = dfa14.predict(input);
            switch (alt14) {
                case 1 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:159:2: cid
                    {
                    pushFollow(FOLLOW_cid_in_var501);
                    cid();

                    state._fsp--;


                    }
                    break;
                case 2 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:160:4: cid OP INT
                    {
                    pushFollow(FOLLOW_cid_in_var509);
                    cid();

                    state._fsp--;

                    match(input,OP,FOLLOW_OP_in_var511); 
                    match(input,INT,FOLLOW_INT_in_var513); 

                    }
                    break;
                case 3 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:161:4: cid OP cid
                    {
                    pushFollow(FOLLOW_cid_in_var520);
                    cid();

                    state._fsp--;

                    match(input,OP,FOLLOW_OP_in_var522); 
                    pushFollow(FOLLOW_cid_in_var524);
                    cid();

                    state._fsp--;


                    }
                    break;
                case 4 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:162:4: cid KW_IN eSet
                    {
                    pushFollow(FOLLOW_cid_in_var530);
                    cid();

                    state._fsp--;

                    match(input,KW_IN,FOLLOW_KW_IN_in_var532); 
                    pushFollow(FOLLOW_eSet_in_var534);
                    eSet();

                    state._fsp--;


                    }
                    break;

            }
            retval.stop = input.LT(-1);

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return retval;
    }
    // $ANTLR end "var"


    // $ANTLR start "varlist"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:165:1: varlist returns [ Vector<CDD> result ] : ( QUOTE var QUOTE | QUOTE var QUOTE K v= varlist );
    public final Vector<CDD> varlist() throws RecognitionException {
        Vector<CDD> result = null;

        Vector<CDD> v = null;

        SRboolParser.var_return var12 = null;

        SRboolParser.var_return var13 = null;


        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:167:2: ( QUOTE var QUOTE | QUOTE var QUOTE K v= varlist )
            int alt15=2;
            alt15 = dfa15.predict(input);
            switch (alt15) {
                case 1 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:168:2: QUOTE var QUOTE
                    {
                    match(input,QUOTE,FOLLOW_QUOTE_in_varlist554); 
                    pushFollow(FOLLOW_var_in_varlist556);
                    var12=var();

                    state._fsp--;

                    match(input,QUOTE,FOLLOW_QUOTE_in_varlist558); 
                    result =new Vector<CDD>(); result.add( BooleanDecision.create( VarRename.getInstance().getShortName( (var12!=null?input.toString(var12.start,var12.stop):null) ) ) );

                    }
                    break;
                case 2 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:169:4: QUOTE var QUOTE K v= varlist
                    {
                    match(input,QUOTE,FOLLOW_QUOTE_in_varlist565); 
                    pushFollow(FOLLOW_var_in_varlist567);
                    var13=var();

                    state._fsp--;

                    match(input,QUOTE,FOLLOW_QUOTE_in_varlist569); 
                    match(input,K,FOLLOW_K_in_varlist571); 
                    pushFollow(FOLLOW_varlist_in_varlist576);
                    v=varlist();

                    state._fsp--;

                    result =v;result.add( BooleanDecision.create( VarRename.getInstance().getShortName((var13!=null?input.toString(var13.start,var13.stop):null) ) ));

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
        return result;
    }
    // $ANTLR end "varlist"


    // $ANTLR start "declaration"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:172:1: declaration returns [ Vector<CDD> result ] : KW_VAR varlist ;
    public final Vector<CDD> declaration() throws RecognitionException {
        Vector<CDD> result = null;

        Vector<CDD> varlist14 = null;


        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:174:2: ( KW_VAR varlist )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:175:2: KW_VAR varlist
            {
            match(input,KW_VAR,FOLLOW_KW_VAR_in_declaration596); 
            pushFollow(FOLLOW_varlist_in_declaration598);
            varlist14=varlist();

            state._fsp--;

            result =varlist14;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return result;
    }
    // $ANTLR end "declaration"


    // $ANTLR start "scopedPattern"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:179:1: scopedPattern returns [ srParsePattern result ] : pScope pattern ;
    public final srParsePattern scopedPattern() throws RecognitionException, ENotDeclaredIdentifier {
        srParsePattern result = null;

        srParsePattern pattern15 = null;

        srParseScope pScope16 = null;


        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:180:35: ( pScope pattern )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:181:2: pScope pattern
            {
            pushFollow(FOLLOW_pScope_in_scopedPattern616);
            pScope16=pScope();

            state._fsp--;

            pushFollow(FOLLOW_pattern_in_scopedPattern618);
            pattern15=pattern();

            state._fsp--;

            result =pattern15;result.setScope(pScope16);

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return result;
    }
    // $ANTLR end "scopedPattern"


    // $ANTLR start "num"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:185:1: num returns [ int value ] : ( INT | QUOTE INT QUOTE );
    public final int num() throws RecognitionException {
        int value = 0;

        Token INT17=null;
        Token INT18=null;

        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:187:2: ( INT | QUOTE INT QUOTE )
            int alt16=2;
            int LA16_0 = input.LA(1);

            if ( (LA16_0==INT) ) {
                alt16=1;
            }
            else if ( (LA16_0==QUOTE) ) {
                alt16=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 16, 0, input);

                throw nvae;
            }
            switch (alt16) {
                case 1 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:187:4: INT
                    {
                    INT17=(Token)match(input,INT,FOLLOW_INT_in_num635); 
                    value =(int)new Integer((INT17!=null?INT17.getText():null)).intValue();

                    }
                    break;
                case 2 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:188:4: QUOTE INT QUOTE
                    {
                    match(input,QUOTE,FOLLOW_QUOTE_in_num644); 
                    INT18=(Token)match(input,INT,FOLLOW_INT_in_num646); 
                    match(input,QUOTE,FOLLOW_QUOTE_in_num648); 
                    value =(int)new Integer((INT18!=null?INT18.getText():null)).intValue();

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
        return value;
    }
    // $ANTLR end "num"


    // $ANTLR start "pattern_exists"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:194:1: pattern_exists returns [ Vector<CDD> result ] : qorExp KW_EVENTUALLY KW_HOLDS ;
    public final Vector<CDD> pattern_exists() throws RecognitionException {
        Vector<CDD> result = null;

        CDD qorExp19 = null;


        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:196:2: ( qorExp KW_EVENTUALLY KW_HOLDS )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:196:4: qorExp KW_EVENTUALLY KW_HOLDS
            {
            pushFollow(FOLLOW_qorExp_in_pattern_exists669);
            qorExp19=qorExp();

            state._fsp--;

            match(input,KW_EVENTUALLY,FOLLOW_KW_EVENTUALLY_in_pattern_exists671); 
            match(input,KW_HOLDS,FOLLOW_KW_HOLDS_in_pattern_exists673); 
            result =new Vector<CDD>(); result.add(qorExp19);

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return result;
    }
    // $ANTLR end "pattern_exists"


    // $ANTLR start "dec_pattern_exists"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:199:1: dec_pattern_exists returns [ srParsePattern result] : ;
    public final srParsePattern dec_pattern_exists() throws RecognitionException {
        srParsePattern result = null;

        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:201:2: ()
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:201:5: 
            {
            result =new srParsePattern(); result.setPattern( result.new BndExistencePattern() );

            }

        }
        finally {
        }
        return result;
    }
    // $ANTLR end "dec_pattern_exists"


    // $ANTLR start "pat_pref_itis"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:205:1: pat_pref_itis : KW_IT KW_IS ;
    public final void pat_pref_itis() throws RecognitionException {
        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:206:2: ( KW_IT KW_IS )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:206:4: KW_IT KW_IS
            {
            match(input,KW_IT,FOLLOW_KW_IT_in_pat_pref_itis703); 
            match(input,KW_IS,FOLLOW_KW_IS_in_pat_pref_itis705); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "pat_pref_itis"


    // $ANTLR start "pattern_BndEx"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:210:1: pattern_BndEx returns [ Vector<CDD> result ] : KW_TRANS KW_TO KW_STATES KW_IN KW_WHICH qorExp KW_HOLDS KW_OCCUR KW_AT KW_MOST KW_TWICE ;
    public final Vector<CDD> pattern_BndEx() throws RecognitionException {
        Vector<CDD> result = null;

        CDD qorExp20 = null;


        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:212:2: ( KW_TRANS KW_TO KW_STATES KW_IN KW_WHICH qorExp KW_HOLDS KW_OCCUR KW_AT KW_MOST KW_TWICE )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:212:4: KW_TRANS KW_TO KW_STATES KW_IN KW_WHICH qorExp KW_HOLDS KW_OCCUR KW_AT KW_MOST KW_TWICE
            {
            match(input,KW_TRANS,FOLLOW_KW_TRANS_in_pattern_BndEx721); 
            match(input,KW_TO,FOLLOW_KW_TO_in_pattern_BndEx723); 
            match(input,KW_STATES,FOLLOW_KW_STATES_in_pattern_BndEx725); 
            match(input,KW_IN,FOLLOW_KW_IN_in_pattern_BndEx727); 
            match(input,KW_WHICH,FOLLOW_KW_WHICH_in_pattern_BndEx729); 
            pushFollow(FOLLOW_qorExp_in_pattern_BndEx731);
            qorExp20=qorExp();

            state._fsp--;

            match(input,KW_HOLDS,FOLLOW_KW_HOLDS_in_pattern_BndEx733); 
            match(input,KW_OCCUR,FOLLOW_KW_OCCUR_in_pattern_BndEx735); 
            match(input,KW_AT,FOLLOW_KW_AT_in_pattern_BndEx737); 
            match(input,KW_MOST,FOLLOW_KW_MOST_in_pattern_BndEx739); 
            match(input,KW_TWICE,FOLLOW_KW_TWICE_in_pattern_BndEx741); 
            result =new Vector<CDD>(); result.add(qorExp20);

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return result;
    }
    // $ANTLR end "pattern_BndEx"


    // $ANTLR start "dec_pattern_BndEx"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:215:1: dec_pattern_BndEx returns [ srParsePattern result ] : ;
    public final srParsePattern dec_pattern_BndEx() throws RecognitionException {
        srParsePattern result = null;

        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:217:2: ()
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:217:4: 
            {
            result =new srParsePattern(); result.setPattern( result.new BndExistencePattern());

            }

        }
        finally {
        }
        return result;
    }
    // $ANTLR end "dec_pattern_BndEx"


    // $ANTLR start "dec_pat_pref_itis"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:220:1: dec_pat_pref_itis returns [ srParsePattern result ] : ( pattern_instabs dec_pattern_instabs | pat_pref_it_always dec_pat_pref_it_always | pat_pref_it_is_always_the_case_that dec_pat_pref_it_is_always_the_case_that );
    public final srParsePattern dec_pat_pref_itis() throws RecognitionException, ENotDeclaredIdentifier {
        srParsePattern result = null;

        srParsePattern dec_pattern_instabs21 = null;

        Vector<CDD> pattern_instabs22 = null;

        srParsePattern dec_pat_pref_it_always23 = null;

        srParsePattern dec_pat_pref_it_is_always_the_case_that24 = null;


        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:222:2: ( pattern_instabs dec_pattern_instabs | pat_pref_it_always dec_pat_pref_it_always | pat_pref_it_is_always_the_case_that dec_pat_pref_it_is_always_the_case_that )
            int alt17=3;
            switch ( input.LA(1) ) {
            case KW_NEVER:
                {
                alt17=1;
                }
                break;
            case KW_ALWAYS:
                {
                alt17=2;
                }
                break;
            case KW_THE:
                {
                alt17=3;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("", 17, 0, input);

                throw nvae;
            }

            switch (alt17) {
                case 1 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:222:4: pattern_instabs dec_pattern_instabs
                    {
                    pushFollow(FOLLOW_pattern_instabs_in_dec_pat_pref_itis771);
                    pattern_instabs22=pattern_instabs();

                    state._fsp--;

                    pushFollow(FOLLOW_dec_pattern_instabs_in_dec_pat_pref_itis773);
                    dec_pattern_instabs21=dec_pattern_instabs();

                    state._fsp--;

                    result =dec_pattern_instabs21; result.mergeCDDs(pattern_instabs22);

                    }
                    break;
                case 2 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:223:4: pat_pref_it_always dec_pat_pref_it_always
                    {
                    pushFollow(FOLLOW_pat_pref_it_always_in_dec_pat_pref_itis780);
                    pat_pref_it_always();

                    state._fsp--;

                    pushFollow(FOLLOW_dec_pat_pref_it_always_in_dec_pat_pref_itis782);
                    dec_pat_pref_it_always23=dec_pat_pref_it_always();

                    state._fsp--;

                    result =dec_pat_pref_it_always23;

                    }
                    break;
                case 3 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:224:4: pat_pref_it_is_always_the_case_that dec_pat_pref_it_is_always_the_case_that
                    {
                    pushFollow(FOLLOW_pat_pref_it_is_always_the_case_that_in_dec_pat_pref_itis789);
                    pat_pref_it_is_always_the_case_that();

                    state._fsp--;

                    pushFollow(FOLLOW_dec_pat_pref_it_is_always_the_case_that_in_dec_pat_pref_itis791);
                    dec_pat_pref_it_is_always_the_case_that24=dec_pat_pref_it_is_always_the_case_that();

                    state._fsp--;

                    result =dec_pat_pref_it_is_always_the_case_that24;

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
        return result;
    }
    // $ANTLR end "dec_pat_pref_itis"


    // $ANTLR start "pattern_instabs"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:229:1: pattern_instabs returns [ Vector<CDD> result ] : KW_NEVER KW_THE KW_CASE KW_THAT qorExp KW_HOLDS ;
    public final Vector<CDD> pattern_instabs() throws RecognitionException {
        Vector<CDD> result = null;

        CDD qorExp25 = null;


        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:231:2: ( KW_NEVER KW_THE KW_CASE KW_THAT qorExp KW_HOLDS )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:231:22: KW_NEVER KW_THE KW_CASE KW_THAT qorExp KW_HOLDS
            {
            match(input,KW_NEVER,FOLLOW_KW_NEVER_in_pattern_instabs814); 
            match(input,KW_THE,FOLLOW_KW_THE_in_pattern_instabs816); 
            match(input,KW_CASE,FOLLOW_KW_CASE_in_pattern_instabs818); 
            match(input,KW_THAT,FOLLOW_KW_THAT_in_pattern_instabs820); 
            pushFollow(FOLLOW_qorExp_in_pattern_instabs822);
            qorExp25=qorExp();

            state._fsp--;

            match(input,KW_HOLDS,FOLLOW_KW_HOLDS_in_pattern_instabs824); 
            result =new Vector<CDD>(); result.add(qorExp25);

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return result;
    }
    // $ANTLR end "pattern_instabs"


    // $ANTLR start "dec_pattern_instabs"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:234:1: dec_pattern_instabs returns [ srParsePattern result ] : ;
    public final srParsePattern dec_pattern_instabs() throws RecognitionException {
        srParsePattern result = null;

        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:236:2: ()
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:236:4: 
            {
            result =new srParsePattern(); result.setPattern( result.new InstAbsPattern());

            }

        }
        finally {
        }
        return result;
    }
    // $ANTLR end "dec_pattern_instabs"


    // $ANTLR start "pat_pref_it_always"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:241:1: pat_pref_it_always : KW_ALWAYS ;
    public final void pat_pref_it_always() throws RecognitionException {
        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:242:2: ( KW_ALWAYS )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:242:22: KW_ALWAYS
            {
            match(input,KW_ALWAYS,FOLLOW_KW_ALWAYS_in_pat_pref_it_always858); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "pat_pref_it_always"


    // $ANTLR start "dec_pat_pref_it_always"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:246:1: dec_pat_pref_it_always returns [ srParsePattern result ] : pat_pref_it_is_always_the_case_that dec_pat_pref_it_is_always_the_case_that ;
    public final srParsePattern dec_pat_pref_it_always() throws RecognitionException, ENotDeclaredIdentifier {
        srParsePattern result = null;

        srParsePattern dec_pat_pref_it_is_always_the_case_that26 = null;


        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:248:2: ( pat_pref_it_is_always_the_case_that dec_pat_pref_it_is_always_the_case_that )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:248:4: pat_pref_it_is_always_the_case_that dec_pat_pref_it_is_always_the_case_that
            {
            pushFollow(FOLLOW_pat_pref_it_is_always_the_case_that_in_dec_pat_pref_it_always876);
            pat_pref_it_is_always_the_case_that();

            state._fsp--;

            pushFollow(FOLLOW_dec_pat_pref_it_is_always_the_case_that_in_dec_pat_pref_it_always878);
            dec_pat_pref_it_is_always_the_case_that26=dec_pat_pref_it_is_always_the_case_that();

            state._fsp--;

            result =dec_pat_pref_it_is_always_the_case_that26;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return result;
    }
    // $ANTLR end "dec_pat_pref_it_always"


    // $ANTLR start "pat_pref_it_is_always_the_case_that"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:252:1: pat_pref_it_is_always_the_case_that : KW_THE KW_CASE KW_THAT ;
    public final void pat_pref_it_is_always_the_case_that() throws RecognitionException {
        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:253:2: ( KW_THE KW_CASE KW_THAT )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:253:27: KW_THE KW_CASE KW_THAT
            {
            match(input,KW_THE,FOLLOW_KW_THE_in_pat_pref_it_is_always_the_case_that895); 
            match(input,KW_CASE,FOLLOW_KW_CASE_in_pat_pref_it_is_always_the_case_that897); 
            match(input,KW_THAT,FOLLOW_KW_THAT_in_pat_pref_it_is_always_the_case_that899); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "pat_pref_it_is_always_the_case_that"


    // $ANTLR start "dec_pat_pref_it_is_always_the_case_that"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:256:1: dec_pat_pref_it_is_always_the_case_that returns [ srParsePattern result ] : ( pattern_univers dec_pattern_univers | pat_pref_it_is_always_the_case_that_if_E_holds dec_pat_pref_it_is_always_the_case_that_if_E_holds | pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for dec_pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for );
    public final srParsePattern dec_pat_pref_it_is_always_the_case_that() throws RecognitionException, ENotDeclaredIdentifier {
        srParsePattern result = null;

        srParsePattern dec_pattern_univers27 = null;

        Vector<CDD> pattern_univers28 = null;

        srParsePattern dec_pat_pref_it_is_always_the_case_that_if_E_holds29 = null;

        Vector<CDD> pat_pref_it_is_always_the_case_that_if_E_holds30 = null;

        srParsePattern dec_pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for31 = null;

        Vector<CDD> pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for32 = null;


        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:258:2: ( pattern_univers dec_pattern_univers | pat_pref_it_is_always_the_case_that_if_E_holds dec_pat_pref_it_is_always_the_case_that_if_E_holds | pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for dec_pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for )
            int alt18=3;
            switch ( input.LA(1) ) {
            case QUOTE:
            case NOT_1:
            case KW_NOT:
            case BR_OPEN:
            case ID:
                {
                alt18=1;
                }
                break;
            case KW_IF:
                {
                alt18=2;
                }
                break;
            case KW_ONCE:
                {
                alt18=3;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("", 18, 0, input);

                throw nvae;
            }

            switch (alt18) {
                case 1 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:258:4: pattern_univers dec_pattern_univers
                    {
                    pushFollow(FOLLOW_pattern_univers_in_dec_pat_pref_it_is_always_the_case_that914);
                    pattern_univers28=pattern_univers();

                    state._fsp--;

                    pushFollow(FOLLOW_dec_pattern_univers_in_dec_pat_pref_it_is_always_the_case_that916);
                    dec_pattern_univers27=dec_pattern_univers();

                    state._fsp--;

                    result =dec_pattern_univers27; result.mergeCDDs(pattern_univers28);

                    }
                    break;
                case 2 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:259:4: pat_pref_it_is_always_the_case_that_if_E_holds dec_pat_pref_it_is_always_the_case_that_if_E_holds
                    {
                    pushFollow(FOLLOW_pat_pref_it_is_always_the_case_that_if_E_holds_in_dec_pat_pref_it_is_always_the_case_that923);
                    pat_pref_it_is_always_the_case_that_if_E_holds30=pat_pref_it_is_always_the_case_that_if_E_holds();

                    state._fsp--;

                    pushFollow(FOLLOW_dec_pat_pref_it_is_always_the_case_that_if_E_holds_in_dec_pat_pref_it_is_always_the_case_that925);
                    dec_pat_pref_it_is_always_the_case_that_if_E_holds29=dec_pat_pref_it_is_always_the_case_that_if_E_holds();

                    state._fsp--;

                    result =dec_pat_pref_it_is_always_the_case_that_if_E_holds29; result.mergeCDDs(pat_pref_it_is_always_the_case_that_if_E_holds30);

                    }
                    break;
                case 3 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:260:4: pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for dec_pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for
                    {
                    pushFollow(FOLLOW_pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for_in_dec_pat_pref_it_is_always_the_case_that932);
                    pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for32=pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for();

                    state._fsp--;

                    pushFollow(FOLLOW_dec_pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for_in_dec_pat_pref_it_is_always_the_case_that934);
                    dec_pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for31=dec_pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for();

                    state._fsp--;

                    result =dec_pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for31; result.mergeCDDs(pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for32);

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
        return result;
    }
    // $ANTLR end "dec_pat_pref_it_is_always_the_case_that"


    // $ANTLR start "pattern_univers"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:272:1: pattern_univers returns [ Vector<CDD> result ] : qorExp KW_HOLDS ;
    public final Vector<CDD> pattern_univers() throws RecognitionException {
        Vector<CDD> result = null;

        CDD qorExp33 = null;


        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:274:2: ( qorExp KW_HOLDS )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:274:44: qorExp KW_HOLDS
            {
            pushFollow(FOLLOW_qorExp_in_pattern_univers963);
            qorExp33=qorExp();

            state._fsp--;

            match(input,KW_HOLDS,FOLLOW_KW_HOLDS_in_pattern_univers965); 
            result =new Vector<CDD>(); result.add(qorExp33);

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return result;
    }
    // $ANTLR end "pattern_univers"


    // $ANTLR start "dec_pattern_univers"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:277:1: dec_pattern_univers returns [ srParsePattern result ] : ( pattern_bnd_recc dec_pattern_bnd_recc | );
    public final srParsePattern dec_pattern_univers() throws RecognitionException {
        srParsePattern result = null;

        srParsePattern dec_pattern_bnd_recc34 = null;

        int pattern_bnd_recc35 = 0;


        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:279:2: ( pattern_bnd_recc dec_pattern_bnd_recc | )
            int alt19=2;
            int LA19_0 = input.LA(1);

            if ( (LA19_0==KW_AT) ) {
                alt19=1;
            }
            else if ( (LA19_0==PKT||LA19_0==EOL) ) {
                alt19=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 19, 0, input);

                throw nvae;
            }
            switch (alt19) {
                case 1 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:279:4: pattern_bnd_recc dec_pattern_bnd_recc
                    {
                    pushFollow(FOLLOW_pattern_bnd_recc_in_dec_pattern_univers982);
                    pattern_bnd_recc35=pattern_bnd_recc();

                    state._fsp--;

                    pushFollow(FOLLOW_dec_pattern_bnd_recc_in_dec_pattern_univers984);
                    dec_pattern_bnd_recc34=dec_pattern_bnd_recc();

                    state._fsp--;

                    result =dec_pattern_bnd_recc34; result.setDuration(pattern_bnd_recc35);

                    }
                    break;
                case 2 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:280:4: 
                    {
                    result =new srParsePattern(); result.setPattern( result.new UniversalityPattern());

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
        return result;
    }
    // $ANTLR end "dec_pattern_univers"


    // $ANTLR start "pat_pref_it_is_always_the_case_that_if_E_holds"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:285:1: pat_pref_it_is_always_the_case_that_if_E_holds returns [ Vector<CDD> result ] : KW_IF qorExp KW_HOLDS ;
    public final Vector<CDD> pat_pref_it_is_always_the_case_that_if_E_holds() throws RecognitionException {
        Vector<CDD> result = null;

        CDD qorExp36 = null;


        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:287:2: ( KW_IF qorExp KW_HOLDS )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:287:44: KW_IF qorExp KW_HOLDS
            {
            match(input,KW_IF,FOLLOW_KW_IF_in_pat_pref_it_is_always_the_case_that_if_E_holds1013); 
            pushFollow(FOLLOW_qorExp_in_pat_pref_it_is_always_the_case_that_if_E_holds1015);
            qorExp36=qorExp();

            state._fsp--;

            match(input,KW_HOLDS,FOLLOW_KW_HOLDS_in_pat_pref_it_is_always_the_case_that_if_E_holds1017); 
            result =new Vector<CDD>(); result.add(qorExp36);

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return result;
    }
    // $ANTLR end "pat_pref_it_is_always_the_case_that_if_E_holds"


    // $ANTLR start "dec_pat_pref_it_is_always_the_case_that_if_E_holds"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:292:1: dec_pat_pref_it_is_always_the_case_that_if_E_holds returns [ srParsePattern result ] : ( pat_pref_it_is_always_the_case_that_if_E_holds_then_E dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E | pat_pref_it_is_always_the_case_that_if_E_holds_and_is_suc_by_E_then_E dec_pat_pref_it_is_always_the_case_that_if_E_holds_and_is_suc_by_E_then_E );
    public final srParsePattern dec_pat_pref_it_is_always_the_case_that_if_E_holds() throws RecognitionException, ENotDeclaredIdentifier {
        srParsePattern result = null;

        srParsePattern dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E37 = null;

        Vector<CDD> pat_pref_it_is_always_the_case_that_if_E_holds_then_E38 = null;

        srParsePattern dec_pat_pref_it_is_always_the_case_that_if_E_holds_and_is_suc_by_E_then_E39 = null;

        Vector<CDD> pat_pref_it_is_always_the_case_that_if_E_holds_and_is_suc_by_E_then_E40 = null;


        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:294:2: ( pat_pref_it_is_always_the_case_that_if_E_holds_then_E dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E | pat_pref_it_is_always_the_case_that_if_E_holds_and_is_suc_by_E_then_E dec_pat_pref_it_is_always_the_case_that_if_E_holds_and_is_suc_by_E_then_E )
            int alt20=2;
            int LA20_0 = input.LA(1);

            if ( (LA20_0==K||LA20_0==KW_THEN) ) {
                alt20=1;
            }
            else if ( (LA20_0==KW_AND) ) {
                alt20=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 20, 0, input);

                throw nvae;
            }
            switch (alt20) {
                case 1 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:294:4: pat_pref_it_is_always_the_case_that_if_E_holds_then_E dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E
                    {
                    pushFollow(FOLLOW_pat_pref_it_is_always_the_case_that_if_E_holds_then_E_in_dec_pat_pref_it_is_always_the_case_that_if_E_holds1038);
                    pat_pref_it_is_always_the_case_that_if_E_holds_then_E38=pat_pref_it_is_always_the_case_that_if_E_holds_then_E();

                    state._fsp--;

                    pushFollow(FOLLOW_dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E_in_dec_pat_pref_it_is_always_the_case_that_if_E_holds1040);
                    dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E37=dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E();

                    state._fsp--;

                    result =dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E37; result.mergeCDDs(pat_pref_it_is_always_the_case_that_if_E_holds_then_E38);

                    }
                    break;
                case 2 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:295:4: pat_pref_it_is_always_the_case_that_if_E_holds_and_is_suc_by_E_then_E dec_pat_pref_it_is_always_the_case_that_if_E_holds_and_is_suc_by_E_then_E
                    {
                    pushFollow(FOLLOW_pat_pref_it_is_always_the_case_that_if_E_holds_and_is_suc_by_E_then_E_in_dec_pat_pref_it_is_always_the_case_that_if_E_holds1047);
                    pat_pref_it_is_always_the_case_that_if_E_holds_and_is_suc_by_E_then_E40=pat_pref_it_is_always_the_case_that_if_E_holds_and_is_suc_by_E_then_E();

                    state._fsp--;

                    pushFollow(FOLLOW_dec_pat_pref_it_is_always_the_case_that_if_E_holds_and_is_suc_by_E_then_E_in_dec_pat_pref_it_is_always_the_case_that_if_E_holds1049);
                    dec_pat_pref_it_is_always_the_case_that_if_E_holds_and_is_suc_by_E_then_E39=dec_pat_pref_it_is_always_the_case_that_if_E_holds_and_is_suc_by_E_then_E();

                    state._fsp--;

                    result =dec_pat_pref_it_is_always_the_case_that_if_E_holds_and_is_suc_by_E_then_E39; result.mergeCDDs(pat_pref_it_is_always_the_case_that_if_E_holds_and_is_suc_by_E_then_E40);

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
        return result;
    }
    // $ANTLR end "dec_pat_pref_it_is_always_the_case_that_if_E_holds"


    // $ANTLR start "pat_pref_it_is_always_the_case_that_if_E_holds_then_E"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:300:1: pat_pref_it_is_always_the_case_that_if_E_holds_then_E returns [ Vector<CDD> result ] : ( K )? KW_THEN qorExp ;
    public final Vector<CDD> pat_pref_it_is_always_the_case_that_if_E_holds_then_E() throws RecognitionException {
        Vector<CDD> result = null;

        CDD qorExp41 = null;


        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:302:2: ( ( K )? KW_THEN qorExp )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:302:55: ( K )? KW_THEN qorExp
            {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:302:55: ( K )?
            int alt21=2;
            int LA21_0 = input.LA(1);

            if ( (LA21_0==K) ) {
                alt21=1;
            }
            switch (alt21) {
                case 1 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:302:56: K
                    {
                    match(input,K,FOLLOW_K_in_pat_pref_it_is_always_the_case_that_if_E_holds_then_E1073); 

                    }
                    break;

            }

            match(input,KW_THEN,FOLLOW_KW_THEN_in_pat_pref_it_is_always_the_case_that_if_E_holds_then_E1077); 
            pushFollow(FOLLOW_qorExp_in_pat_pref_it_is_always_the_case_that_if_E_holds_then_E1079);
            qorExp41=qorExp();

            state._fsp--;

            result =new Vector<CDD>(); result.add(qorExp41);

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return result;
    }
    // $ANTLR end "pat_pref_it_is_always_the_case_that_if_E_holds_then_E"


    // $ANTLR start "dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:305:1: dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E returns [ srParsePattern result ] : ( pattern_precedence dec_pattern_precedence | pattern_response dec_pattern_response | pat_pref_it_is_always_the_case_that_if_E_holds_then_E_holds dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E_holds );
    public final srParsePattern dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E() throws RecognitionException, ENotDeclaredIdentifier {
        srParsePattern result = null;

        srParsePattern dec_pattern_precedence42 = null;

        srParsePattern dec_pattern_response43 = null;

        srParsePattern dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E_holds44 = null;


        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:307:2: ( pattern_precedence dec_pattern_precedence | pattern_response dec_pattern_response | pat_pref_it_is_always_the_case_that_if_E_holds_then_E_holds dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E_holds )
            int alt22=3;
            switch ( input.LA(1) ) {
            case KW_PREV:
                {
                alt22=1;
                }
                break;
            case KW_EVENTUALLY:
                {
                alt22=2;
                }
                break;
            case KW_HOLDS:
                {
                alt22=3;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("", 22, 0, input);

                throw nvae;
            }

            switch (alt22) {
                case 1 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:307:4: pattern_precedence dec_pattern_precedence
                    {
                    pushFollow(FOLLOW_pattern_precedence_in_dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E1096);
                    pattern_precedence();

                    state._fsp--;

                    pushFollow(FOLLOW_dec_pattern_precedence_in_dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E1098);
                    dec_pattern_precedence42=dec_pattern_precedence();

                    state._fsp--;

                    result =dec_pattern_precedence42; 

                    }
                    break;
                case 2 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:308:4: pattern_response dec_pattern_response
                    {
                    pushFollow(FOLLOW_pattern_response_in_dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E1105);
                    pattern_response();

                    state._fsp--;

                    pushFollow(FOLLOW_dec_pattern_response_in_dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E1107);
                    dec_pattern_response43=dec_pattern_response();

                    state._fsp--;

                    result =dec_pattern_response43;

                    }
                    break;
                case 3 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:309:4: pat_pref_it_is_always_the_case_that_if_E_holds_then_E_holds dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E_holds
                    {
                    pushFollow(FOLLOW_pat_pref_it_is_always_the_case_that_if_E_holds_then_E_holds_in_dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E1114);
                    pat_pref_it_is_always_the_case_that_if_E_holds_then_E_holds();

                    state._fsp--;

                    pushFollow(FOLLOW_dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E_holds_in_dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E1116);
                    dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E_holds44=dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E_holds();

                    state._fsp--;

                    result =dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E_holds44;

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
        return result;
    }
    // $ANTLR end "dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E"


    // $ANTLR start "pattern_precedence"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:321:1: pattern_precedence : KW_PREV KW_HELD ;
    public final void pattern_precedence() throws RecognitionException {
        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:322:2: ( KW_PREV KW_HELD )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:322:62: KW_PREV KW_HELD
            {
            match(input,KW_PREV,FOLLOW_KW_PREV_in_pattern_precedence1142); 
            match(input,KW_HELD,FOLLOW_KW_HELD_in_pattern_precedence1144); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "pattern_precedence"


    // $ANTLR start "dec_pattern_precedence"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:324:1: dec_pattern_precedence returns [ srParsePattern result ] : ( pattern_pred_chain21 dec_pattern_pred_chain21 | );
    public final srParsePattern dec_pattern_precedence() throws RecognitionException, ENotDeclaredIdentifier {
        srParsePattern result = null;

        srParsePattern dec_pattern_pred_chain2145 = null;

        Vector<CDD> pattern_pred_chain2146 = null;


        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:326:2: ( pattern_pred_chain21 dec_pattern_pred_chain21 | )
            int alt23=2;
            int LA23_0 = input.LA(1);

            if ( (LA23_0==KW_AND) ) {
                alt23=1;
            }
            else if ( (LA23_0==PKT||LA23_0==EOL) ) {
                alt23=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 23, 0, input);

                throw nvae;
            }
            switch (alt23) {
                case 1 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:326:4: pattern_pred_chain21 dec_pattern_pred_chain21
                    {
                    pushFollow(FOLLOW_pattern_pred_chain21_in_dec_pattern_precedence1157);
                    pattern_pred_chain2146=pattern_pred_chain21();

                    state._fsp--;

                    pushFollow(FOLLOW_dec_pattern_pred_chain21_in_dec_pattern_precedence1159);
                    dec_pattern_pred_chain2145=dec_pattern_pred_chain21();

                    state._fsp--;

                    result =dec_pattern_pred_chain2145; result.mergeCDDs(pattern_pred_chain2146);

                    }
                    break;
                case 2 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:327:4: 
                    {
                    result =new srParsePattern(); result.setPattern( result.new PrecedencePattern());

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
        return result;
    }
    // $ANTLR end "dec_pattern_precedence"


    // $ANTLR start "pattern_pred_chain21"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:331:1: pattern_pred_chain21 returns [ Vector<CDD> result ] : KW_AND KW_WAS KW_PREC KW_BY qorExp ;
    public final Vector<CDD> pattern_pred_chain21() throws RecognitionException {
        Vector<CDD> result = null;

        CDD qorExp47 = null;


        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:333:2: ( KW_AND KW_WAS KW_PREC KW_BY qorExp )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:333:27: KW_AND KW_WAS KW_PREC KW_BY qorExp
            {
            match(input,KW_AND,FOLLOW_KW_AND_in_pattern_pred_chain211185); 
            match(input,KW_WAS,FOLLOW_KW_WAS_in_pattern_pred_chain211187); 
            match(input,KW_PREC,FOLLOW_KW_PREC_in_pattern_pred_chain211189); 
            match(input,KW_BY,FOLLOW_KW_BY_in_pattern_pred_chain211191); 
            pushFollow(FOLLOW_qorExp_in_pattern_pred_chain211193);
            qorExp47=qorExp();

            state._fsp--;

            result =new Vector<CDD>(); result.add(qorExp47);

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return result;
    }
    // $ANTLR end "pattern_pred_chain21"


    // $ANTLR start "dec_pattern_pred_chain21"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:336:1: dec_pattern_pred_chain21 returns [ srParsePattern result ] : ;
    public final srParsePattern dec_pattern_pred_chain21() throws RecognitionException {
        srParsePattern result = null;

        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:338:2: ()
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:338:4: 
            {
            result =new srParsePattern(); result.setPattern( result.new ResponseChain21Pattern());

            }

        }
        finally {
        }
        return result;
    }
    // $ANTLR end "dec_pattern_pred_chain21"


    // $ANTLR start "pat_pref_it_is_always_the_case_that_if_E_holds_and_is_suc_by_E_then_E"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:341:1: pat_pref_it_is_always_the_case_that_if_E_holds_and_is_suc_by_E_then_E returns [ Vector<CDD> result ] : KW_AND KW_IS KW_SUCC KW_BY e1= qorExp KW_THEN e2= qorExp ;
    public final Vector<CDD> pat_pref_it_is_always_the_case_that_if_E_holds_and_is_suc_by_E_then_E() throws RecognitionException {
        Vector<CDD> result = null;

        CDD e1 = null;

        CDD e2 = null;


        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:343:2: ( KW_AND KW_IS KW_SUCC KW_BY e1= qorExp KW_THEN e2= qorExp )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:343:55: KW_AND KW_IS KW_SUCC KW_BY e1= qorExp KW_THEN e2= qorExp
            {
            match(input,KW_AND,FOLLOW_KW_AND_in_pat_pref_it_is_always_the_case_that_if_E_holds_and_is_suc_by_E_then_E1228); 
            match(input,KW_IS,FOLLOW_KW_IS_in_pat_pref_it_is_always_the_case_that_if_E_holds_and_is_suc_by_E_then_E1230); 
            match(input,KW_SUCC,FOLLOW_KW_SUCC_in_pat_pref_it_is_always_the_case_that_if_E_holds_and_is_suc_by_E_then_E1232); 
            match(input,KW_BY,FOLLOW_KW_BY_in_pat_pref_it_is_always_the_case_that_if_E_holds_and_is_suc_by_E_then_E1234); 
            pushFollow(FOLLOW_qorExp_in_pat_pref_it_is_always_the_case_that_if_E_holds_and_is_suc_by_E_then_E1238);
            e1=qorExp();

            state._fsp--;

            match(input,KW_THEN,FOLLOW_KW_THEN_in_pat_pref_it_is_always_the_case_that_if_E_holds_and_is_suc_by_E_then_E1240); 
            pushFollow(FOLLOW_qorExp_in_pat_pref_it_is_always_the_case_that_if_E_holds_and_is_suc_by_E_then_E1244);
            e2=qorExp();

            state._fsp--;

            result =new Vector<CDD>(); result.add(e2);result.add(e1);

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return result;
    }
    // $ANTLR end "pat_pref_it_is_always_the_case_that_if_E_holds_and_is_suc_by_E_then_E"


    // $ANTLR start "dec_pat_pref_it_is_always_the_case_that_if_E_holds_and_is_suc_by_E_then_E"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:347:1: dec_pat_pref_it_is_always_the_case_that_if_E_holds_and_is_suc_by_E_then_E returns [ srParsePattern result ] : ( pattern_pred_chain12 dec_pattern_pred_chain12 | pattern_resp_chain21 dec_pattern_resp_chain21 );
    public final srParsePattern dec_pat_pref_it_is_always_the_case_that_if_E_holds_and_is_suc_by_E_then_E() throws RecognitionException, ENotDeclaredIdentifier {
        srParsePattern result = null;

        srParsePattern dec_pattern_pred_chain1248 = null;

        srParsePattern dec_pattern_resp_chain2149 = null;

        Vector<CDD> pattern_resp_chain2150 = null;


        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:349:2: ( pattern_pred_chain12 dec_pattern_pred_chain12 | pattern_resp_chain21 dec_pattern_resp_chain21 )
            int alt24=2;
            int LA24_0 = input.LA(1);

            if ( (LA24_0==KW_PREV) ) {
                alt24=1;
            }
            else if ( (LA24_0==KW_EVENTUALLY) ) {
                alt24=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 24, 0, input);

                throw nvae;
            }
            switch (alt24) {
                case 1 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:349:4: pattern_pred_chain12 dec_pattern_pred_chain12
                    {
                    pushFollow(FOLLOW_pattern_pred_chain12_in_dec_pat_pref_it_is_always_the_case_that_if_E_holds_and_is_suc_by_E_then_E1263);
                    pattern_pred_chain12();

                    state._fsp--;

                    pushFollow(FOLLOW_dec_pattern_pred_chain12_in_dec_pat_pref_it_is_always_the_case_that_if_E_holds_and_is_suc_by_E_then_E1265);
                    dec_pattern_pred_chain1248=dec_pattern_pred_chain12();

                    state._fsp--;

                    result =dec_pattern_pred_chain1248;

                    }
                    break;
                case 2 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:350:4: pattern_resp_chain21 dec_pattern_resp_chain21
                    {
                    pushFollow(FOLLOW_pattern_resp_chain21_in_dec_pat_pref_it_is_always_the_case_that_if_E_holds_and_is_suc_by_E_then_E1272);
                    pattern_resp_chain2150=pattern_resp_chain21();

                    state._fsp--;

                    pushFollow(FOLLOW_dec_pattern_resp_chain21_in_dec_pat_pref_it_is_always_the_case_that_if_E_holds_and_is_suc_by_E_then_E1274);
                    dec_pattern_resp_chain2149=dec_pattern_resp_chain21();

                    state._fsp--;

                    result =dec_pattern_resp_chain2149; result.mergeCDDs(pattern_resp_chain2150);

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
        return result;
    }
    // $ANTLR end "dec_pat_pref_it_is_always_the_case_that_if_E_holds_and_is_suc_by_E_then_E"


    // $ANTLR start "pattern_pred_chain12"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:355:1: pattern_pred_chain12 : KW_PREV KW_HELD ;
    public final void pattern_pred_chain12() throws RecognitionException {
        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:356:2: ( KW_PREV KW_HELD )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:356:78: KW_PREV KW_HELD
            {
            match(input,KW_PREV,FOLLOW_KW_PREV_in_pattern_pred_chain121293); 
            match(input,KW_HELD,FOLLOW_KW_HELD_in_pattern_pred_chain121295); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "pattern_pred_chain12"


    // $ANTLR start "dec_pattern_pred_chain12"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:359:1: dec_pattern_pred_chain12 returns [ srParsePattern result ] : ;
    public final srParsePattern dec_pattern_pred_chain12() throws RecognitionException {
        srParsePattern result = null;

        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:361:2: ()
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:361:4: 
            {
            result =new srParsePattern(); result.setPattern( result.new PrecedenceChain12Pattern());

            }

        }
        finally {
        }
        return result;
    }
    // $ANTLR end "dec_pattern_pred_chain12"


    // $ANTLR start "pattern_response"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:365:1: pattern_response : KW_EVENTUALLY KW_HOLDS ;
    public final void pattern_response() throws RecognitionException {
        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:366:2: ( KW_EVENTUALLY KW_HOLDS )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:366:62: KW_EVENTUALLY KW_HOLDS
            {
            match(input,KW_EVENTUALLY,FOLLOW_KW_EVENTUALLY_in_pattern_response1325); 
            match(input,KW_HOLDS,FOLLOW_KW_HOLDS_in_pattern_response1327); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "pattern_response"


    // $ANTLR start "dec_pattern_response"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:369:1: dec_pattern_response returns [ srParsePattern result ] : ;
    public final srParsePattern dec_pattern_response() throws RecognitionException {
        srParsePattern result = null;

        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:371:2: ()
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:371:4: 
            {
            result =new srParsePattern(); result.setPattern( result.new InstAbsPattern());

            }

        }
        finally {
        }
        return result;
    }
    // $ANTLR end "dec_pattern_response"


    // $ANTLR start "dec_pattern_responde"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:374:1: dec_pattern_responde returns [ srParsePattern result ] : ( pattern_resp_chain12 dec_pattern_resp_chain12 | );
    public final srParsePattern dec_pattern_responde() throws RecognitionException, ENotDeclaredIdentifier {
        srParsePattern result = null;

        srParsePattern dec_pattern_resp_chain1251 = null;

        Vector<CDD> pattern_resp_chain1252 = null;


        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:376:2: ( pattern_resp_chain12 dec_pattern_resp_chain12 | )
            int alt25=2;
            int LA25_0 = input.LA(1);

            if ( (LA25_0==KW_AND) ) {
                alt25=1;
            }
            else if ( (LA25_0==EOF) ) {
                alt25=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 25, 0, input);

                throw nvae;
            }
            switch (alt25) {
                case 1 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:376:4: pattern_resp_chain12 dec_pattern_resp_chain12
                    {
                    pushFollow(FOLLOW_pattern_resp_chain12_in_dec_pattern_responde1357);
                    pattern_resp_chain1252=pattern_resp_chain12();

                    state._fsp--;

                    pushFollow(FOLLOW_dec_pattern_resp_chain12_in_dec_pattern_responde1359);
                    dec_pattern_resp_chain1251=dec_pattern_resp_chain12();

                    state._fsp--;

                    result =dec_pattern_resp_chain1251; result.mergeCDDs(pattern_resp_chain1252);

                    }
                    break;
                case 2 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:377:4: 
                    {
                    result =new srParsePattern(); result.setPattern( result.new ResponsePattern());

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
        return result;
    }
    // $ANTLR end "dec_pattern_responde"


    // $ANTLR start "pattern_resp_chain12"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:381:1: pattern_resp_chain12 returns [ Vector<CDD> result ] : KW_AND KW_IS KW_SUCC KW_BY qorExp ;
    public final Vector<CDD> pattern_resp_chain12() throws RecognitionException {
        Vector<CDD> result = null;

        CDD qorExp53 = null;


        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:383:2: ( KW_AND KW_IS KW_SUCC KW_BY qorExp )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:383:25: KW_AND KW_IS KW_SUCC KW_BY qorExp
            {
            match(input,KW_AND,FOLLOW_KW_AND_in_pattern_resp_chain121385); 
            match(input,KW_IS,FOLLOW_KW_IS_in_pattern_resp_chain121387); 
            match(input,KW_SUCC,FOLLOW_KW_SUCC_in_pattern_resp_chain121389); 
            match(input,KW_BY,FOLLOW_KW_BY_in_pattern_resp_chain121391); 
            pushFollow(FOLLOW_qorExp_in_pattern_resp_chain121393);
            qorExp53=qorExp();

            state._fsp--;

            result =new Vector<CDD>(); result.add(qorExp53);

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return result;
    }
    // $ANTLR end "pattern_resp_chain12"


    // $ANTLR start "dec_pattern_resp_chain12"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:387:1: dec_pattern_resp_chain12 returns [ srParsePattern result ] : ( pattern_constr_chain dec_pattern_constr_chain | );
    public final srParsePattern dec_pattern_resp_chain12() throws RecognitionException, ENotDeclaredIdentifier {
        srParsePattern result = null;

        srParsePattern dec_pattern_constr_chain54 = null;

        Vector<CDD> pattern_constr_chain55 = null;


        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:389:2: ( pattern_constr_chain dec_pattern_constr_chain | )
            int alt26=2;
            int LA26_0 = input.LA(1);

            if ( (LA26_0==KW_WHERE) ) {
                alt26=1;
            }
            else if ( (LA26_0==EOF) ) {
                alt26=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 26, 0, input);

                throw nvae;
            }
            switch (alt26) {
                case 1 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:389:4: pattern_constr_chain dec_pattern_constr_chain
                    {
                    pushFollow(FOLLOW_pattern_constr_chain_in_dec_pattern_resp_chain121413);
                    pattern_constr_chain55=pattern_constr_chain();

                    state._fsp--;

                    pushFollow(FOLLOW_dec_pattern_constr_chain_in_dec_pattern_resp_chain121415);
                    dec_pattern_constr_chain54=dec_pattern_constr_chain();

                    state._fsp--;

                    result =dec_pattern_constr_chain54; result.mergeCDDs(pattern_constr_chain55);

                    }
                    break;
                case 2 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:390:4: 
                    {
                    result =new srParsePattern(); result.setPattern( result.new ResponseChain12Pattern());

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
        return result;
    }
    // $ANTLR end "dec_pattern_resp_chain12"


    // $ANTLR start "pattern_constr_chain"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:395:1: pattern_constr_chain returns [ Vector<CDD> result ] : KW_WHERE e1= qorExp KW_DOES KW_NOT KW_HOLD SC_BETWEEN e2= orExp KW_AND e3= qorExp ;
    public final Vector<CDD> pattern_constr_chain() throws RecognitionException {
        Vector<CDD> result = null;

        CDD e1 = null;

        CDD e2 = null;

        CDD e3 = null;


        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:397:2: ( KW_WHERE e1= qorExp KW_DOES KW_NOT KW_HOLD SC_BETWEEN e2= orExp KW_AND e3= qorExp )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:397:29: KW_WHERE e1= qorExp KW_DOES KW_NOT KW_HOLD SC_BETWEEN e2= orExp KW_AND e3= qorExp
            {
            match(input,KW_WHERE,FOLLOW_KW_WHERE_in_pattern_constr_chain1443); 
            pushFollow(FOLLOW_qorExp_in_pattern_constr_chain1447);
            e1=qorExp();

            state._fsp--;

            match(input,KW_DOES,FOLLOW_KW_DOES_in_pattern_constr_chain1449); 
            match(input,KW_NOT,FOLLOW_KW_NOT_in_pattern_constr_chain1451); 
            match(input,KW_HOLD,FOLLOW_KW_HOLD_in_pattern_constr_chain1453); 
            match(input,SC_BETWEEN,FOLLOW_SC_BETWEEN_in_pattern_constr_chain1455); 
            pushFollow(FOLLOW_orExp_in_pattern_constr_chain1459);
            e2=orExp();

            state._fsp--;

            match(input,KW_AND,FOLLOW_KW_AND_in_pattern_constr_chain1461); 
            pushFollow(FOLLOW_qorExp_in_pattern_constr_chain1465);
            e3=qorExp();

            state._fsp--;

            result =new Vector<CDD>(); result.add(e3);result.add(e2);result.add(e1);

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return result;
    }
    // $ANTLR end "pattern_constr_chain"


    // $ANTLR start "dec_pattern_constr_chain"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:401:1: dec_pattern_constr_chain returns [ srParsePattern result ] : ;
    public final srParsePattern dec_pattern_constr_chain() throws RecognitionException {
        srParsePattern result = null;

        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:403:2: ()
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:403:4: 
            {
            result =new srParsePattern(); result.setPattern( result.new ConstrainedChainPattern());

            }

        }
        finally {
        }
        return result;
    }
    // $ANTLR end "dec_pattern_constr_chain"


    // $ANTLR start "pattern_resp_chain21"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:407:1: pattern_resp_chain21 returns [ Vector<CDD> result ] : KW_EVENTUALLY KW_HOLDS KW_AFTER qorExp ;
    public final Vector<CDD> pattern_resp_chain21() throws RecognitionException {
        Vector<CDD> result = null;

        CDD qorExp56 = null;


        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:409:2: ( KW_EVENTUALLY KW_HOLDS KW_AFTER qorExp )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:409:78: KW_EVENTUALLY KW_HOLDS KW_AFTER qorExp
            {
            match(input,KW_EVENTUALLY,FOLLOW_KW_EVENTUALLY_in_pattern_resp_chain211503); 
            match(input,KW_HOLDS,FOLLOW_KW_HOLDS_in_pattern_resp_chain211505); 
            match(input,KW_AFTER,FOLLOW_KW_AFTER_in_pattern_resp_chain211507); 
            pushFollow(FOLLOW_qorExp_in_pattern_resp_chain211509);
            qorExp56=qorExp();

            state._fsp--;

            result =new Vector<CDD>(); result.add(qorExp56);

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return result;
    }
    // $ANTLR end "pattern_resp_chain21"


    // $ANTLR start "dec_pattern_resp_chain21"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:412:1: dec_pattern_resp_chain21 returns [ srParsePattern result ] : ;
    public final srParsePattern dec_pattern_resp_chain21() throws RecognitionException {
        srParsePattern result = null;

        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:414:2: ()
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:414:4: 
            {
            result =new srParsePattern(); result.setPattern( result.new ResponseChain21Pattern());

            }

        }
        finally {
        }
        return result;
    }
    // $ANTLR end "dec_pattern_resp_chain21"


    // $ANTLR start "pat_pref_it_is_always_the_case_that_if_E_holds_then_E_holds"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:417:1: pat_pref_it_is_always_the_case_that_if_E_holds_then_E_holds : KW_HOLDS ;
    public final void pat_pref_it_is_always_the_case_that_if_E_holds_then_E_holds() throws RecognitionException {
        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:418:2: ( KW_HOLDS )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:418:62: KW_HOLDS
            {
            match(input,KW_HOLDS,FOLLOW_KW_HOLDS_in_pat_pref_it_is_always_the_case_that_if_E_holds_then_E_holds1538); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "pat_pref_it_is_always_the_case_that_if_E_holds_then_E_holds"


    // $ANTLR start "dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E_holds"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:421:1: dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E_holds returns [ srParsePattern result ] : ( pattern_bnd_resp dec_pattern_bnd_resp | pattern_bnd_inv dec_pattern_bnd_inv | pattern_inv dec_pattern_inv );
    public final srParsePattern dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E_holds() throws RecognitionException {
        srParsePattern result = null;

        srParsePattern dec_pattern_bnd_resp57 = null;

        int pattern_bnd_resp58 = 0;

        srParsePattern dec_pattern_bnd_inv59 = null;

        int pattern_bnd_inv60 = 0;

        srParsePattern dec_pattern_inv61 = null;


        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:423:2: ( pattern_bnd_resp dec_pattern_bnd_resp | pattern_bnd_inv dec_pattern_bnd_inv | pattern_inv dec_pattern_inv )
            int alt27=3;
            switch ( input.LA(1) ) {
            case KW_AFTER:
                {
                alt27=1;
                }
                break;
            case KW_FOR:
                {
                alt27=2;
                }
                break;
            case KW_AS:
                {
                alt27=3;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("", 27, 0, input);

                throw nvae;
            }

            switch (alt27) {
                case 1 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:423:4: pattern_bnd_resp dec_pattern_bnd_resp
                    {
                    pushFollow(FOLLOW_pattern_bnd_resp_in_dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E_holds1552);
                    pattern_bnd_resp58=pattern_bnd_resp();

                    state._fsp--;

                    pushFollow(FOLLOW_dec_pattern_bnd_resp_in_dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E_holds1554);
                    dec_pattern_bnd_resp57=dec_pattern_bnd_resp();

                    state._fsp--;

                    result =dec_pattern_bnd_resp57; result.setDuration(pattern_bnd_resp58);

                    }
                    break;
                case 2 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:424:4: pattern_bnd_inv dec_pattern_bnd_inv
                    {
                    pushFollow(FOLLOW_pattern_bnd_inv_in_dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E_holds1562);
                    pattern_bnd_inv60=pattern_bnd_inv();

                    state._fsp--;

                    pushFollow(FOLLOW_dec_pattern_bnd_inv_in_dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E_holds1564);
                    dec_pattern_bnd_inv59=dec_pattern_bnd_inv();

                    state._fsp--;

                    result =dec_pattern_bnd_inv59; result.setDuration(pattern_bnd_inv60);

                    }
                    break;
                case 3 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:425:4: pattern_inv dec_pattern_inv
                    {
                    pushFollow(FOLLOW_pattern_inv_in_dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E_holds1571);
                    pattern_inv();

                    state._fsp--;

                    pushFollow(FOLLOW_dec_pattern_inv_in_dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E_holds1573);
                    dec_pattern_inv61=dec_pattern_inv();

                    state._fsp--;

                    result =dec_pattern_inv61;

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
        return result;
    }
    // $ANTLR end "dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E_holds"


    // $ANTLR start "pattern_bnd_resp"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:428:1: pattern_bnd_resp returns [ int dur ] : KW_AFTER KW_AT KW_MOST num KW_TIME KW_UNITS ;
    public final int pattern_bnd_resp() throws RecognitionException {
        int dur = 0;

        int num62 = 0;


        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:430:2: ( KW_AFTER KW_AT KW_MOST num KW_TIME KW_UNITS )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:430:68: KW_AFTER KW_AT KW_MOST num KW_TIME KW_UNITS
            {
            match(input,KW_AFTER,FOLLOW_KW_AFTER_in_pattern_bnd_resp1593); 
            match(input,KW_AT,FOLLOW_KW_AT_in_pattern_bnd_resp1595); 
            match(input,KW_MOST,FOLLOW_KW_MOST_in_pattern_bnd_resp1597); 
            pushFollow(FOLLOW_num_in_pattern_bnd_resp1599);
            num62=num();

            state._fsp--;

            match(input,KW_TIME,FOLLOW_KW_TIME_in_pattern_bnd_resp1601); 
            match(input,KW_UNITS,FOLLOW_KW_UNITS_in_pattern_bnd_resp1603); 
            dur =num62;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return dur;
    }
    // $ANTLR end "pattern_bnd_resp"


    // $ANTLR start "dec_pattern_bnd_resp"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:433:1: dec_pattern_bnd_resp returns [ srParsePattern result ] : ;
    public final srParsePattern dec_pattern_bnd_resp() throws RecognitionException {
        srParsePattern result = null;

        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:435:2: ()
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:435:4: 
            {
            result =new srParsePattern(); result.setPattern( result.new BndResponsePattern());

            }

        }
        finally {
        }
        return result;
    }
    // $ANTLR end "dec_pattern_bnd_resp"


    // $ANTLR start "pattern_bnd_inv"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:440:1: pattern_bnd_inv returns [ int dur ] : KW_FOR KW_AT KW_LEAST num KW_TIME KW_UNITS ;
    public final int pattern_bnd_inv() throws RecognitionException {
        int dur = 0;

        int num63 = 0;


        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:442:2: ( KW_FOR KW_AT KW_LEAST num KW_TIME KW_UNITS )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:442:68: KW_FOR KW_AT KW_LEAST num KW_TIME KW_UNITS
            {
            match(input,KW_FOR,FOLLOW_KW_FOR_in_pattern_bnd_inv1639); 
            match(input,KW_AT,FOLLOW_KW_AT_in_pattern_bnd_inv1641); 
            match(input,KW_LEAST,FOLLOW_KW_LEAST_in_pattern_bnd_inv1643); 
            pushFollow(FOLLOW_num_in_pattern_bnd_inv1645);
            num63=num();

            state._fsp--;

            match(input,KW_TIME,FOLLOW_KW_TIME_in_pattern_bnd_inv1647); 
            match(input,KW_UNITS,FOLLOW_KW_UNITS_in_pattern_bnd_inv1649); 
            dur =num63;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return dur;
    }
    // $ANTLR end "pattern_bnd_inv"


    // $ANTLR start "dec_pattern_bnd_inv"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:445:1: dec_pattern_bnd_inv returns [ srParsePattern result ] : ;
    public final srParsePattern dec_pattern_bnd_inv() throws RecognitionException {
        srParsePattern result = null;

        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:447:2: ()
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:447:4: 
            {
            result =new srParsePattern(); result.setPattern( result.new BndInvariancePattern());

            }

        }
        finally {
        }
        return result;
    }
    // $ANTLR end "dec_pattern_bnd_inv"


    // $ANTLR start "pattern_inv"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:452:1: pattern_inv : KW_AS KW_WELL ;
    public final void pattern_inv() throws RecognitionException {
        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:453:2: ( KW_AS KW_WELL )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:453:68: KW_AS KW_WELL
            {
            match(input,KW_AS,FOLLOW_KW_AS_in_pattern_inv1683); 
            match(input,KW_WELL,FOLLOW_KW_WELL_in_pattern_inv1685); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "pattern_inv"


    // $ANTLR start "dec_pattern_inv"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:456:1: dec_pattern_inv returns [ srParsePattern result ] : ;
    public final srParsePattern dec_pattern_inv() throws RecognitionException {
        srParsePattern result = null;

        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:458:2: ()
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:458:4: 
            {
            result =new srParsePattern(); result.setPattern( result.new InvariantPattern());

            }

        }
        finally {
        }
        return result;
    }
    // $ANTLR end "dec_pattern_inv"


    // $ANTLR start "pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:462:1: pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for returns [ Vector<CDD> result ] : KW_ONCE qorExp KW_BECOMES KW_SAT ( K )? KW_IT KW_HOLDS KW_FOR ;
    public final Vector<CDD> pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for() throws RecognitionException {
        Vector<CDD> result = null;

        CDD qorExp64 = null;


        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:464:2: ( KW_ONCE qorExp KW_BECOMES KW_SAT ( K )? KW_IT KW_HOLDS KW_FOR )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:464:44: KW_ONCE qorExp KW_BECOMES KW_SAT ( K )? KW_IT KW_HOLDS KW_FOR
            {
            match(input,KW_ONCE,FOLLOW_KW_ONCE_in_pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for1720); 
            pushFollow(FOLLOW_qorExp_in_pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for1722);
            qorExp64=qorExp();

            state._fsp--;

            match(input,KW_BECOMES,FOLLOW_KW_BECOMES_in_pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for1724); 
            match(input,KW_SAT,FOLLOW_KW_SAT_in_pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for1726); 
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:464:77: ( K )?
            int alt28=2;
            int LA28_0 = input.LA(1);

            if ( (LA28_0==K) ) {
                alt28=1;
            }
            switch (alt28) {
                case 1 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:464:77: K
                    {
                    match(input,K,FOLLOW_K_in_pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for1728); 

                    }
                    break;

            }

            match(input,KW_IT,FOLLOW_KW_IT_in_pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for1731); 
            match(input,KW_HOLDS,FOLLOW_KW_HOLDS_in_pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for1733); 
            match(input,KW_FOR,FOLLOW_KW_FOR_in_pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for1735); 
            result =new Vector<CDD>(); result.add(qorExp64);

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return result;
    }
    // $ANTLR end "pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for"


    // $ANTLR start "dec_pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:467:1: dec_pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for returns [ srParsePattern result ] : ( pattern_min_dur dec_pattern_min_dur | pattern_max_dur dec_pattern_max_dur );
    public final srParsePattern dec_pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for() throws RecognitionException {
        srParsePattern result = null;

        srParsePattern dec_pattern_min_dur65 = null;

        int pattern_min_dur66 = 0;

        srParsePattern dec_pattern_max_dur67 = null;

        int pattern_max_dur68 = 0;


        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:469:2: ( pattern_min_dur dec_pattern_min_dur | pattern_max_dur dec_pattern_max_dur )
            int alt29=2;
            int LA29_0 = input.LA(1);

            if ( (LA29_0==KW_AT) ) {
                alt29=1;
            }
            else if ( (LA29_0==KW_LESS) ) {
                alt29=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 29, 0, input);

                throw nvae;
            }
            switch (alt29) {
                case 1 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:469:4: pattern_min_dur dec_pattern_min_dur
                    {
                    pushFollow(FOLLOW_pattern_min_dur_in_dec_pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for1752);
                    pattern_min_dur66=pattern_min_dur();

                    state._fsp--;

                    pushFollow(FOLLOW_dec_pattern_min_dur_in_dec_pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for1754);
                    dec_pattern_min_dur65=dec_pattern_min_dur();

                    state._fsp--;

                    result =dec_pattern_min_dur65; result.setDuration(pattern_min_dur66);

                    }
                    break;
                case 2 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:470:4: pattern_max_dur dec_pattern_max_dur
                    {
                    pushFollow(FOLLOW_pattern_max_dur_in_dec_pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for1762);
                    pattern_max_dur68=pattern_max_dur();

                    state._fsp--;

                    pushFollow(FOLLOW_dec_pattern_max_dur_in_dec_pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for1764);
                    dec_pattern_max_dur67=dec_pattern_max_dur();

                    state._fsp--;

                    result =dec_pattern_max_dur67; result.setDuration(pattern_max_dur68);

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
        return result;
    }
    // $ANTLR end "dec_pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for"


    // $ANTLR start "pattern_min_dur"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:473:1: pattern_min_dur returns [ int dur ] : KW_AT KW_LEAST num KW_TIME KW_UNITS ;
    public final int pattern_min_dur() throws RecognitionException {
        int dur = 0;

        int num69 = 0;


        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:475:2: ( KW_AT KW_LEAST num KW_TIME KW_UNITS )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:475:72: KW_AT KW_LEAST num KW_TIME KW_UNITS
            {
            match(input,KW_AT,FOLLOW_KW_AT_in_pattern_min_dur1783); 
            match(input,KW_LEAST,FOLLOW_KW_LEAST_in_pattern_min_dur1785); 
            pushFollow(FOLLOW_num_in_pattern_min_dur1787);
            num69=num();

            state._fsp--;

            match(input,KW_TIME,FOLLOW_KW_TIME_in_pattern_min_dur1789); 
            match(input,KW_UNITS,FOLLOW_KW_UNITS_in_pattern_min_dur1791); 
            dur =num69;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return dur;
    }
    // $ANTLR end "pattern_min_dur"


    // $ANTLR start "dec_pattern_min_dur"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:478:1: dec_pattern_min_dur returns [ srParsePattern result ] : ;
    public final srParsePattern dec_pattern_min_dur() throws RecognitionException {
        srParsePattern result = null;

        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:480:2: ()
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:480:4: 
            {
            result =new srParsePattern(); result.setPattern( result.new MinDurationPattern());

            }

        }
        finally {
        }
        return result;
    }
    // $ANTLR end "dec_pattern_min_dur"


    // $ANTLR start "pattern_max_dur"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:483:1: pattern_max_dur returns [ int dur ] : KW_LESS KW_THAN num KW_TIME KW_UNITS ;
    public final int pattern_max_dur() throws RecognitionException {
        int dur = 0;

        int num70 = 0;


        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:485:2: ( KW_LESS KW_THAN num KW_TIME KW_UNITS )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:485:72: KW_LESS KW_THAN num KW_TIME KW_UNITS
            {
            match(input,KW_LESS,FOLLOW_KW_LESS_in_pattern_max_dur1824); 
            match(input,KW_THAN,FOLLOW_KW_THAN_in_pattern_max_dur1826); 
            pushFollow(FOLLOW_num_in_pattern_max_dur1828);
            num70=num();

            state._fsp--;

            match(input,KW_TIME,FOLLOW_KW_TIME_in_pattern_max_dur1830); 
            match(input,KW_UNITS,FOLLOW_KW_UNITS_in_pattern_max_dur1832); 
            dur =num70;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return dur;
    }
    // $ANTLR end "pattern_max_dur"


    // $ANTLR start "dec_pattern_max_dur"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:488:1: dec_pattern_max_dur returns [ srParsePattern result ] : ;
    public final srParsePattern dec_pattern_max_dur() throws RecognitionException {
        srParsePattern result = null;

        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:490:2: ()
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:490:4: 
            {
            result =new srParsePattern(); result.setPattern( result.new MaxDurationPattern());

            }

        }
        finally {
        }
        return result;
    }
    // $ANTLR end "dec_pattern_max_dur"


    // $ANTLR start "pattern_bnd_recc"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:493:1: pattern_bnd_recc returns [ int dur ] : KW_AT KW_LEAST KW_EVERY num KW_TIME KW_UNITS ;
    public final int pattern_bnd_recc() throws RecognitionException {
        int dur = 0;

        int num71 = 0;


        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:495:2: ( KW_AT KW_LEAST KW_EVERY num KW_TIME KW_UNITS )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:495:24: KW_AT KW_LEAST KW_EVERY num KW_TIME KW_UNITS
            {
            match(input,KW_AT,FOLLOW_KW_AT_in_pattern_bnd_recc1866); 
            match(input,KW_LEAST,FOLLOW_KW_LEAST_in_pattern_bnd_recc1868); 
            match(input,KW_EVERY,FOLLOW_KW_EVERY_in_pattern_bnd_recc1870); 
            pushFollow(FOLLOW_num_in_pattern_bnd_recc1872);
            num71=num();

            state._fsp--;

            match(input,KW_TIME,FOLLOW_KW_TIME_in_pattern_bnd_recc1874); 
            match(input,KW_UNITS,FOLLOW_KW_UNITS_in_pattern_bnd_recc1876); 
            dur =num71;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return dur;
    }
    // $ANTLR end "pattern_bnd_recc"


    // $ANTLR start "dec_pattern_bnd_recc"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:498:1: dec_pattern_bnd_recc returns [ srParsePattern result ] : ;
    public final srParsePattern dec_pattern_bnd_recc() throws RecognitionException {
        srParsePattern result = null;

        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:500:2: ()
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:500:4: 
            {
            result =new srParsePattern(); result.setPattern( result.new BndReccurrencePattern());

            }

        }
        finally {
        }
        return result;
    }
    // $ANTLR end "dec_pattern_bnd_recc"


    // $ANTLR start "pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:503:1: pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E returns [ Vector<CDD> result ] : KW_IF e1= qorExp KW_HOLDS ( K )? KW_THEN KW_THERE KW_IS KW_AT KW_LEAST KW_ONE KW_EXEC KW_SEQ KW_SUCH KW_THAT e2= qorExp ;
    public final Vector<CDD> pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E() throws RecognitionException {
        Vector<CDD> result = null;

        CDD e1 = null;

        CDD e2 = null;


        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:505:2: ( KW_IF e1= qorExp KW_HOLDS ( K )? KW_THEN KW_THERE KW_IS KW_AT KW_LEAST KW_ONE KW_EXEC KW_SEQ KW_SUCH KW_THAT e2= qorExp )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:505:4: KW_IF e1= qorExp KW_HOLDS ( K )? KW_THEN KW_THERE KW_IS KW_AT KW_LEAST KW_ONE KW_EXEC KW_SEQ KW_SUCH KW_THAT e2= qorExp
            {
            match(input,KW_IF,FOLLOW_KW_IF_in_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E1909); 
            pushFollow(FOLLOW_qorExp_in_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E1913);
            e1=qorExp();

            state._fsp--;

            match(input,KW_HOLDS,FOLLOW_KW_HOLDS_in_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E1915); 
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:505:29: ( K )?
            int alt30=2;
            int LA30_0 = input.LA(1);

            if ( (LA30_0==K) ) {
                alt30=1;
            }
            switch (alt30) {
                case 1 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:505:29: K
                    {
                    match(input,K,FOLLOW_K_in_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E1917); 

                    }
                    break;

            }

            match(input,KW_THEN,FOLLOW_KW_THEN_in_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E1920); 
            match(input,KW_THERE,FOLLOW_KW_THERE_in_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E1922); 
            match(input,KW_IS,FOLLOW_KW_IS_in_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E1924); 
            match(input,KW_AT,FOLLOW_KW_AT_in_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E1926); 
            match(input,KW_LEAST,FOLLOW_KW_LEAST_in_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E1928); 
            match(input,KW_ONE,FOLLOW_KW_ONE_in_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E1930); 
            match(input,KW_EXEC,FOLLOW_KW_EXEC_in_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E1932); 
            match(input,KW_SEQ,FOLLOW_KW_SEQ_in_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E1934); 
            match(input,KW_SUCH,FOLLOW_KW_SUCH_in_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E1936); 
            match(input,KW_THAT,FOLLOW_KW_THAT_in_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E1938); 
            pushFollow(FOLLOW_qorExp_in_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E1942);
            e2=qorExp();

            state._fsp--;

            result =new Vector<CDD>(); result.add(e2);  result.add(e1);

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return result;
    }
    // $ANTLR end "pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E"


    // $ANTLR start "pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E_holds"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:508:1: pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E_holds : KW_HOLDS ;
    public final void pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E_holds() throws RecognitionException {
        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:509:2: ( KW_HOLDS )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:509:76: KW_HOLDS
            {
            match(input,KW_HOLDS,FOLLOW_KW_HOLDS_in_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E_holds1958); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E_holds"


    // $ANTLR start "pattern_possib"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:513:1: pattern_possib : KW_EVENTUALLY KW_HOLDS ;
    public final void pattern_possib() throws RecognitionException {
        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:514:2: ( KW_EVENTUALLY KW_HOLDS )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:514:76: KW_EVENTUALLY KW_HOLDS
            {
            match(input,KW_EVENTUALLY,FOLLOW_KW_EVENTUALLY_in_pattern_possib1974); 
            match(input,KW_HOLDS,FOLLOW_KW_HOLDS_in_pattern_possib1976); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "pattern_possib"


    // $ANTLR start "dec_pattern_possib"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:517:1: dec_pattern_possib returns [ srParsePattern result ] : ;
    public final srParsePattern dec_pattern_possib() throws RecognitionException {
        srParsePattern result = null;

        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:519:2: ()
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:519:4: 
            {
            result =new srParsePattern(); result.setPattern( result.new PossibilityPattern());

            }

        }
        finally {
        }
        return result;
    }
    // $ANTLR end "dec_pattern_possib"


    // $ANTLR start "dec_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:522:1: dec_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E returns [ srParsePattern result ] : ( pattern_possib dec_pattern_possib | pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E_holds dec_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E_holds );
    public final srParsePattern dec_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E() throws RecognitionException {
        srParsePattern result = null;

        srParsePattern dec_pattern_possib72 = null;

        srParsePattern dec_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E_holds73 = null;


        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:524:2: ( pattern_possib dec_pattern_possib | pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E_holds dec_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E_holds )
            int alt31=2;
            int LA31_0 = input.LA(1);

            if ( (LA31_0==KW_EVENTUALLY) ) {
                alt31=1;
            }
            else if ( (LA31_0==KW_HOLDS) ) {
                alt31=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 31, 0, input);

                throw nvae;
            }
            switch (alt31) {
                case 1 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:524:4: pattern_possib dec_pattern_possib
                    {
                    pushFollow(FOLLOW_pattern_possib_in_dec_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E2005);
                    pattern_possib();

                    state._fsp--;

                    pushFollow(FOLLOW_dec_pattern_possib_in_dec_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E2007);
                    dec_pattern_possib72=dec_pattern_possib();

                    state._fsp--;

                    result =dec_pattern_possib72;

                    }
                    break;
                case 2 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:525:4: pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E_holds dec_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E_holds
                    {
                    pushFollow(FOLLOW_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E_holds_in_dec_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E2014);
                    pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E_holds();

                    state._fsp--;

                    pushFollow(FOLLOW_dec_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E_holds_in_dec_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E2016);
                    dec_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E_holds73=dec_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E_holds();

                    state._fsp--;

                    result =dec_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E_holds73;

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
        return result;
    }
    // $ANTLR end "dec_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E"


    // $ANTLR start "pattern_poss_resp"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:529:1: pattern_poss_resp returns [ int dur ] : KW_AFTER KW_AT KW_MOST num KW_TIME KW_UNITS ;
    public final int pattern_poss_resp() throws RecognitionException {
        int dur = 0;

        int num74 = 0;


        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:531:2: ( KW_AFTER KW_AT KW_MOST num KW_TIME KW_UNITS )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:531:82: KW_AFTER KW_AT KW_MOST num KW_TIME KW_UNITS
            {
            match(input,KW_AFTER,FOLLOW_KW_AFTER_in_pattern_poss_resp2039); 
            match(input,KW_AT,FOLLOW_KW_AT_in_pattern_poss_resp2041); 
            match(input,KW_MOST,FOLLOW_KW_MOST_in_pattern_poss_resp2043); 
            pushFollow(FOLLOW_num_in_pattern_poss_resp2045);
            num74=num();

            state._fsp--;

            match(input,KW_TIME,FOLLOW_KW_TIME_in_pattern_poss_resp2047); 
            match(input,KW_UNITS,FOLLOW_KW_UNITS_in_pattern_poss_resp2049); 
            dur =num74;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return dur;
    }
    // $ANTLR end "pattern_poss_resp"


    // $ANTLR start "dec_pattern_poss_resp"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:535:1: dec_pattern_poss_resp returns [ srParsePattern result ] : ;
    public final srParsePattern dec_pattern_poss_resp() throws RecognitionException {
        srParsePattern result = null;

        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:537:2: ()
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:537:4: 
            {
            result =new srParsePattern(); result.setPattern( result.new BndPossResponsePattern());

            }

        }
        finally {
        }
        return result;
    }
    // $ANTLR end "dec_pattern_poss_resp"


    // $ANTLR start "pattern_bnd_poss_inv"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:540:1: pattern_bnd_poss_inv returns [ int dur ] : KW_FOR KW_AT KW_LEAST num KW_TIME KW_UNITS ;
    public final int pattern_bnd_poss_inv() throws RecognitionException {
        int dur = 0;

        int num75 = 0;


        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:542:2: ( KW_FOR KW_AT KW_LEAST num KW_TIME KW_UNITS )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:542:82: KW_FOR KW_AT KW_LEAST num KW_TIME KW_UNITS
            {
            match(input,KW_FOR,FOLLOW_KW_FOR_in_pattern_bnd_poss_inv2084); 
            match(input,KW_AT,FOLLOW_KW_AT_in_pattern_bnd_poss_inv2086); 
            match(input,KW_LEAST,FOLLOW_KW_LEAST_in_pattern_bnd_poss_inv2088); 
            pushFollow(FOLLOW_num_in_pattern_bnd_poss_inv2090);
            num75=num();

            state._fsp--;

            match(input,KW_TIME,FOLLOW_KW_TIME_in_pattern_bnd_poss_inv2092); 
            match(input,KW_UNITS,FOLLOW_KW_UNITS_in_pattern_bnd_poss_inv2094); 
            dur =num75;

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return dur;
    }
    // $ANTLR end "pattern_bnd_poss_inv"


    // $ANTLR start "dec_pattern_bnd_poss_inv"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:546:1: dec_pattern_bnd_poss_inv returns [ srParsePattern result ] : ;
    public final srParsePattern dec_pattern_bnd_poss_inv() throws RecognitionException {
        srParsePattern result = null;

        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:548:2: ()
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:548:4: 
            {
            result =new srParsePattern(); result.setPattern( result.new BndPossInvariancePattern());

            }

        }
        finally {
        }
        return result;
    }
    // $ANTLR end "dec_pattern_bnd_poss_inv"


    // $ANTLR start "dec_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E_holds"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:551:1: dec_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E_holds returns [ srParsePattern result ] : ( pattern_poss_resp dec_pattern_poss_resp | pattern_bnd_poss_inv dec_pattern_bnd_poss_inv );
    public final srParsePattern dec_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E_holds() throws RecognitionException {
        srParsePattern result = null;

        srParsePattern dec_pattern_poss_resp76 = null;

        int pattern_poss_resp77 = 0;

        srParsePattern dec_pattern_bnd_poss_inv78 = null;

        int pattern_bnd_poss_inv79 = 0;


        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:553:2: ( pattern_poss_resp dec_pattern_poss_resp | pattern_bnd_poss_inv dec_pattern_bnd_poss_inv )
            int alt32=2;
            int LA32_0 = input.LA(1);

            if ( (LA32_0==KW_AFTER) ) {
                alt32=1;
            }
            else if ( (LA32_0==KW_FOR) ) {
                alt32=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 32, 0, input);

                throw nvae;
            }
            switch (alt32) {
                case 1 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:553:4: pattern_poss_resp dec_pattern_poss_resp
                    {
                    pushFollow(FOLLOW_pattern_poss_resp_in_dec_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E_holds2127);
                    pattern_poss_resp77=pattern_poss_resp();

                    state._fsp--;

                    pushFollow(FOLLOW_dec_pattern_poss_resp_in_dec_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E_holds2129);
                    dec_pattern_poss_resp76=dec_pattern_poss_resp();

                    state._fsp--;

                    result =dec_pattern_poss_resp76; result.setDuration(pattern_poss_resp77);

                    }
                    break;
                case 2 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:554:4: pattern_bnd_poss_inv dec_pattern_bnd_poss_inv
                    {
                    pushFollow(FOLLOW_pattern_bnd_poss_inv_in_dec_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E_holds2138);
                    pattern_bnd_poss_inv79=pattern_bnd_poss_inv();

                    state._fsp--;

                    pushFollow(FOLLOW_dec_pattern_bnd_poss_inv_in_dec_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E_holds2140);
                    dec_pattern_bnd_poss_inv78=dec_pattern_bnd_poss_inv();

                    state._fsp--;

                    result =dec_pattern_bnd_poss_inv78; result.setDuration(pattern_bnd_poss_inv79);

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
        return result;
    }
    // $ANTLR end "dec_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E_holds"


    // $ANTLR start "pattern"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:559:1: pattern returns [ srParsePattern result ] : ( pat_pref_itis dec_pat_pref_itis | pattern_exists dec_pattern_exists | pattern_BndEx dec_pattern_BndEx | pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E dec_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E );
    public final srParsePattern pattern() throws RecognitionException, ENotDeclaredIdentifier {
        srParsePattern result = null;

        srParsePattern dec_pat_pref_itis80 = null;

        srParsePattern dec_pattern_exists81 = null;

        Vector<CDD> pattern_exists82 = null;

        srParsePattern dec_pattern_BndEx83 = null;

        Vector<CDD> pattern_BndEx84 = null;

        srParsePattern dec_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E85 = null;

        Vector<CDD> pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E86 = null;


        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:561:2: ( pat_pref_itis dec_pat_pref_itis | pattern_exists dec_pattern_exists | pattern_BndEx dec_pattern_BndEx | pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E dec_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E )
            int alt33=4;
            switch ( input.LA(1) ) {
            case KW_IT:
                {
                alt33=1;
                }
                break;
            case QUOTE:
            case NOT_1:
            case KW_NOT:
            case BR_OPEN:
            case ID:
                {
                alt33=2;
                }
                break;
            case KW_TRANS:
                {
                alt33=3;
                }
                break;
            case KW_IF:
                {
                alt33=4;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("", 33, 0, input);

                throw nvae;
            }

            switch (alt33) {
                case 1 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:561:4: pat_pref_itis dec_pat_pref_itis
                    {
                    pushFollow(FOLLOW_pat_pref_itis_in_pattern2161);
                    pat_pref_itis();

                    state._fsp--;

                    pushFollow(FOLLOW_dec_pat_pref_itis_in_pattern2163);
                    dec_pat_pref_itis80=dec_pat_pref_itis();

                    state._fsp--;

                    result =dec_pat_pref_itis80;

                    }
                    break;
                case 2 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:562:4: pattern_exists dec_pattern_exists
                    {
                    pushFollow(FOLLOW_pattern_exists_in_pattern2170);
                    pattern_exists82=pattern_exists();

                    state._fsp--;

                    pushFollow(FOLLOW_dec_pattern_exists_in_pattern2172);
                    dec_pattern_exists81=dec_pattern_exists();

                    state._fsp--;

                    result =dec_pattern_exists81; result.mergeCDDs(pattern_exists82);

                    }
                    break;
                case 3 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:563:4: pattern_BndEx dec_pattern_BndEx
                    {
                    pushFollow(FOLLOW_pattern_BndEx_in_pattern2179);
                    pattern_BndEx84=pattern_BndEx();

                    state._fsp--;

                    pushFollow(FOLLOW_dec_pattern_BndEx_in_pattern2181);
                    dec_pattern_BndEx83=dec_pattern_BndEx();

                    state._fsp--;

                    result =dec_pattern_BndEx83; result.mergeCDDs(pattern_BndEx84);

                    }
                    break;
                case 4 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:564:4: pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E dec_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E
                    {
                    pushFollow(FOLLOW_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E_in_pattern2188);
                    pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E86=pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E();

                    state._fsp--;

                    pushFollow(FOLLOW_dec_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E_in_pattern2190);
                    dec_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E85=dec_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E();

                    state._fsp--;

                    result =dec_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E85; result.mergeCDDs(pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E86);

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
        return result;
    }
    // $ANTLR end "pattern"


    // $ANTLR start "line"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:568:1: line : ( declaration EOL | scopedPattern ( PKT )? EOL | NODECLARE EOL | EOL );
    public final void line() throws RecognitionException, ENotDeclaredIdentifier {
        Vector<CDD> declaration87 = null;

        srParsePattern scopedPattern88 = null;


        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:569:2: ( declaration EOL | scopedPattern ( PKT )? EOL | NODECLARE EOL | EOL )
            int alt35=4;
            switch ( input.LA(1) ) {
            case KW_VAR:
                {
                alt35=1;
                }
                break;
            case SC_GLOBALLY:
            case SC_BEFORE:
            case SC_BETWEEN:
            case SC_AFTER:
                {
                alt35=2;
                }
                break;
            case NODECLARE:
                {
                alt35=3;
                }
                break;
            case EOL:
                {
                alt35=4;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("", 35, 0, input);

                throw nvae;
            }

            switch (alt35) {
                case 1 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:569:4: declaration EOL
                    {
                    pushFollow(FOLLOW_declaration_in_line2205);
                    declaration87=declaration();

                    state._fsp--;

                    match(input,EOL,FOLLOW_EOL_in_line2208); 
                    srParseController.getInstance().addVariables( declaration87 );

                    }
                    break;
                case 2 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:570:4: scopedPattern ( PKT )? EOL
                    {
                    pushFollow(FOLLOW_scopedPattern_in_line2215);
                    scopedPattern88=scopedPattern();

                    state._fsp--;

                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:570:18: ( PKT )?
                    int alt34=2;
                    int LA34_0 = input.LA(1);

                    if ( (LA34_0==PKT) ) {
                        alt34=1;
                    }
                    switch (alt34) {
                        case 1 :
                            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:570:19: PKT
                            {
                            match(input,PKT,FOLLOW_PKT_in_line2218); 

                            }
                            break;

                    }

                    match(input,EOL,FOLLOW_EOL_in_line2223); 
                    srParseController.getInstance().getPatterns().add( scopedPattern88 );

                    }
                    break;
                case 3 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:571:4: NODECLARE EOL
                    {
                    match(input,NODECLARE,FOLLOW_NODECLARE_in_line2230); 
                    match(input,EOL,FOLLOW_EOL_in_line2232); 
                    srParseController.getInstance().setStrictSyntax(false);

                    }
                    break;
                case 4 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:572:4: EOL
                    {
                    match(input,EOL,FOLLOW_EOL_in_line2239); 

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
        return ;
    }
    // $ANTLR end "line"


    // $ANTLR start "lines"
    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:576:1: lines : line ( lines )? ;
    public final void lines() throws RecognitionException, ENotDeclaredIdentifier {
        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:576:7: ( line ( lines )? )
            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:576:9: line ( lines )?
            {
            pushFollow(FOLLOW_line_in_lines2250);
            line();

            state._fsp--;

            // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:576:14: ( lines )?
            int alt36=2;
            int LA36_0 = input.LA(1);

            if ( (LA36_0==SC_GLOBALLY||(LA36_0>=SC_BEFORE && LA36_0<=SC_BETWEEN)||LA36_0==SC_AFTER||LA36_0==KW_VAR||(LA36_0>=EOL && LA36_0<=NODECLARE)) ) {
                alt36=1;
            }
            switch (alt36) {
                case 1 :
                    // C:\\Documents and Settings\\ros7si\\My Documents\\SRbool.g:576:15: lines
                    {
                    pushFollow(FOLLOW_lines_in_lines2253);
                    lines();

                    state._fsp--;


                    }
                    break;

            }


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "lines"

    // Delegated rules


    protected DFA14 dfa14 = new DFA14(this);
    protected DFA15 dfa15 = new DFA15(this);
    static final String DFA14_eotS =
        "\13\uffff";
    static final String DFA14_eofS =
        "\1\uffff\1\4\5\uffff\2\4\2\uffff";
    static final String DFA14_minS =
        "\1\26\1\4\2\26\1\uffff\1\26\1\uffff\2\4\2\uffff";
    static final String DFA14_maxS =
        "\1\26\2\112\1\26\1\uffff\1\31\1\uffff\2\112\2\uffff";
    static final String DFA14_acceptS =
        "\4\uffff\1\1\1\uffff\1\4\2\uffff\1\2\1\3";
    static final String DFA14_specialS =
        "\13\uffff}>";
    static final String[] DFA14_transitionS = {
            "\1\1",
            "\6\4\3\uffff\1\4\1\uffff\1\4\2\uffff\1\4\1\uffff\1\4\1\2\1"+
            "\uffff\1\3\1\5\1\uffff\1\6\1\uffff\2\4\20\uffff\2\4\5\uffff"+
            "\2\4\11\uffff\1\4\11\uffff\1\4",
            "\1\7\63\uffff\1\4",
            "\1\10",
            "",
            "\1\12\2\uffff\1\11",
            "",
            "\6\4\3\uffff\1\4\1\uffff\1\4\2\uffff\1\4\1\uffff\1\4\1\2\1"+
            "\uffff\1\3\1\5\1\uffff\1\6\1\uffff\2\4\20\uffff\2\4\5\uffff"+
            "\2\4\11\uffff\1\4\11\uffff\1\4",
            "\6\4\3\uffff\1\4\1\uffff\1\4\2\uffff\1\4\1\uffff\1\4\1\2\1"+
            "\uffff\1\3\1\5\1\uffff\1\6\1\uffff\2\4\20\uffff\2\4\5\uffff"+
            "\2\4\11\uffff\1\4\11\uffff\1\4",
            "",
            ""
    };

    static final short[] DFA14_eot = DFA.unpackEncodedString(DFA14_eotS);
    static final short[] DFA14_eof = DFA.unpackEncodedString(DFA14_eofS);
    static final char[] DFA14_min = DFA.unpackEncodedStringToUnsignedChars(DFA14_minS);
    static final char[] DFA14_max = DFA.unpackEncodedStringToUnsignedChars(DFA14_maxS);
    static final short[] DFA14_accept = DFA.unpackEncodedString(DFA14_acceptS);
    static final short[] DFA14_special = DFA.unpackEncodedString(DFA14_specialS);
    static final short[][] DFA14_transition;

    static {
        int numStates = DFA14_transitionS.length;
        DFA14_transition = new short[numStates][];
        for (int i=0; i<numStates; i++) {
            DFA14_transition[i] = DFA.unpackEncodedString(DFA14_transitionS[i]);
        }
    }

    class DFA14 extends DFA {

        public DFA14(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 14;
            this.eot = DFA14_eot;
            this.eof = DFA14_eof;
            this.min = DFA14_min;
            this.max = DFA14_max;
            this.accept = DFA14_accept;
            this.special = DFA14_special;
            this.transition = DFA14_transition;
        }
        public String getDescription() {
            return "156:1: var : ( cid | cid OP INT | cid OP cid | cid KW_IN eSet );";
        }
    }
    static final String DFA15_eotS =
        "\54\uffff";
    static final String DFA15_eofS =
        "\54\uffff";
    static final String DFA15_minS =
        "\1\11\1\26\1\11\2\26\1\17\2\26\2\11\2\uffff\4\11\2\26\2\17\1\31"+
        "\2\26\2\11\2\26\5\11\4\17\1\31\1\17\2\26\1\11\3\17";
    static final String DFA15_maxS =
        "\1\11\1\26\1\32\2\26\1\112\1\121\1\31\2\32\2\uffff\1\27\1\31\1"+
        "\11\1\27\2\26\2\122\1\31\2\26\2\27\2\26\1\31\2\11\2\27\4\122\1\31"+
        "\1\122\2\26\1\11\3\122";
    static final String DFA15_acceptS =
        "\12\uffff\1\2\1\1\40\uffff";
    static final String DFA15_specialS =
        "\54\uffff}>";
    static final String[] DFA15_transitionS = {
            "\1\1",
            "\1\2",
            "\1\5\13\uffff\1\3\1\uffff\1\4\1\7\1\uffff\1\6",
            "\1\10",
            "\1\11",
            "\1\12\72\uffff\1\13",
            "\1\14\72\uffff\1\15",
            "\1\17\2\uffff\1\16",
            "\1\5\13\uffff\1\3\1\uffff\1\4\1\7\1\uffff\1\6",
            "\1\5\13\uffff\1\3\1\uffff\1\4\1\7\1\uffff\1\6",
            "",
            "",
            "\1\5\13\uffff\1\20\1\uffff\1\21",
            "\1\24\14\uffff\1\22\2\uffff\1\23",
            "\1\5",
            "\1\5\13\uffff\1\25\1\uffff\1\26",
            "\1\27",
            "\1\30",
            "\1\33\5\uffff\1\31\1\uffff\1\32\72\uffff\1\34",
            "\1\33\102\uffff\1\34",
            "\1\35",
            "\1\36",
            "\1\37",
            "\1\5\13\uffff\1\20\1\uffff\1\21",
            "\1\5\13\uffff\1\20\1\uffff\1\21",
            "\1\40",
            "\1\41",
            "\1\44\14\uffff\1\42\2\uffff\1\43",
            "\1\5",
            "\1\45",
            "\1\5\13\uffff\1\25\1\uffff\1\26",
            "\1\5\13\uffff\1\25\1\uffff\1\26",
            "\1\33\5\uffff\1\31\1\uffff\1\32\72\uffff\1\34",
            "\1\33\5\uffff\1\31\1\uffff\1\32\72\uffff\1\34",
            "\1\33\5\uffff\1\46\1\uffff\1\47\72\uffff\1\34",
            "\1\33\102\uffff\1\34",
            "\1\50",
            "\1\33\102\uffff\1\34",
            "\1\51",
            "\1\52",
            "\1\53",
            "\1\33\5\uffff\1\46\1\uffff\1\47\72\uffff\1\34",
            "\1\33\5\uffff\1\46\1\uffff\1\47\72\uffff\1\34",
            "\1\33\102\uffff\1\34"
    };

    static final short[] DFA15_eot = DFA.unpackEncodedString(DFA15_eotS);
    static final short[] DFA15_eof = DFA.unpackEncodedString(DFA15_eofS);
    static final char[] DFA15_min = DFA.unpackEncodedStringToUnsignedChars(DFA15_minS);
    static final char[] DFA15_max = DFA.unpackEncodedStringToUnsignedChars(DFA15_maxS);
    static final short[] DFA15_accept = DFA.unpackEncodedString(DFA15_acceptS);
    static final short[] DFA15_special = DFA.unpackEncodedString(DFA15_specialS);
    static final short[][] DFA15_transition;

    static {
        int numStates = DFA15_transitionS.length;
        DFA15_transition = new short[numStates][];
        for (int i=0; i<numStates; i++) {
            DFA15_transition[i] = DFA.unpackEncodedString(DFA15_transitionS[i]);
        }
    }

    class DFA15 extends DFA {

        public DFA15(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 15;
            this.eot = DFA15_eot;
            this.eof = DFA15_eof;
            this.min = DFA15_min;
            this.max = DFA15_max;
            this.accept = DFA15_accept;
            this.special = DFA15_special;
            this.transition = DFA15_transition;
        }
        public String getDescription() {
            return "165:1: varlist returns [ Vector<CDD> result ] : ( QUOTE var QUOTE | QUOTE var QUOTE K v= varlist );";
        }
    }
 

    public static final BitSet FOLLOW_lines_in_file19 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_set_in_eAND0 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_set_in_eOR0 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_orExp_in_qorExp78 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_QUOTE_in_qorExp85 = new BitSet(new long[]{0x0000000000401C00L});
    public static final BitSet FOLLOW_orExp_in_qorExp87 = new BitSet(new long[]{0x0000000000000200L});
    public static final BitSet FOLLOW_QUOTE_in_qorExp89 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_andExp_in_orExp108 = new BitSet(new long[]{0x00000000000001C2L});
    public static final BitSet FOLLOW_eOR_in_orExp111 = new BitSet(new long[]{0x0000000000401C00L});
    public static final BitSet FOLLOW_orExp_in_orExp115 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_set_in_eNot0 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_eNot_in_notExp172 = new BitSet(new long[]{0x0000000000401C00L});
    public static final BitSet FOLLOW_eExp_in_notExp174 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_eExp_in_notExp181 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_notExp_in_andExp203 = new BitSet(new long[]{0x0000000000000032L});
    public static final BitSet FOLLOW_eAND_in_andExp206 = new BitSet(new long[]{0x0000000000401C00L});
    public static final BitSet FOLLOW_andExp_in_andExp210 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_var_in_eExp240 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_BR_OPEN_in_eExp265 = new BitSet(new long[]{0x0000000000401C00L});
    public static final BitSet FOLLOW_orExp_in_eExp267 = new BitSet(new long[]{0x0000000000002000L});
    public static final BitSet FOLLOW_BR_CLOSE_in_eExp269 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_orExp_in_qeExp292 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_QUOTE_in_qeExp299 = new BitSet(new long[]{0x0000000000401C00L});
    public static final BitSet FOLLOW_orExp_in_qeExp301 = new BitSet(new long[]{0x0000000000000200L});
    public static final BitSet FOLLOW_QUOTE_in_qeExp303 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_SC_GLOBALLY_in_pScope321 = new BitSet(new long[]{0x0000000000008000L});
    public static final BitSet FOLLOW_K_in_pScope323 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_SC_BEFORE_in_pScope330 = new BitSet(new long[]{0x0000000000401E00L});
    public static final BitSet FOLLOW_qorExp_in_pScope334 = new BitSet(new long[]{0x0000000000008000L});
    public static final BitSet FOLLOW_K_in_pScope336 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_pScopeAfter_in_pScope343 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_SC_BETWEEN_in_pScope351 = new BitSet(new long[]{0x0000000000401E00L});
    public static final BitSet FOLLOW_qorExp_in_pScope355 = new BitSet(new long[]{0x0000000000040000L});
    public static final BitSet FOLLOW_KW_AND_in_pScope357 = new BitSet(new long[]{0x0000000000401E00L});
    public static final BitSet FOLLOW_qorExp_in_pScope361 = new BitSet(new long[]{0x0000000000008000L});
    public static final BitSet FOLLOW_K_in_pScope363 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_SC_AFTER_in_pScopeAfter384 = new BitSet(new long[]{0x0000000000401E00L});
    public static final BitSet FOLLOW_qorExp_in_pScopeAfter388 = new BitSet(new long[]{0x0000000000108000L});
    public static final BitSet FOLLOW_SC_UNTIL_in_pScopeAfter391 = new BitSet(new long[]{0x0000000000401E00L});
    public static final BitSet FOLLOW_qorExp_in_pScopeAfter395 = new BitSet(new long[]{0x0000000000008000L});
    public static final BitSet FOLLOW_K_in_pScopeAfter399 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_PKT_in_epktId413 = new BitSet(new long[]{0x0000000000400000L});
    public static final BitSet FOLLOW_ID_in_epktId415 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_DPKT_in_epktId420 = new BitSet(new long[]{0x0000000000400000L});
    public static final BitSet FOLLOW_ID_in_epktId422 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_ID_in_cid432 = new BitSet(new long[]{0x0000000000A00002L});
    public static final BitSet FOLLOW_epktId_in_cid435 = new BitSet(new long[]{0x0000000000A00002L});
    public static final BitSet FOLLOW_cid_in_eiSet449 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_num_in_eiSet454 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_cid_in_eSet466 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_81_in_eSet471 = new BitSet(new long[]{0x0000000002400200L});
    public static final BitSet FOLLOW_eiSet_in_eSet473 = new BitSet(new long[]{0x0000000000008000L,0x0000000000040000L});
    public static final BitSet FOLLOW_K_in_eSet477 = new BitSet(new long[]{0x0000000002400200L});
    public static final BitSet FOLLOW_eiSet_in_eSet479 = new BitSet(new long[]{0x0000000000008000L,0x0000000000040000L});
    public static final BitSet FOLLOW_82_in_eSet483 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_cid_in_var501 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_cid_in_var509 = new BitSet(new long[]{0x0000000001000000L});
    public static final BitSet FOLLOW_OP_in_var511 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_INT_in_var513 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_cid_in_var520 = new BitSet(new long[]{0x0000000001000000L});
    public static final BitSet FOLLOW_OP_in_var522 = new BitSet(new long[]{0x0000000000400000L});
    public static final BitSet FOLLOW_cid_in_var524 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_cid_in_var530 = new BitSet(new long[]{0x0000000004000000L});
    public static final BitSet FOLLOW_KW_IN_in_var532 = new BitSet(new long[]{0x0000000000400000L,0x0000000000020000L});
    public static final BitSet FOLLOW_eSet_in_var534 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_QUOTE_in_varlist554 = new BitSet(new long[]{0x0000000000400000L});
    public static final BitSet FOLLOW_var_in_varlist556 = new BitSet(new long[]{0x0000000000000200L});
    public static final BitSet FOLLOW_QUOTE_in_varlist558 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_QUOTE_in_varlist565 = new BitSet(new long[]{0x0000000000400000L});
    public static final BitSet FOLLOW_var_in_varlist567 = new BitSet(new long[]{0x0000000000000200L});
    public static final BitSet FOLLOW_QUOTE_in_varlist569 = new BitSet(new long[]{0x0000000000008000L});
    public static final BitSet FOLLOW_K_in_varlist571 = new BitSet(new long[]{0x0000000000000200L});
    public static final BitSet FOLLOW_varlist_in_varlist576 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_KW_VAR_in_declaration596 = new BitSet(new long[]{0x0000000000000200L});
    public static final BitSet FOLLOW_varlist_in_declaration598 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_pScope_in_scopedPattern616 = new BitSet(new long[]{0x0000200140401E00L});
    public static final BitSet FOLLOW_pattern_in_scopedPattern618 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_INT_in_num635 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_QUOTE_in_num644 = new BitSet(new long[]{0x0000000002000000L});
    public static final BitSet FOLLOW_INT_in_num646 = new BitSet(new long[]{0x0000000000000200L});
    public static final BitSet FOLLOW_QUOTE_in_num648 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_qorExp_in_pattern_exists669 = new BitSet(new long[]{0x0000000010000000L});
    public static final BitSet FOLLOW_KW_EVENTUALLY_in_pattern_exists671 = new BitSet(new long[]{0x0000000020000000L});
    public static final BitSet FOLLOW_KW_HOLDS_in_pattern_exists673 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_KW_IT_in_pat_pref_itis703 = new BitSet(new long[]{0x0000000080000000L});
    public static final BitSet FOLLOW_KW_IS_in_pat_pref_itis705 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_KW_TRANS_in_pattern_BndEx721 = new BitSet(new long[]{0x0000000200000000L});
    public static final BitSet FOLLOW_KW_TO_in_pattern_BndEx723 = new BitSet(new long[]{0x0000000400000000L});
    public static final BitSet FOLLOW_KW_STATES_in_pattern_BndEx725 = new BitSet(new long[]{0x0000000004000000L});
    public static final BitSet FOLLOW_KW_IN_in_pattern_BndEx727 = new BitSet(new long[]{0x0000000800000000L});
    public static final BitSet FOLLOW_KW_WHICH_in_pattern_BndEx729 = new BitSet(new long[]{0x0000000000401E00L});
    public static final BitSet FOLLOW_qorExp_in_pattern_BndEx731 = new BitSet(new long[]{0x0000000020000000L});
    public static final BitSet FOLLOW_KW_HOLDS_in_pattern_BndEx733 = new BitSet(new long[]{0x0000001000000000L});
    public static final BitSet FOLLOW_KW_OCCUR_in_pattern_BndEx735 = new BitSet(new long[]{0x0000002000000000L});
    public static final BitSet FOLLOW_KW_AT_in_pattern_BndEx737 = new BitSet(new long[]{0x0000004000000000L});
    public static final BitSet FOLLOW_KW_MOST_in_pattern_BndEx739 = new BitSet(new long[]{0x0000008000000000L});
    public static final BitSet FOLLOW_KW_TWICE_in_pattern_BndEx741 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_pattern_instabs_in_dec_pat_pref_itis771 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_dec_pattern_instabs_in_dec_pat_pref_itis773 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_pat_pref_it_always_in_dec_pat_pref_itis780 = new BitSet(new long[]{0x0000020000000000L});
    public static final BitSet FOLLOW_dec_pat_pref_it_always_in_dec_pat_pref_itis782 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_pat_pref_it_is_always_the_case_that_in_dec_pat_pref_itis789 = new BitSet(new long[]{0x8000200000401E00L});
    public static final BitSet FOLLOW_dec_pat_pref_it_is_always_the_case_that_in_dec_pat_pref_itis791 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_KW_NEVER_in_pattern_instabs814 = new BitSet(new long[]{0x0000020000000000L});
    public static final BitSet FOLLOW_KW_THE_in_pattern_instabs816 = new BitSet(new long[]{0x0000040000000000L});
    public static final BitSet FOLLOW_KW_CASE_in_pattern_instabs818 = new BitSet(new long[]{0x0000080000000000L});
    public static final BitSet FOLLOW_KW_THAT_in_pattern_instabs820 = new BitSet(new long[]{0x0000000000401E00L});
    public static final BitSet FOLLOW_qorExp_in_pattern_instabs822 = new BitSet(new long[]{0x0000000020000000L});
    public static final BitSet FOLLOW_KW_HOLDS_in_pattern_instabs824 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_KW_ALWAYS_in_pat_pref_it_always858 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_pat_pref_it_is_always_the_case_that_in_dec_pat_pref_it_always876 = new BitSet(new long[]{0x8000200000401E00L});
    public static final BitSet FOLLOW_dec_pat_pref_it_is_always_the_case_that_in_dec_pat_pref_it_always878 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_KW_THE_in_pat_pref_it_is_always_the_case_that895 = new BitSet(new long[]{0x0000040000000000L});
    public static final BitSet FOLLOW_KW_CASE_in_pat_pref_it_is_always_the_case_that897 = new BitSet(new long[]{0x0000080000000000L});
    public static final BitSet FOLLOW_KW_THAT_in_pat_pref_it_is_always_the_case_that899 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_pattern_univers_in_dec_pat_pref_it_is_always_the_case_that914 = new BitSet(new long[]{0x0000002000000000L});
    public static final BitSet FOLLOW_dec_pattern_univers_in_dec_pat_pref_it_is_always_the_case_that916 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_pat_pref_it_is_always_the_case_that_if_E_holds_in_dec_pat_pref_it_is_always_the_case_that923 = new BitSet(new long[]{0x0000400000048000L});
    public static final BitSet FOLLOW_dec_pat_pref_it_is_always_the_case_that_if_E_holds_in_dec_pat_pref_it_is_always_the_case_that925 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for_in_dec_pat_pref_it_is_always_the_case_that932 = new BitSet(new long[]{0x0000002000000000L,0x0000000000000004L});
    public static final BitSet FOLLOW_dec_pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for_in_dec_pat_pref_it_is_always_the_case_that934 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_qorExp_in_pattern_univers963 = new BitSet(new long[]{0x0000000020000000L});
    public static final BitSet FOLLOW_KW_HOLDS_in_pattern_univers965 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_pattern_bnd_recc_in_dec_pattern_univers982 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_dec_pattern_bnd_recc_in_dec_pattern_univers984 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_KW_IF_in_pat_pref_it_is_always_the_case_that_if_E_holds1013 = new BitSet(new long[]{0x0000000000401E00L});
    public static final BitSet FOLLOW_qorExp_in_pat_pref_it_is_always_the_case_that_if_E_holds1015 = new BitSet(new long[]{0x0000000020000000L});
    public static final BitSet FOLLOW_KW_HOLDS_in_pat_pref_it_is_always_the_case_that_if_E_holds1017 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_pat_pref_it_is_always_the_case_that_if_E_holds_then_E_in_dec_pat_pref_it_is_always_the_case_that_if_E_holds1038 = new BitSet(new long[]{0x0000800030000000L});
    public static final BitSet FOLLOW_dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E_in_dec_pat_pref_it_is_always_the_case_that_if_E_holds1040 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_pat_pref_it_is_always_the_case_that_if_E_holds_and_is_suc_by_E_then_E_in_dec_pat_pref_it_is_always_the_case_that_if_E_holds1047 = new BitSet(new long[]{0x0000800010000000L});
    public static final BitSet FOLLOW_dec_pat_pref_it_is_always_the_case_that_if_E_holds_and_is_suc_by_E_then_E_in_dec_pat_pref_it_is_always_the_case_that_if_E_holds1049 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_K_in_pat_pref_it_is_always_the_case_that_if_E_holds_then_E1073 = new BitSet(new long[]{0x0000400000000000L});
    public static final BitSet FOLLOW_KW_THEN_in_pat_pref_it_is_always_the_case_that_if_E_holds_then_E1077 = new BitSet(new long[]{0x0000000000401E00L});
    public static final BitSet FOLLOW_qorExp_in_pat_pref_it_is_always_the_case_that_if_E_holds_then_E1079 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_pattern_precedence_in_dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E1096 = new BitSet(new long[]{0x0000000000040000L});
    public static final BitSet FOLLOW_dec_pattern_precedence_in_dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E1098 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_pattern_response_in_dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E1105 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_dec_pattern_response_in_dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E1107 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_pat_pref_it_is_always_the_case_that_if_E_holds_then_E_holds_in_dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E1114 = new BitSet(new long[]{0x2900000000000000L});
    public static final BitSet FOLLOW_dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E_holds_in_dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E1116 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_KW_PREV_in_pattern_precedence1142 = new BitSet(new long[]{0x0001000000000000L});
    public static final BitSet FOLLOW_KW_HELD_in_pattern_precedence1144 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_pattern_pred_chain21_in_dec_pattern_precedence1157 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_dec_pattern_pred_chain21_in_dec_pattern_precedence1159 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_KW_AND_in_pattern_pred_chain211185 = new BitSet(new long[]{0x0002000000000000L});
    public static final BitSet FOLLOW_KW_WAS_in_pattern_pred_chain211187 = new BitSet(new long[]{0x0004000000000000L});
    public static final BitSet FOLLOW_KW_PREC_in_pattern_pred_chain211189 = new BitSet(new long[]{0x0008000000000000L});
    public static final BitSet FOLLOW_KW_BY_in_pattern_pred_chain211191 = new BitSet(new long[]{0x0000000000401E00L});
    public static final BitSet FOLLOW_qorExp_in_pattern_pred_chain211193 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_KW_AND_in_pat_pref_it_is_always_the_case_that_if_E_holds_and_is_suc_by_E_then_E1228 = new BitSet(new long[]{0x0000000080000000L});
    public static final BitSet FOLLOW_KW_IS_in_pat_pref_it_is_always_the_case_that_if_E_holds_and_is_suc_by_E_then_E1230 = new BitSet(new long[]{0x0010000000000000L});
    public static final BitSet FOLLOW_KW_SUCC_in_pat_pref_it_is_always_the_case_that_if_E_holds_and_is_suc_by_E_then_E1232 = new BitSet(new long[]{0x0008000000000000L});
    public static final BitSet FOLLOW_KW_BY_in_pat_pref_it_is_always_the_case_that_if_E_holds_and_is_suc_by_E_then_E1234 = new BitSet(new long[]{0x0000000000401E00L});
    public static final BitSet FOLLOW_qorExp_in_pat_pref_it_is_always_the_case_that_if_E_holds_and_is_suc_by_E_then_E1238 = new BitSet(new long[]{0x0000400000000000L});
    public static final BitSet FOLLOW_KW_THEN_in_pat_pref_it_is_always_the_case_that_if_E_holds_and_is_suc_by_E_then_E1240 = new BitSet(new long[]{0x0000000000401E00L});
    public static final BitSet FOLLOW_qorExp_in_pat_pref_it_is_always_the_case_that_if_E_holds_and_is_suc_by_E_then_E1244 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_pattern_pred_chain12_in_dec_pat_pref_it_is_always_the_case_that_if_E_holds_and_is_suc_by_E_then_E1263 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_dec_pattern_pred_chain12_in_dec_pat_pref_it_is_always_the_case_that_if_E_holds_and_is_suc_by_E_then_E1265 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_pattern_resp_chain21_in_dec_pat_pref_it_is_always_the_case_that_if_E_holds_and_is_suc_by_E_then_E1272 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_dec_pattern_resp_chain21_in_dec_pat_pref_it_is_always_the_case_that_if_E_holds_and_is_suc_by_E_then_E1274 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_KW_PREV_in_pattern_pred_chain121293 = new BitSet(new long[]{0x0001000000000000L});
    public static final BitSet FOLLOW_KW_HELD_in_pattern_pred_chain121295 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_KW_EVENTUALLY_in_pattern_response1325 = new BitSet(new long[]{0x0000000020000000L});
    public static final BitSet FOLLOW_KW_HOLDS_in_pattern_response1327 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_pattern_resp_chain12_in_dec_pattern_responde1357 = new BitSet(new long[]{0x0020000000000000L});
    public static final BitSet FOLLOW_dec_pattern_resp_chain12_in_dec_pattern_responde1359 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_KW_AND_in_pattern_resp_chain121385 = new BitSet(new long[]{0x0000000080000000L});
    public static final BitSet FOLLOW_KW_IS_in_pattern_resp_chain121387 = new BitSet(new long[]{0x0010000000000000L});
    public static final BitSet FOLLOW_KW_SUCC_in_pattern_resp_chain121389 = new BitSet(new long[]{0x0008000000000000L});
    public static final BitSet FOLLOW_KW_BY_in_pattern_resp_chain121391 = new BitSet(new long[]{0x0000000000401E00L});
    public static final BitSet FOLLOW_qorExp_in_pattern_resp_chain121393 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_pattern_constr_chain_in_dec_pattern_resp_chain121413 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_dec_pattern_constr_chain_in_dec_pattern_resp_chain121415 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_KW_WHERE_in_pattern_constr_chain1443 = new BitSet(new long[]{0x0000000000401E00L});
    public static final BitSet FOLLOW_qorExp_in_pattern_constr_chain1447 = new BitSet(new long[]{0x0040000000000000L});
    public static final BitSet FOLLOW_KW_DOES_in_pattern_constr_chain1449 = new BitSet(new long[]{0x0000000000000800L});
    public static final BitSet FOLLOW_KW_NOT_in_pattern_constr_chain1451 = new BitSet(new long[]{0x0080000000000000L});
    public static final BitSet FOLLOW_KW_HOLD_in_pattern_constr_chain1453 = new BitSet(new long[]{0x0000000000020000L});
    public static final BitSet FOLLOW_SC_BETWEEN_in_pattern_constr_chain1455 = new BitSet(new long[]{0x0000000000401C00L});
    public static final BitSet FOLLOW_orExp_in_pattern_constr_chain1459 = new BitSet(new long[]{0x0000000000040000L});
    public static final BitSet FOLLOW_KW_AND_in_pattern_constr_chain1461 = new BitSet(new long[]{0x0000000000401E00L});
    public static final BitSet FOLLOW_qorExp_in_pattern_constr_chain1465 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_KW_EVENTUALLY_in_pattern_resp_chain211503 = new BitSet(new long[]{0x0000000020000000L});
    public static final BitSet FOLLOW_KW_HOLDS_in_pattern_resp_chain211505 = new BitSet(new long[]{0x0100000000000000L});
    public static final BitSet FOLLOW_KW_AFTER_in_pattern_resp_chain211507 = new BitSet(new long[]{0x0000000000401E00L});
    public static final BitSet FOLLOW_qorExp_in_pattern_resp_chain211509 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_KW_HOLDS_in_pat_pref_it_is_always_the_case_that_if_E_holds_then_E_holds1538 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_pattern_bnd_resp_in_dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E_holds1552 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_dec_pattern_bnd_resp_in_dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E_holds1554 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_pattern_bnd_inv_in_dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E_holds1562 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_dec_pattern_bnd_inv_in_dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E_holds1564 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_pattern_inv_in_dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E_holds1571 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_dec_pattern_inv_in_dec_pat_pref_it_is_always_the_case_that_if_E_holds_then_E_holds1573 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_KW_AFTER_in_pattern_bnd_resp1593 = new BitSet(new long[]{0x0000002000000000L});
    public static final BitSet FOLLOW_KW_AT_in_pattern_bnd_resp1595 = new BitSet(new long[]{0x0000004000000000L});
    public static final BitSet FOLLOW_KW_MOST_in_pattern_bnd_resp1597 = new BitSet(new long[]{0x0000000002400200L});
    public static final BitSet FOLLOW_num_in_pattern_bnd_resp1599 = new BitSet(new long[]{0x0200000000000000L});
    public static final BitSet FOLLOW_KW_TIME_in_pattern_bnd_resp1601 = new BitSet(new long[]{0x0400000000000000L});
    public static final BitSet FOLLOW_KW_UNITS_in_pattern_bnd_resp1603 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_KW_FOR_in_pattern_bnd_inv1639 = new BitSet(new long[]{0x0000002000000000L});
    public static final BitSet FOLLOW_KW_AT_in_pattern_bnd_inv1641 = new BitSet(new long[]{0x1000000000000000L});
    public static final BitSet FOLLOW_KW_LEAST_in_pattern_bnd_inv1643 = new BitSet(new long[]{0x0000000002400200L});
    public static final BitSet FOLLOW_num_in_pattern_bnd_inv1645 = new BitSet(new long[]{0x0200000000000000L});
    public static final BitSet FOLLOW_KW_TIME_in_pattern_bnd_inv1647 = new BitSet(new long[]{0x0400000000000000L});
    public static final BitSet FOLLOW_KW_UNITS_in_pattern_bnd_inv1649 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_KW_AS_in_pattern_inv1683 = new BitSet(new long[]{0x4000000000000000L});
    public static final BitSet FOLLOW_KW_WELL_in_pattern_inv1685 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_KW_ONCE_in_pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for1720 = new BitSet(new long[]{0x0000000000401E00L});
    public static final BitSet FOLLOW_qorExp_in_pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for1722 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000001L});
    public static final BitSet FOLLOW_KW_BECOMES_in_pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for1724 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000002L});
    public static final BitSet FOLLOW_KW_SAT_in_pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for1726 = new BitSet(new long[]{0x0000000040008000L});
    public static final BitSet FOLLOW_K_in_pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for1728 = new BitSet(new long[]{0x0000000040000000L});
    public static final BitSet FOLLOW_KW_IT_in_pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for1731 = new BitSet(new long[]{0x0000000020000000L});
    public static final BitSet FOLLOW_KW_HOLDS_in_pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for1733 = new BitSet(new long[]{0x0800000000000000L});
    public static final BitSet FOLLOW_KW_FOR_in_pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for1735 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_pattern_min_dur_in_dec_pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for1752 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_dec_pattern_min_dur_in_dec_pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for1754 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_pattern_max_dur_in_dec_pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for1762 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_dec_pattern_max_dur_in_dec_pat_pref_it_is_always_the_case_that_once_E_bec_sat_it_holds_for1764 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_KW_AT_in_pattern_min_dur1783 = new BitSet(new long[]{0x1000000000000000L});
    public static final BitSet FOLLOW_KW_LEAST_in_pattern_min_dur1785 = new BitSet(new long[]{0x0000000002400200L});
    public static final BitSet FOLLOW_num_in_pattern_min_dur1787 = new BitSet(new long[]{0x0200000000000000L});
    public static final BitSet FOLLOW_KW_TIME_in_pattern_min_dur1789 = new BitSet(new long[]{0x0400000000000000L});
    public static final BitSet FOLLOW_KW_UNITS_in_pattern_min_dur1791 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_KW_LESS_in_pattern_max_dur1824 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000008L});
    public static final BitSet FOLLOW_KW_THAN_in_pattern_max_dur1826 = new BitSet(new long[]{0x0000000002400200L});
    public static final BitSet FOLLOW_num_in_pattern_max_dur1828 = new BitSet(new long[]{0x0200000000000000L});
    public static final BitSet FOLLOW_KW_TIME_in_pattern_max_dur1830 = new BitSet(new long[]{0x0400000000000000L});
    public static final BitSet FOLLOW_KW_UNITS_in_pattern_max_dur1832 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_KW_AT_in_pattern_bnd_recc1866 = new BitSet(new long[]{0x1000000000000000L});
    public static final BitSet FOLLOW_KW_LEAST_in_pattern_bnd_recc1868 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000010L});
    public static final BitSet FOLLOW_KW_EVERY_in_pattern_bnd_recc1870 = new BitSet(new long[]{0x0000000002400200L});
    public static final BitSet FOLLOW_num_in_pattern_bnd_recc1872 = new BitSet(new long[]{0x0200000000000000L});
    public static final BitSet FOLLOW_KW_TIME_in_pattern_bnd_recc1874 = new BitSet(new long[]{0x0400000000000000L});
    public static final BitSet FOLLOW_KW_UNITS_in_pattern_bnd_recc1876 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_KW_IF_in_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E1909 = new BitSet(new long[]{0x0000000000401E00L});
    public static final BitSet FOLLOW_qorExp_in_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E1913 = new BitSet(new long[]{0x0000000020000000L});
    public static final BitSet FOLLOW_KW_HOLDS_in_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E1915 = new BitSet(new long[]{0x0000400000008000L});
    public static final BitSet FOLLOW_K_in_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E1917 = new BitSet(new long[]{0x0000400000000000L});
    public static final BitSet FOLLOW_KW_THEN_in_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E1920 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000020L});
    public static final BitSet FOLLOW_KW_THERE_in_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E1922 = new BitSet(new long[]{0x0000000080000000L});
    public static final BitSet FOLLOW_KW_IS_in_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E1924 = new BitSet(new long[]{0x0000002000000000L});
    public static final BitSet FOLLOW_KW_AT_in_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E1926 = new BitSet(new long[]{0x1000000000000000L});
    public static final BitSet FOLLOW_KW_LEAST_in_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E1928 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000040L});
    public static final BitSet FOLLOW_KW_ONE_in_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E1930 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000080L});
    public static final BitSet FOLLOW_KW_EXEC_in_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E1932 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000100L});
    public static final BitSet FOLLOW_KW_SEQ_in_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E1934 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000200L});
    public static final BitSet FOLLOW_KW_SUCH_in_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E1936 = new BitSet(new long[]{0x0000080000000000L});
    public static final BitSet FOLLOW_KW_THAT_in_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E1938 = new BitSet(new long[]{0x0000000000401E00L});
    public static final BitSet FOLLOW_qorExp_in_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E1942 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_KW_HOLDS_in_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E_holds1958 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_KW_EVENTUALLY_in_pattern_possib1974 = new BitSet(new long[]{0x0000000020000000L});
    public static final BitSet FOLLOW_KW_HOLDS_in_pattern_possib1976 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_pattern_possib_in_dec_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E2005 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_dec_pattern_possib_in_dec_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E2007 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E_holds_in_dec_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E2014 = new BitSet(new long[]{0x0900000000000000L});
    public static final BitSet FOLLOW_dec_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E_holds_in_dec_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E2016 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_KW_AFTER_in_pattern_poss_resp2039 = new BitSet(new long[]{0x0000002000000000L});
    public static final BitSet FOLLOW_KW_AT_in_pattern_poss_resp2041 = new BitSet(new long[]{0x0000004000000000L});
    public static final BitSet FOLLOW_KW_MOST_in_pattern_poss_resp2043 = new BitSet(new long[]{0x0000000002400200L});
    public static final BitSet FOLLOW_num_in_pattern_poss_resp2045 = new BitSet(new long[]{0x0200000000000000L});
    public static final BitSet FOLLOW_KW_TIME_in_pattern_poss_resp2047 = new BitSet(new long[]{0x0400000000000000L});
    public static final BitSet FOLLOW_KW_UNITS_in_pattern_poss_resp2049 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_KW_FOR_in_pattern_bnd_poss_inv2084 = new BitSet(new long[]{0x0000002000000000L});
    public static final BitSet FOLLOW_KW_AT_in_pattern_bnd_poss_inv2086 = new BitSet(new long[]{0x1000000000000000L});
    public static final BitSet FOLLOW_KW_LEAST_in_pattern_bnd_poss_inv2088 = new BitSet(new long[]{0x0000000002400200L});
    public static final BitSet FOLLOW_num_in_pattern_bnd_poss_inv2090 = new BitSet(new long[]{0x0200000000000000L});
    public static final BitSet FOLLOW_KW_TIME_in_pattern_bnd_poss_inv2092 = new BitSet(new long[]{0x0400000000000000L});
    public static final BitSet FOLLOW_KW_UNITS_in_pattern_bnd_poss_inv2094 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_pattern_poss_resp_in_dec_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E_holds2127 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_dec_pattern_poss_resp_in_dec_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E_holds2129 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_pattern_bnd_poss_inv_in_dec_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E_holds2138 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_dec_pattern_bnd_poss_inv_in_dec_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E_holds2140 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_pat_pref_itis_in_pattern2161 = new BitSet(new long[]{0x0000130000000000L});
    public static final BitSet FOLLOW_dec_pat_pref_itis_in_pattern2163 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_pattern_exists_in_pattern2170 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_dec_pattern_exists_in_pattern2172 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_pattern_BndEx_in_pattern2179 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_dec_pattern_BndEx_in_pattern2181 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E_in_pattern2188 = new BitSet(new long[]{0x0000000030000000L});
    public static final BitSet FOLLOW_dec_pat_pref_if_E_holds_then_there_is_at_least_one_exec_seq_such_that_E_in_pattern2190 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_declaration_in_line2205 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000400L});
    public static final BitSet FOLLOW_EOL_in_line2208 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_scopedPattern_in_line2215 = new BitSet(new long[]{0x0000000000200000L,0x0000000000000400L});
    public static final BitSet FOLLOW_PKT_in_line2218 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000400L});
    public static final BitSet FOLLOW_EOL_in_line2223 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_NODECLARE_in_line2230 = new BitSet(new long[]{0x0000000000000000L,0x0000000000000400L});
    public static final BitSet FOLLOW_EOL_in_line2232 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_EOL_in_line2239 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_line_in_lines2250 = new BitSet(new long[]{0x00000000080B4002L,0x0000000000000C00L});
    public static final BitSet FOLLOW_lines_in_lines2253 = new BitSet(new long[]{0x0000000000000002L});

}