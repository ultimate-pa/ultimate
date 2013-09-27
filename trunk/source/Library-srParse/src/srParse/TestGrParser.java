// $ANTLR 3.2 Sep 23, 2009 12:02:23 C:\\Documents and Settings\\ros7si\\My Documents\\Workspace_komplett\\REFramework\\src\\srParse\\TestGr.g 2010-07-27 18:20:48

package srParse;


import org.antlr.runtime.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;

import org.antlr.runtime.debug.*;
import java.io.IOException;
public class TestGrParser extends DebugParser {
    public static final String[] tokenNames = new String[] {
        "<invalid>", "<EOR>", "<DOWN>", "<UP>", "AND"
    };
    public static final int AND=4;
    public static final int EOF=-1;

    // delegates
    // delegators

    public static final String[] ruleNames = new String[] {
        "invalidRule", "rule"
    };
     
        public int ruleLevel = 0;
        public int getRuleLevel() { return ruleLevel; }
        public void incRuleLevel() { ruleLevel++; }
        public void decRuleLevel() { ruleLevel--; }
        public TestGrParser(TokenStream input) {
            this(input, DebugEventSocketProxy.DEFAULT_DEBUGGER_PORT, new RecognizerSharedState());
        }
        public TestGrParser(TokenStream input, int port, RecognizerSharedState state) {
            super(input, state);
            DebugEventSocketProxy proxy =
                new DebugEventSocketProxy(this, port, null);
            setDebugListener(proxy);
            try {
                proxy.handshake();
            }
            catch (IOException ioe) {
                reportError(ioe);
            }
        }
    public TestGrParser(TokenStream input, DebugEventListener dbg) {
        super(input, dbg, new RecognizerSharedState());

    }
    protected boolean evalPredicate(boolean result, String predicate) {
        dbg.semanticPredicate(result, predicate);
        return result;
    }


    public String[] getTokenNames() { return TestGrParser.tokenNames; }
    public String getGrammarFileName() { return "C:\\Documents and Settings\\ros7si\\My Documents\\Workspace_komplett\\REFramework\\src\\srParse\\TestGr.g"; }



    // $ANTLR start "rule"
    // C:\\Documents and Settings\\ros7si\\My Documents\\Workspace_komplett\\REFramework\\src\\srParse\\TestGr.g:8:1: rule : AND ;
    public final void rule() throws RecognitionException {
        try { dbg.enterRule(getGrammarFileName(), "rule");
        if ( getRuleLevel()==0 ) {dbg.commence();}
        incRuleLevel();
        dbg.location(8, 1);

        try {
            // C:\\Documents and Settings\\ros7si\\My Documents\\Workspace_komplett\\REFramework\\src\\srParse\\TestGr.g:8:6: ( AND )
            dbg.enterAlt(1);

            // C:\\Documents and Settings\\ros7si\\My Documents\\Workspace_komplett\\REFramework\\src\\srParse\\TestGr.g:8:8: AND
            {
            dbg.location(8,8);
            match(input,AND,FOLLOW_AND_in_rule16); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        dbg.location(9, 2);

        }
        finally {
            dbg.exitRule(getGrammarFileName(), "rule");
            decRuleLevel();
            if ( getRuleLevel()==0 ) {dbg.terminate();}
        }

        return ;
    }
    // $ANTLR end "rule"

    // Delegated rules


 

    public static final BitSet FOLLOW_AND_in_rule16 = new BitSet(new long[]{0x0000000000000002L});

}