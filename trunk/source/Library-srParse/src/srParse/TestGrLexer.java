// $ANTLR 3.2 Sep 23, 2009 12:02:23 C:\\Documents and Settings\\ros7si\\My Documents\\Workspace_komplett\\REFramework\\src\\srParse\\TestGr.g 2010-07-27 18:20:48
package srParse;

import org.antlr.runtime.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;

public class TestGrLexer extends Lexer {
    public static final int AND=4;
    public static final int EOF=-1;

    // delegates
    // delegators

    public TestGrLexer() {;} 
    public TestGrLexer(CharStream input) {
        this(input, new RecognizerSharedState());
    }
    public TestGrLexer(CharStream input, RecognizerSharedState state) {
        super(input,state);

    }
    public String getGrammarFileName() { return "C:\\Documents and Settings\\ros7si\\My Documents\\Workspace_komplett\\REFramework\\src\\srParse\\TestGr.g"; }

    // $ANTLR start "AND"
    public final void mAND() throws RecognitionException {
        try {
            int _type = AND;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // C:\\Documents and Settings\\ros7si\\My Documents\\Workspace_komplett\\REFramework\\src\\srParse\\TestGr.g:11:5: ( 'and' )
            // C:\\Documents and Settings\\ros7si\\My Documents\\Workspace_komplett\\REFramework\\src\\srParse\\TestGr.g:11:7: 'and'
            {
            match("and"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "AND"

    public void mTokens() throws RecognitionException {
        // C:\\Documents and Settings\\ros7si\\My Documents\\Workspace_komplett\\REFramework\\src\\srParse\\TestGr.g:1:8: ( AND )
        // C:\\Documents and Settings\\ros7si\\My Documents\\Workspace_komplett\\REFramework\\src\\srParse\\TestGr.g:1:10: AND
        {
        mAND(); 

        }


    }


 

}