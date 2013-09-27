package PatternLanguage;

import java.util.regex.Pattern;

public class TestToNuSMV {

	/**
	 * @param args
	 */
	
	static public void testReplace_W_formula(){
		ToNuSMV test = new ToNuSMV();
		test.replace_AW_inCTL("(P & S)", "Z");
	}
	
	static public void testReplace(){
		ToNuSMV test = new ToNuSMV();
		test.transformToSMVSyntax(test.test1);
	}
	
	
	
	public static void main(String[] args) {
		// TODO Auto-generated method stub
		testReplace_W_formula();
		testReplace();
		
		//String testString = "AG(P ! EF S)";
		String testString = "A(((P ! E[(¬R ) U (S ^¬R )]) _	AG(¬R )) W R )";
		ToNuSMV test = new ToNuSMV();
		testString = test.transformToSMVSyntax(testString);
		
		//String testString2 = "& Globally & n.a. & \red$\texttt{AG(\textit{P}} \rightarrow \texttt{EF \textit{S})}$ & \red$\texttt{AG(\textit{P}} \rightarrow \texttt{EF \textit{S})}$";
		//String testString2 = "& After $Q$ & n.a. & \red\texttt{A($\neg$\textit{Q} W (\textit{Q} $\\wedge$ AG (\textit{P} $\rightarrow$ EF(\textit{S}))))}";
		//--> direkt aus Tex ist doof, da der Tex-Text sowieso geändert werden muß (z.B. \wedge z.B. müßte erst per Hand durch \\wedge ersetzt werden, sonst wird das nicht als String erkannt)
		//testString2 = test.transformFromTexToSMVSyntax(testString2);
		
		test.getPossibleResponse_inCTL();
		test.getAbsence_inCTL();
		test.getExistence_inCTL();
		test.getBndExistence_inCTL();
		test.getUniversality_inCTL();
		test.getPrecedence_inCTL();
		test.getResponse_inCTL();
		test.getPrecedenceChain21_inCTL();
		test.getPrecedenceChain12_inCTL();
		test.getResponseChain21_inCTL();
		test.getResponseChain12_inCTL();
		test.getConstrainedChain_inCTL();
		test.getInvariant_inCTL();
		test.getPossBoundedResp_inTCTL();
		test.getPossBoundedInv_inTCTL();
		test.getBoundedInv_inTCTL();
		test.getBoundedResp_inTCTL();
		test.getPeriodic_inTCTL();
		test.getMinDuration_inTCTL();
		test.getMaxDuration_inTCTL();
	}

}
