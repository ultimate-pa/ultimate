package PatternLanguage;

import java.util.Vector;
import java.util.regex.Pattern;
import java.util.regex.Matcher;


public class TestPatternLanguage {
	//False
	static String testString1 = "Globally, it is always the case that \"proc1.state = critical\" holds";
	static String testString2 = "Before \"proc1.state = critical\", it is never the case that \"proc1.state = critical\" holds";
	//True
	//AbsentPattern
	static String testString3 = "Globally, it is never the case that \"(proc1.state = critical & proc2.state = critical)\" holds";
	static String testString4 = "Before \"proc1.state = critical\", it is never the case that \"proc1.state = critical & proc2.state = critical\" holds";
	static String testString5 = "After \"proc1.state = idle\", it is never the case that \"proc1.state = initAmi\" holds";
	static String testString6 = "Between \"proc1.state = critical\" and \"proc2.state = critical\", it is never the case that \"proc1.state = initAmi\" holds";
	static String testString7 = "After \"proc1.state = critical\" until \"proc2.state = critical\", it is never the case that \"proc1.state = initAmi\" holds";
	
	//TestUniversalityPattern
	static String testString3U = "Globally, it is always the case that \"!(proc1.state = critical & proc2.state = critical)\" holds";
	static String testString4U = "Before \"proc1.state = idle\", it is always the case that \"proc1.state = initAmi\" holds";
	static String testString5U = "After \"proc1.state = initAmi\", it is always the case that \"(proc1.state = idle | proc1.state = entering | proc1.state = critical | proc1.state = exiting)\" holds";
	static String testString6U = "Between \"proc1.state = initAmi\" and \"proc1.state = idle\", it is always the case that \"proc1.state = initAmi\" holds";
	static String testString7U = "After \"proc1.state = initAmi\" until \"proc1.state = idle\", it is always the case that \"proc1.state = initAmi\" holds";
	
	//Test ExistencePattern
	static String testString3E = "Globally, \"proc1.state = initAmi\" eventually holds";
	static String testString4E = "Before \"proc1.state = idle\", \"proc1.state = initAmi\" eventually holds";
	static String testString5E = "After \"proc1.state = initAmi\", \"(proc1.state = idle | proc1.state = entering | proc1.state = critical | proc1.state = exiting)\" eventually holds";
	static String testString6E = "Between \"proc1.state = initAmi\" and \"proc1.state = critical\", \"proc1.state = idle\" eventually holds";
	static String testString7E = "After \"proc1.state = initAmi\" until \"proc1.state = critical\", \"proc1.state = idle\" eventually holds";
	
	//TestPrecedencePattern
	static String testString3P = "Globally, it is always the case that if \"proc1.state = critical\" holds, then \"proc1.state = critical\" previously held";
	static String testString4P = "Before \"proc1.state = critical\", it is always the case that if \"proc1.state = idle\" holds, then \"proc1.state = initAmi\" previously held";
	static String testString5P = "After \"proc1.state = initAmi\", it is always the case that if \"(proc1.state = entering | proc1.state = critical)\" holds, then \"proc1.state = idle\" previously held";
	static String testString6P = "Between \"proc1.state = initAmi\" and \"proc1.state = idle\", it is always the case that if \"proc1.state = idle\" holds, then \"proc1.state = initAmi\" previously held";
	static String testString7P = "After \"proc1.state = initAmi\" until \"proc1.state = critical\", it is always the case that if \"proc1.state = exiting\" holds, then \"proc1.state = entering\" previously held";
	
	//TestResponsePattern
	static String testString3R = "Globally, it is always the case that if \"proc1.state = entering & semaphore = 1\" holds, then \"proc1.state = critical | proc2.state = critical\" eventually holds";
	static String testString4R = "Before \"proc1.state = exiting\", it is always the case that if \"proc1.state = entering & semaphore = 1\" holds, then \"proc1.state = critical\" eventually holds";
	static String testString5R = "After \"proc1.state = entering\", it is always the case that if \"semaphore = 1\" holds, then \"proc1.state = critical | proc2.state = critical\" eventually holds";
	static String testString6R = "Between \"proc1.state = initAmi\" and \"proc1.state = idle\", it is always the case that if \"proc1.state = init2\" holds, then \"proc1.state = init3\" eventually holds";
	static String testString7R = "After \"proc1.state = initAmi\" until \"proc1.state = idle\", it is always the case that if \"proc1.state = init2\" holds, then \"proc1.state = init3\" eventually holds";
	
	//TestInvariantPattern
	static String testString3I = "Globally, it is always the case that if \"proc1.state = entering\" holds, then \"proc1.state = entering\" holds as well";
	static String testString4I = "Before \"proc1.state = idle\", it is always the case that if \"proc1.state = init2\" holds, then \"proc1.state = init2\" holds as well";
	static String testString5I = "After \"proc1.state = idle\", it is always the case that if \"proc1.state = init2\" holds, then \"proc1.state = init2\" holds as well";
	static String testString6I = "Between \"proc1.state = idle\" and \"proc2.state = idle\", it is always the case that if \"proc1.state = init2\" holds, then \"proc1.state = init2\" holds as well";
	static String testString7I = "After \"proc1.state = idle\" until \"proc2.state = idle\", it is always the case that if \"proc1.state = init2\" holds, then \"proc1.state = init2\" holds as well";
	
	//Test Bounded ResponsePattern
	static String testString3BR = "Globally, it is always the case that if \"proc1.state = entering & semaphore = 1\" holds, then \"proc1.state = critical | proc2.state = critical\" holds after at most \"10\" time units";
	static String testString4BR = "Before \"proc1.state = exiting\", it is always the case that if \"proc1.state = entering & semaphore = 1\" holds, then \"proc1.state = critical\" holds after at most \"10\" time units";
	static String testString5BR = "After \"proc1.state = entering\", it is always the case that if \"semaphore = 1\" holds, then \"proc1.state = critical | proc2.state = critical\" holds after at most \"10\" time units";
	static String testString6BR = "Between \"proc1.state = initAmi\" and \"proc1.state = idle\", it is always the case that if \"proc1.state = init2\" holds, then \"proc1.state = init3\" holds after at most \"10\" time units";
	static String testString7BR = "After \"proc1.state = initAmi\" until \"proc1.state = idle\", it is always the case that if \"proc1.state = init2\" holds, then \"proc1.state = init3\" holds after at most \"10\" time units";
	
	//Test Possible Bounded ResponsePattern
	static String testString3PBR = "Globally, if \"proc1.state = entering & semaphore = 1\" holds, then there is at least one execution sequence such that \"proc1.state = critical | proc2.state = critical\" holds after at most \"10\" time units";
	static String testString4PBR = "Before \"proc1.state = exiting\", if \"proc1.state = entering & semaphore = 1\" holds, then there is at least one execution sequence such that \"proc1.state = critical\" holds after at most \"10\" time units";
	static String testString5PBR = "After \"proc1.state = entering\", if \"semaphore = 1\" holds, then there is at least one execution sequence such that \"proc1.state = critical | proc2.state = critical\" holds after at most \"10\" time units";
	static String testString6PBR = "Between \"proc1.state = initAmi\" and \"proc1.state = idle\", if \"proc1.state = init2\" holds, then there is at least one execution sequence such that \"proc1.state = init3\" holds after at most \"10\" time units";
	static String testString7PBR = "After \"proc1.state = initAmi\" until \"proc1.state = idle\", if \"proc1.state = init2\" holds, then there is at least one execution sequence such that \"proc1.state = init3\" holds after at most \"10\" time units";
	
	//Test Bounded Invariance Pattern
	static String testString3BI = "Globally, it is always the case that if \"proc1.state = entering & semaphore = 1\" holds, then \"proc1.state = critical | proc2.state = critical\" holds for at least \"10\" time units";
	static String testString4BI = "Before \"proc1.state = exiting\", it is always the case that if \"proc1.state = entering & semaphore = 1\" holds, then \"proc1.state = critical\" holds for at least \"10\" time units";
	static String testString5BI = "After \"proc1.state = entering\", it is always the case that if \"semaphore = 1\" holds, then \"proc1.state = critical | proc2.state = critical\" holds for at least \"10\" time units";
	static String testString6BI = "Between \"proc1.state = initAmi\" and \"proc1.state = idle\", it is always the case that if \"proc1.state = init2\" holds, then \"proc1.state = init3\" holds for at least \"10\" time units";
	static String testString7BI = "After \"proc1.state = initAmi\" until \"proc1.state = idle\", it is always the case that if \"proc1.state = init2\" holds, then \"proc1.state = init3\" holds for at least \"10\" time units";
	
	//Test Possible Bounded Invariance Pattern
	static String testString3PBI = "Globally, if \"proc1.state = entering & semaphore = 1\" holds, then there is at least one execution sequence such that \"proc1.state = critical | proc2.state = critical\" holds for at least \"10\" time units";
	static String testString4PBI = "Before \"proc1.state = exiting\", if \"proc1.state = entering & semaphore = 1\" holds, then there is at least one execution sequence such that \"proc1.state = critical\" holds for at least \"10\" time units";
	static String testString5PBI = "After \"proc1.state = entering\", if \"semaphore = 1\" holds, then there is at least one execution sequence such that \"proc1.state = critical | proc2.state = critical\" holds for at least \"10\" time units";
	static String testString6PBI = "Between \"proc1.state = initAmi\" and \"proc1.state = idle\", if \"proc1.state = init2\" holds, then there is at least one execution sequence such that \"proc1.state = init3\" holds for at least \"10\" time units";
	static String testString7PBI = "After \"proc1.state = initAmi\" until \"proc1.state = idle\", if \"proc1.state = init2\" holds, then there is at least one execution sequence such that \"proc1.state = init3\" holds for at least \"10\" time units";
	
	//Test Bounded Recurrence Pattern
	static String testString3BRe = "Globally, it is always the case that \"proc1.state = entering & semaphore = 1\" holds at least every \"10\" time units";
	static String testString4BRe = "Before \"proc1.state = exiting\", it is always the case that \"proc1.state = entering & semaphore = 1\" holds at least every \"10\" time units";
	static String testString5BRe = "After \"proc1.state = entering\", it is always the case that \"semaphore = 1\" holds at least every \"10\" time units";
	static String testString6BRe = "Between \"proc1.state = initAmi\" and \"proc1.state = idle\", it is always the case that \"proc1.state = init2\" holds at least every \"10\" time units";
	static String testString7BRe = "After \"proc1.state = initAmi\" until \"proc1.state = idle\", it is always the case that \"proc1.state = init2\" holds at least every \"10\" time units";
	
	//Test minimum Duration Pattern
	static String testString3MD = "Globally, it is always the case that once \"proc1.state = entering & semaphore = 1\" becomes satisfied, it holds for at least \"10\" time units";
	static String testString4MD = "Before \"proc1.state = exiting\", it is always the case that once \"proc1.state = entering & semaphore = 1\" becomes satisfied, it holds for at least \"10\" time units";
	static String testString5MD = "After \"proc1.state = entering\", it is always the case that once \"semaphore = 1\" becomes satisfied, it holds for at least \"10\" time units";
	static String testString6MD = "Between \"proc1.state = initAmi\" and \"proc1.state = idle\", it is always the case that once \"proc1.state = init2\" becomes satisfied, it holds for at least \"10\" time units";
	static String testString7MD = "After \"proc1.state = initAmi\" until \"proc1.state = idle\", it is always the case that once \"proc1.state = init2\" becomes satisfied, it holds for at least \"10\" time units";
	
	//Test minimum Duration Pattern
	static String testString3MaD = "Globally, it is always the case that once \"proc1.state = entering & semaphore = 1\" becomes satisfied, it holds for less than \"10\" time units";
	static String testString4MaD = "Before \"proc1.state = exiting\", it is always the case that once \"proc1.state = entering & semaphore = 1\" becomes satisfied, it holds for less than \"10\" time units";
	static String testString5MaD = "After \"proc1.state = entering\", it is always the case that once \"semaphore = 1\" becomes satisfied, it holds for less than \"10\" time units";
	static String testString6MaD = "Between \"proc1.state = initAmi\" and \"proc1.state = idle\", it is always the case that once \"proc1.state = init2\" becomes satisfied, it holds for less than \"10\" time units";
	static String testString7MaD = "After \"proc1.state = initAmi\" until \"proc1.state = idle\", it is always the case that once \"proc1.state = init2\" becomes satisfied, it holds for less than \"10\" time units";
	
	static String testString8 = "Globally, \"<S OR S> AND <S> OR <S>\" eventually holds";
	static String testString9 = "Globally, transitions to states in which \"<S OR S> AND <S>\" holds occur at most twice";
	static String testString10 = "Globally, it is always the case that if \"<S>\" holds, then \"<S OR S>\" previously held";
	static String testString11 = "Globally, it is always the case that if \"<S>\" holds and is succeeded by \"<S OR S> AND <S>\", then \"<S OR S>\" previously held";
	static String testString12 = "Globally, it is always the case that if \"<S>\" holds, then \"<S OR S>\" previously held and was preceded by \"<S>\"";
	
	static String testString13 = "Globally, it is always the case that if \"<S>\" holds, then \"<S OR S>\" eventually holds";
	static String testString14 = "Globally, it is always the case that if \"<S>\" holds, then \"<S OR S>\" eventually holds and is succeeded by \"<S>\"";
	static String testString15 = "Globally, it is always the case that if \"<S>\" holds and is succeeded by \"<S OR S>\", then \"<S>\" eventually holds after \"<S>\"";
	static String testString16 = "Globally, it is always the case that if \"<S>\" holds, then \"<S OR S>\" eventually holds and is succeeded by \"<S>\", where \"<S OR S>\" does not hold between \"<S OR S>\" and \"<S OR S>\"";
	
	//quantitative Patterns
	static String testString17 = "Globally, it is always the case that once \"<S>\" becomes satisfied, it holds for at least \"10\" time units";
	static String testString18 = "Globally, it is always the case that once \"<S>\" becomes satisfied, it holds for less than \"10\" time units";
	static String testString19 = "Globally, it is always the case that \"<S>\" holds at least every \"20\" time units";
	static String testString20 = "Globally, it is always the case that if \"<S>\" holds, then \"<S OR S> AND <S> OR <S>\" holds after at most \"20\" time units";
	static String testString21 = "Globally, it is always the case that if \"<S>\" holds, then \"<S OR S> AND <S> OR <S>\" holds for at least \"20\" time units";
	
	//extended Patterns
	static String testString22 = "Globally, if \"<S>\" holds, then there is at least one execution sequence such that \"<S OR S> AND <S> OR <S>\" eventually holds";
	static String testString23 = "Globally, if \"<S>\" holds, then there is at least one execution sequence such that \"<S OR S> AND <S> OR <S>\" holds after at most \"20\" time units";
	static String testString24 = "Globally, if \"<S>\" holds, then there is at least one execution sequence such that \"<S OR S> AND <S> OR <S>\" holds for at least \"20\" time units";
	static String testString25 = "Globally, it is always the case that if \"<S>\" holds, then \"<S OR S> AND <S> OR <S>\" holds as well";
	
	static String testString26 = "Globally, this is no pattern";
	
	
	//(<S>|<S AND S>|<S OR S>)(( AND| OR) (<S>|<S AND S>|<S OR S>))*
	public static void testmatch(String testString){
		   PL_PatternList pattern = new PL_PatternList();
		   Pattern p2 = Pattern.compile("(Globally|Before \"R\"|After \"Q\"|After \"Q\" until \"R\"|Between \"Q\" and \"R\"), it is never the case that \"(<S>|<S AND S>|<S OR S>)(( AND| OR) (<S>|<S AND S>|<S OR S>))*\" holds");
		   //Matcher m = p2.matcher(testString); // get a matcher object
		   System.out.println("The String: __"+testString+"__ matches "+p2.pattern()+": " + Pattern.matches(p2.toString(), testString));
	}
	
	public static void testmatch(String testString, PL_Pattern pattern){
		   //Pattern p2 = pattern.getPattern();
		   //System.out.println("The String: \""+testString+"\" matches "+pattern.getPatternName()+": " + Pattern.matches(p2.toString(), testString));
		   System.out.println("The String: \""+testString+"\" matches "+pattern.getPatternName()+": " + pattern.matchesToPattern(testString));
	}
	
	public static void giveStringArray(String[] stringArray){
		System.out.println("The stringArray contains the following values:");
		for (int i=0; i<stringArray.length; i++){
			System.out.println(stringArray[i]);
		}
	}
	
	public static void giveStringVector(Vector<String> stringArray){
		//System.out.println("The stringArray contains the following values:");
		for (int i=0; i<stringArray.size(); i++){
			System.out.println(stringArray.get(i));
		}
	}
	
	public static void testGetScope(){
		PL_PatternList testPattern = new PL_PatternList();		
		//We expect Globally, Before, After, Between...and, After...until
		System.out.println("Now we test the function getScope");
		System.out.println(testPattern.getScope(testString1));
		System.out.println(testPattern.getScope(testString4));
		System.out.println(testPattern.getScope(testString5));
		System.out.println(testPattern.getScope(testString6));
		System.out.println(testPattern.getScope(testString7));		
	}
	
	public static void testScope(){
		PL_PatternList testPattern = new PL_PatternList();		
		System.out.println("We test the scope definitions with the absentPattern:");
		//Should be all set to true
		testmatch(testString3, testPattern.getAbsentPattern());
		testmatch(testString4, testPattern.getAbsentPattern());
		testmatch(testString5, testPattern.getAbsentPattern());
		testmatch(testString6, testPattern.getAbsentPattern());
		testmatch(testString7, testPattern.getAbsentPattern());	
	}
	
	public static void testPatterns(){
		 PL_PatternList testPattern = new PL_PatternList();
		 
		 PL_Pattern absentPattern 	= testPattern.getAbsentPattern();
		 PL_Pattern univPattern 	= testPattern.getUniversalityPattern();
		 PL_Pattern existPattern 	= testPattern.getBndExistencePattern();
		 PL_Pattern bndExistPattern = testPattern.getBndExistencePattern();
		 PL_Pattern precedencePattern = testPattern.getPrecedencePattern();
		 PL_Pattern precChain12 	= testPattern.getPrecedenceChainPattern12();
		 PL_Pattern precChain21 	= testPattern.getPrecedenceChainPattern21();
		 PL_Pattern resp 			= testPattern.getResponsePattern();
		 PL_Pattern resp12 			= testPattern.getResponseChainPattern12();
		 PL_Pattern resp21 			= testPattern.getResponseChainPattern21();
		 PL_Pattern constr 			= testPattern.getConstrainedChainPattern12();
		 
		 PL_Pattern minDur 			= testPattern.getMinDurationPattern();
		 PL_Pattern maxDur 			= testPattern.getMaxDurationPattern();
		 PL_Pattern recc 			= testPattern.getBoundedRecurrencePattern();
		 PL_Pattern bndResp 		= testPattern.getBoundedResponsePattern();
		 PL_Pattern bndInv 			= testPattern.getBoundedInvariancePattern();
		 
		 PL_Pattern poss 			= testPattern.getPossibilityPattern();
		 PL_Pattern bndPossResp		= testPattern.getPossBndResponsePattern();
		 PL_Pattern bndPossInv		= testPattern.getPossBndInvariancePattern();
		 PL_Pattern invariant		= testPattern.getInvariancePattern();
		 
		 //Test Qualitative Patterns:
		 testmatch(testString3, absentPattern);
		 testmatch(testString1, univPattern);
		 testmatch(testString8, existPattern);
		 testmatch(testString9, bndExistPattern);
		 testmatch(testString10, precedencePattern);
		 testmatch(testString11, precChain12);
		 testmatch(testString12, precChain21);
		 testmatch(testString13, resp);
		 testmatch(testString14, resp12);
		 testmatch(testString15, resp21);
		 testmatch(testString16, constr);
		 //Test Quantitative Patterns:
		 testmatch(testString17, minDur);
		 testmatch(testString18, maxDur);
		 testmatch(testString19, recc);
		 testmatch(testString20, bndResp);
		 testmatch(testString21, bndInv);
		 //Test PossibilityPatterns
		 testmatch(testString22, poss);
		 testmatch(testString23, bndPossResp);
		 testmatch(testString24, bndPossInv);
		 testmatch(testString25, invariant);
		 
		 
	}
	
	public static void testPatternList(){
		 PL_PatternList testPattern = new PL_PatternList();
		 
		 testPattern.splitForTerminals(testString1);
		 //Matches
		 testPattern.findMatchingPattern(testString8);
		 testPattern.findMatchingPattern(testString25);
		 testPattern.findMatchingPattern(testString26);
		 //get nonLiteralTerminals
		 giveStringVector(testPattern.getNonLiteralTerminals(testString1));			
	}
	
	public static void testInitiatedPatterns(String testString){
		PL_initiatedPattern test = new PL_initiatedPattern(testString);
		System.out.println("Test if the initiatedPatterns are determined correctly");
		System.out.println("Test with: "+testString);
		System.out.println("The scope is: "+test.getScope());
		System.out.println("The pattern is: "+test.getPatternClass().getPatternName());
		System.out.println("The nonLiteralTerminales are ");
		giveStringVector(test.getNonLiteralTerminals());
	}
	
	public static void testInitiatedPatterns(){
		testInitiatedPatterns(testString1);
		testInitiatedPatterns(testString3);
		testInitiatedPatterns(testString8);
		testInitiatedPatterns(testString9);
		testInitiatedPatterns(testString10);
	}
	
	public static void testPatternToLTL(String testString){
		 PL_PatternToLTL testToLTL = new PL_PatternToLTL();
		 PL_initiatedPattern test = new PL_initiatedPattern(testString);
		 System.out.println("pattern language requirement: "+testString);
		 System.out.println("in LTL: "+testToLTL.transformAbsentPattern(test));		 
	}
	
	public static void getSpecInLTL(String testString){
		 PL_PatternToLTL testToLTL = new PL_PatternToLTL();
		 PL_initiatedPattern test = new PL_initiatedPattern(testString);
		 //System.out.println("LTLSPEC "+testToLTL.transformAbsentPattern(test));	
		 //System.out.println("LTLSPEC "+testToLTL.transformUniversalityPattern(test));		
		 System.out.println("LTLSPEC "+testToLTL.transformPatternToLTL(test));
	}
	
	public static void getSpecInTCTL(String testString){
		 PL_PatternToLTL testToTCTL = new PL_PatternToLTL();
		 PL_initiatedPattern test = new PL_initiatedPattern(testString);
		 //System.out.println("LTLSPEC "+testToLTL.transformAbsentPattern(test));	
		 //System.out.println("LTLSPEC "+testToLTL.transformUniversalityPattern(test));		
		 System.out.println("SPEC "+testToTCTL.transformPatternToLTL(test));
	}
	
	public static void getSpecInDC(String testString){
		 PL_PatternToLTL testToDC = new PL_PatternToLTL();
		 PL_initiatedPattern test = new PL_initiatedPattern(testString);
		 testToDC.transformPatternToLTL(test);
		 //PEA.dump() wird schon bei transformPatternToLTL aufgerufen
	}
	
	public static void testPatternToLTL(){
		 System.out.println("Test the transformation from PatternLanguage requirements to LTL");
		 testPatternToLTL(testString3);
		 testPatternToLTL(testString4);
		 testPatternToLTL(testString5);
		 testPatternToLTL(testString6);
		 testPatternToLTL(testString7);
	}
	
	public static void getSpecInLTL(){
		 System.out.println("Copy from hereon:");
		 //AbsentPatterns
		 getSpecInLTL(testString3);
		 getSpecInLTL(testString4);
		 getSpecInLTL(testString5);
		 getSpecInLTL(testString6);
		 getSpecInLTL(testString7);
		 //UniversalityPatterns
		 getSpecInLTL(testString3U);
		 getSpecInLTL(testString4U);
		 getSpecInLTL(testString5U);
		 getSpecInLTL(testString6U);
		 getSpecInLTL(testString7U);
		 //ExistencePattern
		 getSpecInLTL(testString3E);
		 getSpecInLTL(testString4E);
		 getSpecInLTL(testString5E);
		 getSpecInLTL(testString6E);
		 getSpecInLTL(testString7E);
		 //PrecedencePattern
		 getSpecInLTL(testString3P);
		 getSpecInLTL(testString4P);
		 getSpecInLTL(testString5P);
		 getSpecInLTL(testString6P);
		 getSpecInLTL(testString7P);
		 //ResponsePattern
		 getSpecInLTL(testString3R);
		 getSpecInLTL(testString4R);
		 getSpecInLTL(testString5R);
		 getSpecInLTL(testString6R);
		 getSpecInLTL(testString7R);
		 //InvariantPattern
		 getSpecInLTL(testString3I);
		 getSpecInLTL(testString4I);
		 getSpecInLTL(testString5I);
		 getSpecInLTL(testString6I);
		 getSpecInLTL(testString7I);
		 
	}
	
	public static void getSpecInTCTL(){
		//PossibleBoundedResponse Pattern
		 getSpecInLTL(testString3PBR);
		 getSpecInLTL(testString4PBR);
		 getSpecInLTL(testString5PBR);
		 getSpecInLTL(testString6PBR);
		 getSpecInLTL(testString7PBR);
		 
		//PossibleBoundedInvariance Pattern
		 getSpecInLTL(testString3PBI);
		 getSpecInLTL(testString4PBI);
		 getSpecInLTL(testString5PBI);
		 getSpecInLTL(testString6PBI);
		 getSpecInLTL(testString7PBI);
		 
		//BoundedInvariance Pattern
		 getSpecInLTL(testString3BI);
		 getSpecInLTL(testString4BI);
		 getSpecInLTL(testString5BI);
		 getSpecInLTL(testString6BI);
		 getSpecInLTL(testString7BI);
		 
		//BoundedResponse Pattern
		 getSpecInLTL(testString3BR);
		 getSpecInLTL(testString4BR);
		 getSpecInLTL(testString5BR);
		 getSpecInLTL(testString6BR);
		 getSpecInLTL(testString7BR);
		 
		//BoundedReccurrence Pattern
		 getSpecInLTL(testString3BRe);
		 getSpecInLTL(testString4BRe);
		 getSpecInLTL(testString5BRe);
		 getSpecInLTL(testString6BRe);
		 getSpecInLTL(testString7BRe);
		 
		//Minimum Duration Pattern
		 getSpecInLTL(testString3MD);
		 getSpecInLTL(testString4MD);
		 getSpecInLTL(testString5MD);
		 getSpecInLTL(testString6MD);
		 getSpecInLTL(testString7MD);
		 
		//Maximum Duration Pattern
		 getSpecInLTL(testString3MaD);
		 getSpecInLTL(testString4MaD);
		 getSpecInLTL(testString5MaD);
		 getSpecInLTL(testString6MaD);
		 getSpecInLTL(testString7MaD);
		 
	}
	
	public static void testResponsePattern(){
		//Check, ob ResponsePattern richtig nach LTL übersetzt wird
		
		//TestResponsePattern
		String testString3Re = "Globally, it is always the case that if \"P\" holds, then \"S\" eventually holds";
		String testString4Re = "Before \"R\", it is always the case that if \"P\" holds, then \"S\" eventually holds";
		String testString5Re = "After \"Q\", it is always the case that if \"P\" holds, then \"S\" eventually holds";
		String testString6Re = "Between \"Q\" and \"R\", it is always the case that if \"P\" holds, then \"S\" eventually holds";
		String testString7Re = "After \"Q\" until \"R\", it is always the case that if \"P\" holds, then \"S\" eventually holds";
		
		System.out.println("Übersetze ResponsePattern nach LTL:");
		getSpecInLTL(testString3Re);
		getSpecInLTL(testString4Re);
		getSpecInLTL(testString5Re);
		getSpecInLTL(testString6Re);
		getSpecInLTL(testString7Re);
		
	}
	
	
	
	public static void testPrecedencePattern(){
		//Check, ob PrecedencePattern richtig nach LTL übersetzt wird
		
		//TestPrecedencePattern
		String testString3 = "Globally, it is always the case that if \"P\" holds, then \"S\" previously held";
		String testString4 = "Before \"R\", it is always the case that if \"P\" holds, then \"S\" previously held";
		String testString5 = "After \"Q\", it is always the case that if \"P\" holds, then \"S\" previously held";
		String testString6 = "Between \"Q\" and \"R\", it is always the case that if \"P\" holds, then \"S\" previously held";
		String testString7 = "After \"Q\" until \"R\", it is always the case that if \"P\" holds, then \"S\" previously held";
				
		System.out.println("Übersetze PrecedencePattern nach LTL:");
		getSpecInLTL(testString3);
		getSpecInLTL(testString4);
		getSpecInLTL(testString5);
		getSpecInLTL(testString6);
		getSpecInLTL(testString7);
		
	}
	
	public static void testInvariantPattern(){
		//Check, ob InvariantPattern richtig nach LTL übersetzt wird
		
		//TestInvariantPattern
		String testString3 = "Globally, it is always the case that if \"P\" holds, then \"S\" holds as well";
		String testString4 = "Before \"R\", it is always the case that if \"P\" holds, then \"S\" holds as well";
		String testString5 = "After \"Q\", it is always the case that if \"P\" holds, then \"S\" holds as well";
		String testString6 = "Between \"Q\" and \"R\", it is always the case that if \"P\" holds, then \"S\" holds as well";
		String testString7 = "After \"Q\" until \"R\", it is always the case that if \"P\" holds, then \"S\" holds as well";
		
		System.out.println("Übersetze InvariantPattern nach LTL:");
		getSpecInLTL(testString3);
		getSpecInLTL(testString4);
		getSpecInLTL(testString5);
		getSpecInLTL(testString6);
		getSpecInLTL(testString7);
		
	}
	
	public static void testBndExistPattern(){
		//Check, ob InvariantPattern richtig nach LTL übersetzt wird
		
		//TestInvariantPattern
		String testString3 = "Globally, transitions to states in which \"P\" holds occur at most twice";
		String testString4 = "Before \"R\", transitions to states in which \"P\" holds occur at most twice";
		String testString5 = "After \"Q\", transitions to states in which \"P\" holds occur at most twice";
		String testString6 = "Between \"Q\" and \"R\", transitions to states in which \"P\" holds occur at most twice";
		String testString7 = "After \"Q\" until \"R\", transitions to states in which \"P\" holds occur at most twice";
		
		System.out.println("Übersetze BoundedExistencePattern nach LTL:");
		getSpecInLTL(testString3);
		getSpecInLTL(testString4);
		getSpecInLTL(testString5);
		getSpecInLTL(testString6);
		getSpecInLTL(testString7);
		
	}
	
	public static void testPrecedenceChain21Pattern(){
		//Check, ob InvariantPattern richtig nach LTL übersetzt wird
		
		//TestPrecedenceChain21Pattern
		String testString3 = "Globally, it is always the case that if \"P\" holds, then \"S\" previously held and was preceded by \"T\"";
		String testString4 = "Before \"R\", it is always the case that if \"P\" holds, then \"S\" previously held and was preceded by \"T\"";
		String testString5 = "After \"Q\", it is always the case that if \"P\" holds, then \"S\" previously held and was preceded by \"T\"";
		String testString6 = "Between \"Q\" and \"R\", it is always the case that if \"P\" holds, then \"S\" previously held and was preceded by \"T\"";
		String testString7 = "After \"Q\" until \"R\", it is always the case that if \"P\" holds, then \"S\" previously held and was preceded by \"T\"";
		
		System.out.println("Übersetze PrecedenceChainPattern2-1 nach LTL:");
		getSpecInLTL(testString3);
		getSpecInLTL(testString4);
		getSpecInLTL(testString5);
		getSpecInLTL(testString6);
		getSpecInLTL(testString7);
		
	}
	
	public static void testPrecedenceChain12Pattern(){
		//Check, ob PrecedenceChain12Pattern richtig nach LTL übersetzt wird
		
		//TestPrecedenceChain12Pattern
		String testString3 = "Globally, it is always the case that if \"S\" holds and is succeeded by \"T\", then \"P\" previously held";
		String testString4 = "Before \"R\", it is always the case that if \"S\" holds and is succeeded by \"T\", then \"P\" previously held";
		String testString5 = "After \"Q\", it is always the case that if \"S\" holds and is succeeded by \"T\", then \"P\" previously held";
		String testString6 = "Between \"Q\" and \"R\", it is always the case that if \"S\" holds and is succeeded by \"T\", then \"P\" previously held";
		String testString7 = "After \"Q\" until \"R\", it is always the case that if \"S\" holds and is succeeded by \"T\", then \"P\" previously held";
		
		System.out.println("Übersetze PrecedenceChainPattern1-2 nach LTL:");
		getSpecInLTL(testString3);
		getSpecInLTL(testString4);
		getSpecInLTL(testString5);
		getSpecInLTL(testString6);
		getSpecInLTL(testString7);
		
	}
	
	public static void testResponseChain21Pattern(){
		//Check, ob PrecedenceChain12Pattern richtig nach LTL übersetzt wird
		
		//TestResponseChain21Pattern
		String testString3 = "Globally, it is always the case that if \"S\" holds and is succeeded by \"T\", then \"P\" eventually holds after \"T\"";
		String testString4 = "Before \"R\", it is always the case that if \"S\" holds and is succeeded by \"T\", then \"P\" eventually holds after \"T\"";
		String testString5 = "After \"Q\", it is always the case that if \"S\" holds and is succeeded by \"T\", then \"P\" eventually holds after \"T\"";
		String testString6 = "Between \"Q\" and \"R\", it is always the case that if \"S\" holds and is succeeded by \"T\", then \"P\" eventually holds after \"T\"";
		String testString7 = "After \"Q\" until \"R\", it is always the case that if \"S\" holds and is succeeded by \"T\", then \"P\" eventually holds after \"T\"";
		
		System.out.println("Übersetze ResponseChainPattern2-1 nach LTL:");
		getSpecInLTL(testString3);
		getSpecInLTL(testString4);
		getSpecInLTL(testString5);
		getSpecInLTL(testString6);
		getSpecInLTL(testString7);
		
	}
	
	public static void testResponseChain12Pattern(){
		//Check, ob ResponseChain12Pattern richtig nach LTL übersetzt wird
		
		//TestResponseChain12Pattern
		String testString3 = "Globally, it is always the case that if \"P\" holds, then \"S\" eventually holds and is succeeded by \"T\"";
		String testString4 = "Before \"R\", it is always the case that if \"P\" holds, then \"S\" eventually holds and is succeeded by \"T\"";
		String testString5 = "After \"Q\", it is always the case that if \"P\" holds, then \"S\" eventually holds and is succeeded by \"T\"";
		String testString6 = "Between \"Q\" and \"R\", it is always the case that if \"P\" holds, then \"S\" eventually holds and is succeeded by \"T\"";
		String testString7 = "After \"Q\" until \"R\", it is always the case that if \"P\" holds, then \"S\" eventually holds and is succeeded by \"T\"";
		
		System.out.println("Übersetze ResponseChain12Pattern nach LTL:");
		getSpecInLTL(testString3);
		getSpecInLTL(testString4);
		getSpecInLTL(testString5);
		getSpecInLTL(testString6);
		getSpecInLTL(testString7);
		
	}
	
	public static void testConstrainedChainPattern(){
		//Check, ob ConstrainedChainPattern richtig nach LTL übersetzt wird
		
		//TestConstrainedChainPattern
		//                  "Globally, it is always the case that if \"(.)*\" holds, then \"(.)*\" eventually holds and is succeeded by \"(.)*\", where \"(.)*\" does not hold between \"(.)*\" and \"(.)*\".") 
		String testString = "Globally, it is always the case that if \"<S>\" holds, then \"<S OR S>\" eventually holds and is succeeded by \"<S>\", where \"<S OR S>\" does not hold between \"<S OR S>\" and \"<S OR S>\"";
		String testString3 = "Globally, it is always the case that if \"P\" holds, then \"S\" eventually holds and is succeeded by \"T\", where \"Z\" does not hold between \"S\" and \"T\"";
		String testString4 = "Before \"R\", it is always the case that if \"P\" holds, then \"S\" eventually holds and is succeeded by \"T\", where \"Z\" does not hold between \"S\" and \"T\"";
		String testString5 = "After \"Q\", it is always the case that if \"P\" holds, then \"S\" eventually holds and is succeeded by \"T\", where \"Z\" does not hold between \"S\" and \"T\"";
		String testString6 = "Between \"Q\" and \"R\", it is always the case that if \"P\" holds, then \"S\" eventually holds and is succeeded by \"T\", where \"Z\" does not hold between \"S\" and \"T\"";
		String testString7 = "After \"Q\" until \"R\", it is always the case that if \"P\" holds, then \"S\" eventually holds and is succeeded by \"T\", where \"Z\" does not hold between \"S\" and \"T\"";
		
		System.out.println("Übersetze ConstrainedChainPattern nach LTL:");
		getSpecInLTL(testString);
		getSpecInLTL(testString3);
		getSpecInLTL(testString4);
		getSpecInLTL(testString5);
		getSpecInLTL(testString6);
		getSpecInLTL(testString7);
		
	}
	
	
	//ICH KANN BEI REGULÄREN AUSDRÜCKEN NICHT AUF KORREKTE KLAMMERUNG FÜR UNENDLICHE AUSDRÜCKE PRÜFEN :(

	/**
	 * @param args
	 */
	public static void main(String[] args) {	
		testPatterns();
		System.out.println("......................................");
		//testScope();
		//System.out.println("......................................");
		//testGetScope(); 
		//System.out.println("......................................");
		//testPatternList();
		//System.out.println("......................................");
		//testInitiatedPatterns();
		System.out.println("......................................");
		//testPatternToLTL();
		//getSpecInLTL();
		
		//Prüfe bei den Pattern, ob richtig übersetzt (mit P,Q,...)
		//testResponsePattern();
		//testPrecedencePattern();
		//testInvariantPattern();
		//testBndExistPattern();
		//testPrecedenceChain21Pattern();
		//testPrecedenceChain12Pattern();
		//testResponseChain21Pattern();
		//testResponseChain12Pattern();
		//testConstrainedChainPattern();
		
		//Prüfe TCTL Patterns
		//getSpecInTCTL();
		//getSpecInDC(testString3);
		
		
	}

}
