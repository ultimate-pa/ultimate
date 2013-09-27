package PatternLanguage;

/**
* The class <code>TestPL_Pattern2Logic</code> provides tests for <code>PL_Pattern2Logic</code>
*/

public class TestPL_Pattern2Logic {
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
	static String testString6P = "Between \"proc1.state = initAmi\" and \"proc1.state = idle\", it is always the case that if \"proc1.state = idle\" holds, then \"proc1.state = critical\" previously held";
	static String testString7P = "After \"proc1.state = initAmi\" until \"proc1.state = critical\", it is always the case that if \"proc1.state = exiting\" holds, then \"proc1.state = entering\" previously held";
	
	//TestResponsePattern
	static String testString3R = "Globally, it is always the case that if \"proc1.state = entering & semaphore = 1\" holds, then \"proc1.state = critical | proc2.state = critical\" eventually holds";
	static String testString4R = "Before \"proc1.state = exiting\", it is always the case that if \"proc1.state = entering & semaphore = 1\" holds, then \"proc1.state = critical\" eventually holds";
	static String testString5R = "After \"proc1.state = entering\", it is always the case that if \"semaphore = 1\" holds, then \"proc1.state = critical | proc2.state = critical\" eventually holds";
	static String testString6R = "Between \"proc1.state = initAmi\" and \"proc1.state = idle\", it is always the case that if \"proc1.state = init2\" holds, then \"proc1.state = init3\" eventually holds";
	static String testString7R = "After \"proc1.state = initAmi\" until \"proc1.state = idle\", it is always the case that if \"proc1.state = init2\" holds, then \"proc1.state = init3\" eventually holds";
	
	//TestInvariantPattern
	static String testString3I = "Globally, it is always the case that if \"proc1.state = entering\" holds, then \"proc1.state = critical\" holds as well";
	static String testString4I = "Before \"proc1.state = idle\", it is always the case that if \"proc1.state = init2\" holds, then \"proc1.state = critical\" holds as well";
	static String testString5I = "After \"proc1.state = idle\", it is always the case that if \"proc1.state = init2\" holds, then \"proc1.state = critical\" holds as well";
	static String testString6I = "Between \"proc1.state = idle\" and \"proc2.state = idle\", it is always the case that if \"proc1.state = init2\" holds, then \"proc1.state = critical\" holds as well";
	static String testString7I = "After \"proc1.state = idle\" until \"proc2.state = idle\", it is always the case that if \"proc1.state = init2\" holds, then \"proc1.state = critical\" holds as well";
	
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
	static String testString3MD = "Globally, it is always the case that once \"proc1.state = entering\" becomes satisfied, it holds for at least \"10\" time units";
	static String testString4MD = "Before \"proc1.state = exiting\", it is always the case that once \"proc1.state = entering\" becomes satisfied, it holds for at least \"10\" time units";
	static String testString5MD = "After \"proc1.state = entering\", it is always the case that once \"semaphore = 1\" becomes satisfied, it holds for at least \"10\" time units";
	static String testString6MD = "Between \"proc1.state = initAmi\" and \"proc1.state = idle\", it is always the case that once \"proc1.state = init2\" becomes satisfied, it holds for at least \"10\" time units";
	static String testString7MD = "After \"proc1.state = initAmi\" until \"proc1.state = idle\", it is always the case that once \"proc1.state = init2\" becomes satisfied, it holds for at least \"10\" time units";
	
	//Test maximum Duration Pattern
	static String testString3MaD = "Globally, it is always the case that once \"proc1.state = entering & semaphore = 1\" becomes satisfied, it holds for less than \"10\" time units";
	static String testString4MaD = "Before \"proc1.state = exiting\", it is always the case that once \"proc1.state = entering & semaphore = 1\" becomes satisfied, it holds for less than \"10\" time units";
	static String testString5MaD = "After \"proc1.state = entering\", it is always the case that once \"semaphore = 1\" becomes satisfied, it holds for less than \"10\" time units";
	static String testString6MaD = "Between \"proc1.state = initAmi\" and \"proc1.state = idle\", it is always the case that once \"proc1.state = init2\" becomes satisfied, it holds for less than \"10\" time units";
	static String testString7MaD = "After \"proc1.state = initAmi\" until \"proc1.state = idle\", it is always the case that once \"proc1.state = init2\" becomes satisfied, it holds for less than \"10\" time units";
	
	//Test BoundedExistence
	static String testString9B = "Globally, transitions to states in which \"<S OR S> AND <S>\" holds occur at most twice";
	static String testString10B = "Before \"proc1.state = exiting\", transitions to states in which \"<S OR S> AND <S>\" holds occur at most twice";
	static String testString11B = "After \"proc1.state = entering\", transitions to states in which \"<S OR S> AND <S>\" holds occur at most twice";
	static String testString12B = "Between \"proc1.state = initAmi\" and \"proc1.state = idle\", transitions to states in which \"<S OR S> AND <S>\" holds occur at most twice";
	static String testString13B = "After \"proc1.state = initAmi\" until \"proc1.state = idle\", transitions to states in which \"<S OR S> AND <S>\" holds occur at most twice";
	
	//Test PrecedenceChainPattern 21
	static String testString3PC = "Globally, it is always the case that if \"<P>\" holds, then \"<S>\" previously held and was preceded by \"<T>\"";
	static String testString4PC = "Before \"R\", it is always the case that if \"<P>\" holds, then \"<S>\" previously held and was preceded by \"<T>\"";
	static String testString5PC = "After \"Q\", it is always the case that if \"<P>\" holds, then \"<S>\" previously held and was preceded by \"<T>\"";
	static String testString6PC = "Between \"Q\" and \"R\", it is always the case that if \"<P>\" holds, then \"<S>\" previously held and was preceded by \"<T>\"";
	static String testString7PC = "After \"proc1.state = initAmi\" until \"proc1.state = idle\", it is always the case that if \"<P>\" holds, then \"<S>\" previously held and was preceded by \"<T>\"";
	
	//Test PrecedenceChainPattern 12
	static String testString3PC12 = "Globally, it is always the case that if \"S\" holds and is succeeded by \"T\", then \"P\" previously held";
	static String testString4PC12 = "Before \"R\", it is always the case that if \"S\" holds and is succeeded by \"T\", then \"P\" previously held";
	static String testString5PC12 = "After \"Q\", it is always the case that if \"S\" holds and is succeeded by \"T\", then \"P\" previously held";
	static String testString6PC12 = "Between \"Q\" and \"R\", it is always the case that if \"S\" holds and is succeeded by \"T\", then \"P\" previously held";
	static String testString7PC12 = "After \"proc1.state = initAmi\" until \"proc1.state = idle\", it is always the case that if \"S\" holds and is succeeded by \"T\", then \"P\" previously held";
	
	//Test ResponseChainPattern21
	static String testString3RC = "Globally, it is always the case that if \"S\" holds and is succeeded by \"T\", then \"P\" eventually holds after \"T\"";
	static String testString4RC = "Before \"R\", it is always the case that if \"S\" holds and is succeeded by \"T\", then \"P\" eventually holds after \"T\"";
	static String testString5RC = "After \"Q\", it is always the case that if \"S\" holds and is succeeded by \"T\", then \"P\" eventually holds after \"T\"";
	static String testString6RC = "Between \"Q\" and \"R\", it is always the case that if \"S\" holds and is succeeded by \"T\", then \"P\" eventually holds after \"T\"";
	static String testString7RC = "After \"proc1.state = initAmi\" until \"proc1.state = idle\", it is always the case that if \"S\" holds and is succeeded by \"T\", then \"P\" eventually holds after \"T\"";
	
	//Test ResponseChainPattern 12
	static String testString3RC2 = "Globally, it is always the case that if \"P\" holds, then \"S\" eventually holds and is succeeded by \"T\"";
	static String testString4RC2 = "Before \"R\", it is always the case that if \"P\" holds, then \"S\" eventually holds and is succeeded by \"T\"";
	static String testString5RC2 = "After \"Q\", it is always the case that if \"P\" holds, then \"S\" eventually holds and is succeeded by \"T\"";
	static String testString6RC2 = "Between \"Q\" and \"R\", it is always the case that if \"P\" holds, then \"S\" eventually holds and is succeeded by \"T\"";
	static String testString7RC2 = "After \"proc1.state = initAmi\" until \"proc1.state = idle\", it is always the case that if \"P\" holds, then \"S\" eventually holds and is succeeded by \"T\"";
	
	//constrained chain pattern
	static String testString16 = "Globally, it is always the case that if \"<S>\" holds, then \"<S OR S>\" eventually holds and is succeeded by \"<S>\", where \"<S OR S>\" does not hold between \"<S OR S>\" and \"<S OR S>\"";
	
		
	//extended Possibility Patterns
	static String testString22 = "Globally, if \"<S>\" holds, then there is at least one execution sequence such that \"<S OR S> AND <S> OR <S>\" eventually holds";
	static String testString23 = "Globally, if \"<S>\" holds, then there is at least one execution sequence such that \"<S OR S> AND <S> OR <S>\" holds after at most \"20\" time units";
	static String testString24 = "Globally, if \"<S>\" holds, then there is at least one execution sequence such that \"<S OR S> AND <S> OR <S>\" holds for at least \"20\" time units";
	
	
	static String testString26 = "Globally, this is no pattern";
	/**
	 * @param args
	 */
	
	private static void testPattern4allScopes(String t1, String t2, String t3, String t4, String t5, String requestedLogic){
		System.out.println("Übersetze nach "+ requestedLogic);
		
		PL_Pattern2Logic toLogicTransformator = new PL_Pattern2Logic();
		
		//Teststrings mit instanziierten Versionen des AbsencePatterns jeweils pro Scope
		PL_initiatedPattern test1 = new PL_initiatedPattern(t1);
		PL_initiatedPattern test2 = new PL_initiatedPattern(t2);
		PL_initiatedPattern test3 = new PL_initiatedPattern(t3);
		PL_initiatedPattern test4 = new PL_initiatedPattern(t4);
		PL_initiatedPattern test5 = new PL_initiatedPattern(t5);
		
		System.out.println(toLogicTransformator.transformPatternToLogic(test1, requestedLogic));
		System.out.println(toLogicTransformator.transformPatternToLogic(test2, requestedLogic));
		System.out.println(toLogicTransformator.transformPatternToLogic(test3, requestedLogic));
		System.out.println(toLogicTransformator.transformPatternToLogic(test4, requestedLogic));
		System.out.println(toLogicTransformator.transformPatternToLogic(test5, requestedLogic));
		
	}
	
	private static void testPattern(String t1, String requestedLogic){
		System.out.println("Übersetze nach "+ requestedLogic);
		
		PL_Pattern2Logic toLogicTransformator = new PL_Pattern2Logic();
		
		//Teststrings mit instanziierten Versionen des AbsencePatterns jeweils pro Scope
		PL_initiatedPattern test1 = new PL_initiatedPattern(t1);		
		System.out.println(toLogicTransformator.transformPatternToLogic(test1, requestedLogic));
		
	}
	
	public static void testAbsencePattern(String requestedLogic){
		//Check, ob ResponsePattern richtig nach LTL/CTL/DC/TCTL übersetzt wird
				
		System.out.println("Test AbsencePattern");
		testPattern4allScopes(testString3, testString4, testString5, testString6, testString7, requestedLogic);				
	}
	
	public static void testUniversalityPattern(String requestedLogic){
		System.out.println("Test UniversalityPattern");
		testPattern4allScopes(testString3U, testString4U, testString5U, testString6U, testString7U, requestedLogic);	
				
	}
	
	public static void testExistencePattern(String requestedLogic){
		System.out.println("Test ExistencePattern");
		testPattern4allScopes(testString3E, testString4E, testString5E, testString6E, testString7E, requestedLogic);	
				
	}
	
	public static void testPrecedencePattern(String requestedLogic){
		System.out.println("Test PrecedencePattern");
		testPattern4allScopes(testString3P, testString4P, testString5P, testString6P, testString7P, requestedLogic);	
				
	}
	
	public static void testBoundedExistencePattern(String requestedLogic){
		System.out.println("Test BoundedExistencePattern");
		testPattern4allScopes(testString9B, testString10B, testString11B, testString12B, testString13B, requestedLogic);	
				
	}
	
	public static void testBoundedInvariancePattern(String requestedLogic){
		System.out.println("Test BoundedInvariancePattern");
		testPattern4allScopes(testString3BI, testString4BI, testString5BI, testString6BI, testString7BI, requestedLogic);
				
	}
	
	public static void testBoundedRecurrencePattern(String requestedLogic){
		System.out.println("Test BoundedRecurrencePattern");
		testPattern4allScopes(testString3BRe, testString4BRe, testString5BRe, testString6BRe, testString7BRe, requestedLogic);
				
	}
	
	public static void testBoundedResponsePattern(String requestedLogic){
		System.out.println("Test BoundedResponsePattern");
		testPattern4allScopes(testString3BR, testString4BR, testString5BR, testString6BR, testString7BR, requestedLogic);
				
	}
	
	public static void testResponsePattern(String requestedLogic){
		System.out.println("Test ResponsePattern");
		testPattern4allScopes(testString3R, testString4R, testString5R, testString6R, testString7R, requestedLogic);
				
	}
	
	public static void testInvariantPattern(String requestedLogic){
		System.out.println("Test InvariantPattern");
		testPattern4allScopes(testString3I, testString4I, testString5I, testString6I, testString7I, requestedLogic);
				
	}
	
	public static void testPrecedenceChain21(String requestedLogic){
		System.out.println("Test Precedence Chain 21 Pattern");
		testPattern4allScopes(testString3PC, testString4PC, testString5PC, testString6PC, testString7PC, requestedLogic);
				
	}
	
	public static void testPrecedenceChain12(String requestedLogic){
		System.out.println("Test Precedence Chain 12 Pattern");
		testPattern4allScopes(testString3PC12, testString4PC12, testString5PC12, testString6PC12, testString7PC12, requestedLogic);
				
	}
	
	public static void testResponseChain21(String requestedLogic){
		System.out.println("Test Response Chain 21 Pattern");
		testPattern4allScopes(testString3RC, testString4RC, testString5RC, testString6RC, testString7RC, requestedLogic);
				
	}
	
	public static void testResponseChain12(String requestedLogic){
		System.out.println("Test Response Chain 12 Pattern");
		testPattern4allScopes(testString3RC2, testString4RC2, testString5RC2, testString6RC2, testString7RC2, requestedLogic);
				
	}
	
	public static void testMaximumDurationPattern(String requestedLogic){
		System.out.println("Test Minimum Duration Pattern");
		testPattern4allScopes(testString3MaD, testString4MaD, testString5MaD, testString6MaD, testString7MaD, requestedLogic);
				
	}
	
	public static void testMinimumDurationPattern(String requestedLogic){
		System.out.println("Test Minimum Duration Pattern");
		testPattern4allScopes(testString3MD, testString4MD, testString5MD, testString6MD, testString7MD, requestedLogic);
				
	}
	
	public static void main(String[] args) {
		//testAbsencePattern("DC");
		//testUniversalityPattern("DC");
		//testExistencePattern("DC");
		//testBoundedExistencePattern("DC");
		//testPrecedencePattern("DC");
		//testPrecedenceChain21("DC");
		//testPrecedenceChain12("DC");
		//testResponsePattern("DC");
		//testResponseChain21("DC");
		//testResponseChain12("DC");
		
		testMinimumDurationPattern("DC");
		//testMaximumDurationPattern("DC");
		//testBoundedRecurrencePattern("DC");
		//testBoundedResponsePattern("DC");
		//testBoundedInvariancePattern("DC");		
		
		//testInvariantPattern("DC");
		
		
		//Bisher noch nicht umgesetzt da die entsprechenden Übersetzungen nach DC fehlen
		//ConstrainedChainPattern 
		//Possible bounded invariance
		//Possible bounded response
		//possible response

	}

}
