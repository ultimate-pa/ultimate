package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.alternating;

import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;

public class TestUnion{

	public static void main(String[] args){
		TestAutomaton_1 automaton1 = new TestAutomaton_1();
		TestAutomaton_2 automaton2 = new TestAutomaton_2();
		AA_Union<String, String> union = new AA_Union<String, String>(automaton1, automaton2);
		try{
			AlternatingAutomaton<String, String> resultAutomaton = union.getResult();
			long startNanoTime = System.nanoTime();
			TestCase.test(resultAutomaton, TestAutomaton_1.TEST_CASES);
			TestCase.test(resultAutomaton, TestAutomaton_2.TEST_CASES);
			System.out.println(((System.nanoTime() - startNanoTime) / 1000000f) + " ms");
		}catch(OperationCanceledException ex){
			ex.printStackTrace();
		}
	}
}
