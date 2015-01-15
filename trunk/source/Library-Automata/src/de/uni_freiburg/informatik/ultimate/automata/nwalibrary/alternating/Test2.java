package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.alternating;

public class Test2{

	public static void main(String[] args){
		TestAutomaton_2 automaton = new TestAutomaton_2();
		long startNanoTime = System.nanoTime();
		TestCase.test(automaton, TestAutomaton_2.TEST_CASES);
		System.out.println(((System.nanoTime() - startNanoTime) / 1000000f) + " ms");
	}
}
