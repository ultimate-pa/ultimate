package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.alternating;

public class Test1{

	public static void main(String[] args){
		TestAutomaton_1 automaton = new TestAutomaton_1();
		long startNanoTime = System.nanoTime();
		TestCase.test(automaton, TestAutomaton_1.TEST_CASES);
		System.out.println(((System.nanoTime() - startNanoTime) / 1000000f) + " ms");
		System.out.println(automaton);
	}
}
