package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.alternating;

import de.uni_freiburg.informatik.ultimate.automata.Word;

public class TestCase<LETTER>{

	public TestCase(Word<LETTER> word, boolean isAccepted){
		this.word = word;
		this.isAccepted = isAccepted;
	}
	private Word<LETTER> word;
	private boolean isAccepted;
	
	public static <LETTER> void test(AlternatingAutomaton<LETTER, String> automaton, TestCase<LETTER>[] testCases){
		for(int i=0;i<testCases.length;i++){
			System.out.println("Test #" + i + " " + (testCases[i].test(automaton)?"successful":"failed"));
		}
	}
	
	public boolean test(AlternatingAutomaton<LETTER, String> automaton){
		return (automaton.accepts(word) == isAccepted);
	}
}
