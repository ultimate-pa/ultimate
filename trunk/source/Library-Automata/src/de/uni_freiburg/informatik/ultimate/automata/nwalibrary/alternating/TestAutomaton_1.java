package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.alternating;

import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.automata.Word;

public class TestAutomaton_1 extends AlternatingAutomaton<String, String>{

	public TestAutomaton_1(){
		super(generateAlphabet(), null);
		String state1 = new String("q1_1");
		String state2 = new String("q1_2");
		addState(state1);
		addState(state2);
		setStateFinal(state2);
		addTransition(a, state1, generateDisjunction(new String[]{state1}, new String[]{}));
		addTransition(a, state1, generateDisjunction(new String[]{}, new String[]{state2}));
		addTransition(a, state2, generateDisjunction(new String[]{}, new String[]{state1, state2}));
		addTransition(b, state1, generateDisjunction(new String[]{state1}, new String[]{state2}));
		addTransition(b, state2, generateDisjunction(new String[]{}, new String[]{state1}));
		addTransition(b, state2, generateDisjunction(new String[]{}, new String[]{state2}));
		addAcceptingConjunction(generateDisjunction(new String[]{state1}, new String[]{state2}));
	}
	public static String a = new String("a");
	public static String b = new String("b");
	@SuppressWarnings("unchecked")
	public static TestCase<String>[] TEST_CASES = new TestCase[]{
		new TestCase<String>(new Word<String>(a,a,a,b), true),
		new TestCase<String>(new Word<String>(b,a,a,a), false)
	};
	
	private static HashSet<String> generateAlphabet(){
		HashSet<String> alphabet = new HashSet<String>();
		alphabet.add(a);
		alphabet.add(b);
		return alphabet;
	}
}
