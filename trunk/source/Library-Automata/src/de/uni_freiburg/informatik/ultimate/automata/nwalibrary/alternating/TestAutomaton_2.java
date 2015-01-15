package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.alternating;

import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.automata.Word;

public class TestAutomaton_2 extends AlternatingAutomaton<String, String>{

	//b*a(a|ba)*b(a|b)*
	public TestAutomaton_2(){
		super(generateAlphabet(), null);
		String state1 = new String("q2_1");
		String state2 = new String("q2_2");
		String state3 = new String("q2_3");
		addState(state1);
		addState(state2);
		addState(state3);
		addTransition(a, state1, generateDisjunction(new String[]{state2, state3}, new String[]{}));
		addTransition(a, state2, generateDisjunction(new String[]{state2, state3}, new String[]{}));
		addTransition(a, state3, new BooleanExpression(0, 0));
		addTransition(b, state1, generateDisjunction(new String[]{state2}, new String[]{}));
		addTransition(b, state2, generateDisjunction(new String[]{state2}, new String[]{}));
		addTransition(b, state2, generateDisjunction(new String[]{state3}, new String[]{}));
		addTransition(b, state3, generateDisjunction(new String[]{state2}, new String[]{}));
		addAcceptingConjunction(generateDisjunction(new String[]{state1}, new String[]{}));
	}
	public static String a = new String("a");
	public static String b = new String("b");
	@SuppressWarnings("unchecked")
	public static TestCase<String>[] TEST_CASES = new TestCase[]{
		new TestCase<String>(new Word<String>(b,b,a), true),
		new TestCase<String>(new Word<String>(a,b,b,b,b,b,b,a), true),
		new TestCase<String>(new Word<String>(b,a,b,a), false),
		new TestCase<String>(new Word<String>(b,b,a,b,a,a,a), true),
		new TestCase<String>(new Word<String>(a,a,a,a,a,a,b,b,a), true)
	};
	
	private static HashSet<String> generateAlphabet(){
		HashSet<String> alphabet = new HashSet<String>();
		alphabet.add(a);
		alphabet.add(b);
		return alphabet;
	}
}
