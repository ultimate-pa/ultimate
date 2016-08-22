/*
 * Copyright (C) 2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Carl Kuesters
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automata Library.
 * 
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.alternating;

import java.util.BitSet;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.automata.Word;

public class TestAutomaton_2 extends AlternatingAutomaton<String, String> {
	public static String a = new String("a");
	public static String b = new String("b");

	//b*a(a|ba)*b(a|b)*
	public TestAutomaton_2() {
		super(generateAlphabet(), null);
		final String state1 = new String("q2_1");
		final String state2 = new String("q2_2");
		final String state3 = new String("q2_3");
		addState(state1);
		addState(state2);
		addState(state3);
		addTransition(a, state1, generateCube(new String[]{state2, state3}, new String[]{}));
		addTransition(a, state2, generateCube(new String[]{state2, state3}, new String[]{}));
		addTransition(a, state3, new BooleanExpression(new BitSet(), new BitSet()));
		addTransition(b, state1, generateCube(new String[]{state2}, new String[]{}));
		addTransition(b, state2, generateCube(new String[]{state2}, new String[]{}));
		addTransition(b, state2, generateCube(new String[]{state3}, new String[]{}));
		addTransition(b, state3, generateCube(new String[]{state2}, new String[]{}));
		addAcceptingConjunction(generateCube(new String[]{state1}, new String[]{}));
	}
	
	@SuppressWarnings("unchecked")
	public static TestCase<String>[] TEST_CASES = new TestCase[]{
		new TestCase<String>(new Word<String>(b,b,a), true),
		new TestCase<String>(new Word<String>(a,b,b,b,b,b,b,a), true),
		new TestCase<String>(new Word<String>(b,a,b,a), false),
		new TestCase<String>(new Word<String>(b,b,a,b,a,a,a), true),
		new TestCase<String>(new Word<String>(a,a,a,a,a,a,b,b,a), true)
	};
	
	private static HashSet<String> generateAlphabet() {
		final HashSet<String> alphabet = new HashSet<String>();
		alphabet.add(a);
		alphabet.add(b);
		return alphabet;
	}
}
