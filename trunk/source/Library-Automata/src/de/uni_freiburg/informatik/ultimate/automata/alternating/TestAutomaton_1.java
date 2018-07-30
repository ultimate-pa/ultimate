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

import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.automata.Word;

public final class TestAutomaton_1 extends AlternatingAutomaton<String, String> {
	public static final String a = "a";
	public static final String b = "b";

	@SuppressWarnings("unchecked")
	public static final TestCase<String>[] TEST_CASES = new TestCase[] { new TestCase<>(new Word<>(a, a, a, b), true),
			new TestCase<>(new Word<>(b, a, a, a), false) };

	public TestAutomaton_1() {
		super(generateAlphabet());
		final String state1 = "q1_1";
		final String state2 = "q1_2";
		addState(state1);
		addState(state2);
		setStateFinal(state2);
		addTransition(a, state1, generateCube(new String[] { state1 }, new String[] {}));
		addTransition(a, state1, generateCube(new String[] {}, new String[] { state2 }));
		addTransition(a, state2, generateCube(new String[] {}, new String[] { state1, state2 }));
		addTransition(b, state1, generateCube(new String[] { state1 }, new String[] { state2 }));
		addTransition(b, state2, generateCube(new String[] {}, new String[] { state1 }));
		addTransition(b, state2, generateCube(new String[] {}, new String[] { state2 }));
		addAcceptingConjunction(generateCube(new String[] { state1 }, new String[] { state2 }));
	}

	private static HashSet<String> generateAlphabet() {
		final HashSet<String> alphabet = new HashSet<>();
		alphabet.add(a);
		alphabet.add(b);
		return alphabet;
	}
}
