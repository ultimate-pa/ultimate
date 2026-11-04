/*
 * Copyright (C) 2015 Carl Kuesters
 * Copyright (C) 2015 University of Freiburg
 * Copyright (C) 2026 Dominik Klumpp(klumpp@lix.polytechnique.fr)
 * Copyright (C) 2026 Ecole Polytechnique
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

import org.junit.Before;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.test.mocks.UltimateMocks;

public class AlternatingAutomataTest {
	private AutomataLibraryServices mServices;

	@Before
	public void setUp() {
		mServices = new AutomataLibraryServices(UltimateMocks.createUltimateServiceProviderMock(LogLevel.INFO));
	}

	@Test
	public void test1() {
		final TestAutomaton_1 automaton = new TestAutomaton_1();
		final long startNanoTime = System.nanoTime();
		TestCase.test(automaton, TestAutomaton_1.TEST_CASES);
		System.out.println(((System.nanoTime() - startNanoTime) / 1000000F) + " ms");
	}

	@Test
	public void test2() {
		final TestAutomaton_2 automaton = new TestAutomaton_2();
		final long startNanoTime = System.nanoTime();
		TestCase.test(automaton, TestAutomaton_2.TEST_CASES);
		System.out.println(((System.nanoTime() - startNanoTime) / 1000000F) + " ms");
	}

	@Test
	public void testUnion() {
		final TestAutomaton_1 automaton1 = new TestAutomaton_1();
		final TestAutomaton_2 automaton2 = new TestAutomaton_2();
		final AA_MergedUnion<String, String> union = new AA_MergedUnion<>(mServices, automaton1, automaton2);
		final AlternatingAutomaton<String, String> resultAutomaton = union.getResult();
		final long startNanoTime = System.nanoTime();
		TestCase.test(resultAutomaton, TestAutomaton_1.TEST_CASES);
		TestCase.test(resultAutomaton, TestAutomaton_2.TEST_CASES);
		System.out.println(((System.nanoTime() - startNanoTime) / 1000000F) + " ms");
	}

	private static final class TestCase<LETTER> {
		private final Word<LETTER> mWord;
		private final boolean mIsAccepted;

		public TestCase(final Word<LETTER> word, final boolean isAccepted) {
			mWord = word;
			mIsAccepted = isAccepted;
		}

		public static <LETTER> void test(final AlternatingAutomaton<LETTER, String> automaton,
				final TestCase<LETTER>[] testCases) {
			for (int i = 0; i < testCases.length; i++) {
				System.out.println("Test #" + i + " " + (testCases[i].test(automaton) ? "successful" : "failed"));
			}
		}

		public boolean test(final AlternatingAutomaton<LETTER, String> automaton) {
			return (automaton.accepts(mWord) == mIsAccepted);
		}
	}

	private static final class TestAutomaton_1 extends AlternatingAutomaton<String, String> {
		public static final String a = "a";
		public static final String b = "b";

		@SuppressWarnings("unchecked")
		public static final TestCase<String>[] TEST_CASES = new TestCase[] {
				new TestCase<>(new Word<>(a, a, a, b), true), new TestCase<>(new Word<>(b, a, a, a), false) };

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

	private static final class TestAutomaton_2 extends AlternatingAutomaton<String, String> {
		public static final String a = "a";
		public static final String b = "b";

		@SuppressWarnings("unchecked")
		public static final TestCase<String>[] TEST_CASES = new TestCase[] { new TestCase<>(new Word<>(b, b, a), true),
				new TestCase<>(new Word<>(a, b, b, b, b, b, b, a), true), new TestCase<>(new Word<>(b, a, b, a), false),
				new TestCase<>(new Word<>(b, b, a, b, a, a, a), true),
				new TestCase<>(new Word<>(a, a, a, a, a, a, b, b, a), true) };

		// b*a(a|ba)*b(a|b)*
		public TestAutomaton_2() {
			super(generateAlphabet());
			final String state1 = "q2_1";
			final String state2 = "q2_2";
			final String state3 = "q2_3";
			addState(state1);
			addState(state2);
			addState(state3);
			addTransition(a, state1, generateCube(new String[] { state2, state3 }, new String[] {}));
			addTransition(a, state2, generateCube(new String[] { state2, state3 }, new String[] {}));
			addTransition(a, state3, new BooleanExpression(new BitSet(), new BitSet()));
			addTransition(b, state1, generateCube(new String[] { state2 }, new String[] {}));
			addTransition(b, state2, generateCube(new String[] { state2 }, new String[] {}));
			addTransition(b, state2, generateCube(new String[] { state3 }, new String[] {}));
			addTransition(b, state3, generateCube(new String[] { state2 }, new String[] {}));
			addAcceptingConjunction(generateCube(new String[] { state1 }, new String[] {}));
		}

		private static HashSet<String> generateAlphabet() {
			final HashSet<String> alphabet = new HashSet<>();
			alphabet.add(a);
			alphabet.add(b);
			return alphabet;
		}
	}
}
