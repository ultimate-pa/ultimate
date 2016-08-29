/*
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

public class TestUnion {

	public static void main(final String[] args) {
		final TestAutomaton_1 automaton1 = new TestAutomaton_1();
		final TestAutomaton_2 automaton2 = new TestAutomaton_2();
		final AA_MergedUnion<String, String> union = new AA_MergedUnion<String, String>(automaton1, automaton2);
		final AlternatingAutomaton<String, String> resultAutomaton = union.getResult();
		final long startNanoTime = System.nanoTime();
		TestCase.test(resultAutomaton, TestAutomaton_1.TEST_CASES);
		TestCase.test(resultAutomaton, TestAutomaton_2.TEST_CASES);
		System.out.println(((System.nanoTime() - startNanoTime) / 1000000f) + " ms");
	}
}
