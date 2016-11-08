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

import de.uni_freiburg.informatik.ultimate.automata.Word;

public class TestCase<LETTER> {
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
