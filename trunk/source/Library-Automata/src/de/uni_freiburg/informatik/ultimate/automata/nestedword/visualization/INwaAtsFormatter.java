/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.visualization;

import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.GeneralAutomatonPrinter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;

public interface INwaAtsFormatter<LETTER, STATE> {
	Map<LETTER, String> getAlphabetMapping(final Collection<LETTER> alphabet, final char symbol);

	Map<STATE, String> getStateMapping(final Collection<STATE> states);

	/**
	 * Prints an {@link INestedWordAutomaton}. In this version letters and states are represented by their
	 * {@link #toString()} method.
	 *
	 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 * @param <LETTER>
	 *            letter type
	 * @param <STATE>
	 *            state type
	 */
	class ToString<LETTER, STATE> implements INwaAtsFormatter<LETTER, STATE> {
		@Override
		public Map<LETTER, String> getAlphabetMapping(final Collection<LETTER> alphabet, final char symbol) {
			final Map<LETTER, String> alphabetMapping = new HashMap<>();
			for (final LETTER letter : alphabet) {
				alphabetMapping.put(letter, GeneralAutomatonPrinter.quoteAndReplaceBackslashes(letter));
			}
			return alphabetMapping;
		}

		@Override
		public Map<STATE, String> getStateMapping(final Collection<STATE> states) {
			final Map<STATE, String> stateMapping = new HashMap<>();
			for (final STATE state : states) {
				stateMapping.put(state, GeneralAutomatonPrinter.quoteAndReplaceBackslashes(state));
			}
			return stateMapping;
		}
	}

	/**
	 * Prints an {@link INestedWordAutomaton}. In this version letters and states are represented by their
	 * {@link #toString()} and {@link #hashCode()} methods.
	 *
	 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 * @param <LETTER>
	 *            letter type
	 * @param <STATE>
	 *            state type
	 */
	class ToStringWithHash<LETTER, STATE> implements INwaAtsFormatter<LETTER, STATE> {
		/**
		 * Print hash modulo this number to get shorter identifiers.
		 */
		private static int sHashDivisor = 1;

		@Override
		public Map<LETTER, String> getAlphabetMapping(final Collection<LETTER> alphabet, final char symbol) {
			final Map<LETTER, String> alphabetMapping = new HashMap<>();
			for (final LETTER letter : alphabet) {
				alphabetMapping.put(letter, GeneralAutomatonPrinter.quoteAndReplaceBackslashes(letter,
						Integer.toString(letter.hashCode() / sHashDivisor)));
			}
			return alphabetMapping;
		}

		@Override
		public Map<STATE, String> getStateMapping(final Collection<STATE> states) {
			final Map<STATE, String> stateMapping = new HashMap<>();
			for (final STATE state : states) {
				stateMapping.put(state, GeneralAutomatonPrinter.quoteAndReplaceBackslashes(state,
						Integer.toString(state.hashCode() / sHashDivisor)));
			}
			return stateMapping;
		}
	}

	class UniqueId<LETTER, STATE> implements INwaAtsFormatter<LETTER, STATE> {
		@Override
		public Map<LETTER, String> getAlphabetMapping(final Collection<LETTER> alphabet, final char symbol) {
			return CommonExternalFormatWriter.constructAlphabetMapping(alphabet, symbol);
		}

		@Override
		public Map<STATE, String> getStateMapping(final Collection<STATE> states) {
			int counter = 0;
			final Map<STATE, String> stateMapping = new LinkedHashMap<>();
			for (final STATE state : states) {
				stateMapping.put(state, 's' + Integer.toString(counter));
				counter++;
			}
			return stateMapping;
		}
	}
}
