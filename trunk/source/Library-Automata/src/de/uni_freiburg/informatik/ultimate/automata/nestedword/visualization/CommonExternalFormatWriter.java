/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2017 University of Freiburg
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

import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.GeneralAutomatonPrinter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;

/**
 * Common methods for writers of external formats.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public abstract class CommonExternalFormatWriter<LETTER, STATE> extends GeneralAutomatonPrinter {
	protected final Map<LETTER, String> mAlphabetMapping;
	protected final Map<STATE, String> mStateMapping;
	protected final INestedWordAutomaton<LETTER, STATE> mNwa;

	/**
	 * @param writer
	 *            Print writer.
	 * @param nwa
	 *            nested word automaton
	 */
	public CommonExternalFormatWriter(final PrintWriter writer, final INestedWordAutomaton<LETTER, STATE> nwa) {
		super(writer);
		mAlphabetMapping = getAlphabetMapping(nwa.getVpAlphabet().getInternalAlphabet());
		mStateMapping = getStateMapping(nwa.getStates());
		mNwa = nwa;
		finish();
	}

	private Map<LETTER, String> getAlphabetMapping(final Collection<LETTER> alphabet) {
		int counter = 0;
		final Map<LETTER, String> alphabetMapping = new LinkedHashMap<>();

		final ArrayList<LETTER> alphabetList = new ArrayList<>(alphabet);

		Collections.sort(alphabetList, new sortLetter<LETTER>());
		for (final LETTER letter : alphabetList) {
			alphabetMapping.put(letter, Integer.toString(counter));
			counter++;
		}
		return alphabetMapping;
	}

	private Map<STATE, String> getStateMapping(final Collection<STATE> states) {
		int counter = 0;
		final Map<STATE, String> stateMapping = new HashMap<>();
		for (final STATE state : states) {
			stateMapping.put(state, Integer.toString(counter));
			++counter;
		}
		return stateMapping;
	}


	public static <LETTER> Map<LETTER, String> constructAlphabetMapping(final Collection<LETTER> alphabet,
			final char symbol) {
		int counter = 0;
		final Map<LETTER, String> alphabetMapping = new LinkedHashMap<>();
		final ArrayList<LETTER> alphabetList = new ArrayList<LETTER>(alphabet);
		Collections.sort(alphabetList, new sortLetter<LETTER>());
		for (final LETTER letter : alphabetList) {
			alphabetMapping.put(letter, symbol + Integer.toString(counter));
			counter++;
		}
		return alphabetMapping;
	}

	/**
	 * Converts a parametric object to a {@link String}.
	 *
	 * @param <E>
	 *            type of object to print
	 */
	@FunctionalInterface
	protected interface IConverter<E> {
		/**
		 * @param element
		 *            Element.
		 * @return corresponding string
		 */
		String convert(E element);
	}

	/**
	 * Uses the {@link String#valueOf(Object)} method for printing.
	 *
	 * @param <E>
	 *            type of object to print
	 */
	protected static class ToStringConverter<E> implements IConverter<E> {
		@Override
		public String convert(final E elem) {
			return elem.toString();
		}
	}

	/**
	 * Uses the {@link String#valueOf(Object)} method and a map for printing.
	 *
	 * @param <E>
	 *            type of object to print
	 * @param <V>
	 *            type of mapped object
	 */
	protected static class MapBasedConverter<E, V> implements IConverter<E> {
		private final Map<E, V> mMap;

		public MapBasedConverter(final Map<E, V> map) {
			mMap = map;
		}

		@Override
		public String convert(final E elem) {
			final V value = mMap.get(elem);
			if (value == null) {
				throw new IllegalArgumentException("unknown element: " + elem);
			}
			return String.valueOf(value);
		}
	}
}
