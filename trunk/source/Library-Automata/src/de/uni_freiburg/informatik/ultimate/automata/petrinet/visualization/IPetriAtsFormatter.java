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
package de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.GeneralAutomatonPrinter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.visualization.CommonExternalFormatWriter;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;

public interface IPetriAtsFormatter<LETTER, PLACE> {
	Map<LETTER, String> getAlphabetMapping(final Collection<LETTER> alphabet);

	Map<PLACE, String> getPlacesMapping(final Collection<PLACE> places);

	/**
	 * Prints a {@link BoundedPetriNet}. In this version letters and places are represented by their {@link #toString()}
	 * method.
	 *
	 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 * @param <LETTER>
	 *            letter type
	 * @param <PLACE>
	 *            place type
	 */
	class ToString<LETTER, PLACE> implements IPetriAtsFormatter<LETTER, PLACE> {
		@Override
		public Map<LETTER, String> getAlphabetMapping(final Collection<LETTER> alphabet) {
			final Map<LETTER, String> alphabetMapping = new HashMap<>();
			for (final LETTER letter : alphabet) {
				alphabetMapping.put(letter, GeneralAutomatonPrinter.quoteAndReplaceBackslashes(letter));
			}
			return alphabetMapping;
		}

		@Override
		public Map<PLACE, String> getPlacesMapping(final Collection<PLACE> places) {
			final HashMap<PLACE, String> placesMapping = new HashMap<>();
			for (final PLACE place : places) {
				placesMapping.put(place, GeneralAutomatonPrinter.quoteAndReplaceBackslashes(place));
			}
			return placesMapping;
		}
	}

	/**
	 * Prints a {@link BoundedPetriNet}. In this version letters and places are represented by their {@link #toString()}
	 * method and a unique number.
	 *
	 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 * @param <LETTER>
	 *            letter type
	 * @param <PLACE>
	 *            place type
	 */
	class ToStringWithUniqueNumber<LETTER, PLACE> implements IPetriAtsFormatter<LETTER, PLACE> {
		@Override
		public Map<LETTER, String> getAlphabetMapping(final Collection<LETTER> alphabet) {
			int counter = 0;
			final Map<LETTER, String> alphabetMapping = new HashMap<>();
			for (final LETTER letter : alphabet) {
				alphabetMapping.put(letter,
						GeneralAutomatonPrinter.quoteAndReplaceBackslashes(letter, Integer.toString(counter)));
				counter++;
			}
			return alphabetMapping;
		}

		@Override
		public Map<PLACE, String> getPlacesMapping(final Collection<PLACE> places) {
			int counter = 0;
			final HashMap<PLACE, String> placesMapping = new HashMap<>();
			for (final PLACE place : places) {
				placesMapping.put(place,
						GeneralAutomatonPrinter.quoteAndReplaceBackslashes(place, Integer.toString(counter)));
				counter++;
			}
			return placesMapping;
		}
	}

	/**
	 * Prints a {@link BoundedPetriNet}. In this version letters and places are represented by a default symbol and a
	 * unique ID.
	 *
	 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 * @param <LETTER>
	 *            letter type
	 * @param <STATE>
	 *            state type
	 */
	class UniqueId<LETTER, PLACE> implements IPetriAtsFormatter<LETTER, PLACE> {
		@Override
		public Map<LETTER, String> getAlphabetMapping(final Collection<LETTER> alphabet) {
			return CommonExternalFormatWriter.constructAlphabetMapping(alphabet, 'a');
		}

		@Override
		public Map<PLACE, String> getPlacesMapping(final Collection<PLACE> places) {
			int counter = 0;
			final HashMap<PLACE, String> placesMapping = new HashMap<>();
			for (final PLACE place : places) {
				placesMapping.put(place, 'p' + Integer.toString(counter));
				counter++;
			}
			return placesMapping;
		}
	}
}
