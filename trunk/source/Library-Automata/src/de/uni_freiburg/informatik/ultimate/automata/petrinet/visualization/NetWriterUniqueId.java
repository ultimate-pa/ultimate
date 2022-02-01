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
package de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization;

import java.io.PrintWriter;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.visualization.CommonExternalFormatWriter;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;

/**
 * Prints a {@link BoundedPetriNet}. In this version letters and places are represented by a default symbol and a unique
 * ID.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public final class NetWriterUniqueId<LETTER, STATE> extends NetWriter<LETTER, STATE> {
	/**
	 * @param writer
	 *            Print writer.
	 * @param name
	 *            Petri net name
	 * @param net
	 *            Petri net
	 */
	public NetWriterUniqueId(final PrintWriter writer, final String name, final BoundedPetriNet<LETTER, STATE> net) {
		super(writer, name, net);
	}

	@Override
	protected Map<LETTER, String> getAlphabetMapping(final Collection<LETTER> alphabet) {
		return CommonExternalFormatWriter.constructAlphabetMapping(alphabet, 'a');
	}

	@Override
	protected Map<STATE, String> getPlacesMapping(final Collection<STATE> places) {
		int counter = 0;
		final HashMap<STATE, String> placesMapping = new HashMap<>();
		for (final STATE place : places) {
			placesMapping.put(place, 'p' + Integer.toString(counter));
			counter++;
		}
		return placesMapping;
	}
}
