/*
 * Copyright (C) 2020 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.petrinet;

import java.util.Collection;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.ISuccessorTransitionProvider;

/**
 * Interface for the development of on-demand Petri net operations, where the
 * construction is driven by an unfolding. TODO: more details
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public interface IPetriNetSuccessorProvider<LETTER, PLACE> extends IAutomaton<LETTER, PLACE> {

	Set<PLACE> getInitialPlaces();

	/**
	 *
	 * @return {@link ISuccessorTransitionProvider}s such that the set of predecessors contains only "mayPlaces" and at
	 *         least one "mustPlaces".
	 */
	Collection<ISuccessorTransitionProvider<LETTER, PLACE>> getSuccessorTransitionProviders(final Set<PLACE> mustPlaces,
			final Set<PLACE> mayPlaces);

	/**
	 * @param marking A marking.
	 * @return {@code true} iff the marking is accepting.
	 */
	boolean isAccepting(Marking<PLACE> marking);

	boolean isAccepting(PLACE place);

}