/*
 * Copyright (C) 2011-2015 Julian Jarecki (jareckij@informatik.uni-freiburg.de)
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;

/**
 * Interface for possible extensions.
 *
 * @author Julian Jarecki (jareckij@informatik.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            symbol type
 * @param <PLACE>
 *            place content type
 */
public interface IPossibleExtensions<LETTER, PLACE> {
	/**
	 * Removes and returns the minimal element with respect to the specified Order. Throws an Exception if queue empty.
	 *
	 * @return the minimal element
	 */
	Event<LETTER, PLACE> remove();

	/**
	 * Extends set of possible extensions by all possible extensions which are successors of e.
	 *
	 * @param event
	 *            event
	 */
	void update(Event<LETTER, PLACE> event) throws PetriNetNot1SafeException;

	/**
	 * @return The size.
	 */
	int size();

	/**
	 * @return {@code true} iff there is no extension.
	 */
	boolean isEmpy();
	
	public int getUsefulExtensionCandidates();

	public int getUselessExtensionCandidates();

	public int getMaximalSize();
}
