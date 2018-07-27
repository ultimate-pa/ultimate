/*
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
package de.uni_freiburg.informatik.ultimate.automata;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;

/**
 * All automata have to implement this interface.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            Type of objects that are contained in the alphabet.
 * @param <STATE>
 *            Type of objects that are used to label states (resp. places for
 *            {@link de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet IPetriNet})
 */
public interface IAutomaton<LETTER, STATE> {
	/**
	 * @return Alphabet of this automaton.
	 */
	Set<LETTER> getAlphabet();

	/**
	 * Can the alphabet still change after the automaton was constructed? Note that the correctness of this property is
	 * not checked and the user of the library has to use this with caution. (There is no simple check for this property
	 * since the automata usually take user-provided {@link Set} objects as alphabet and for performance reasons we do
	 * not want to change this.)
	 *
	 * @return {@code true} iff the automaton's alphabet may be modified after the automaton was constructed
	 */
	default boolean hasModifiableAlphabet() {
		return false;
	}


	/**
	 * @return Size of the automaton. E.g., the number of states.
	 */
	int size();

	/**
	 * @return Some human readable information about the size of the automaton.
	 */
	String sizeInformation();

	/**
	 * Checks whether two automata have the same alphabet.
	 *
	 * @param fstOperand
	 *            first operand
	 * @param sndOperand
	 *            second operand
	 * @param <LETTER>
	 *            letter type
	 * @param <STATE>
	 *            state type
	 * @return {@code true} iff the automata have the same alphabet
	 */
	static <LETTER, STATE> boolean sameAlphabet(final IAutomaton<LETTER, STATE> fstOperand,
			final IAutomaton<LETTER, STATE> sndOperand) {
		return fstOperand.getAlphabet().equals(sndOperand.getAlphabet());
	}

	/**
	 * @param services
	 *            Ultimate services.
	 * @return Ultimate model of the automaton
	 * @throws AutomataOperationCanceledException
	 *             if operation was canceled
	 */
	IElement transformToUltimateModel(AutomataLibraryServices services) throws AutomataOperationCanceledException;
}
