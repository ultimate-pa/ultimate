/*
 * Copyright (C) 2018 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures;

import java.util.Collection;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaInclusionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEquivalent;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetSuccessorProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.PetriNet2FiniteAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;

/**
 * Provides static methods for Petri nets.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public final class PetriNetUtils {

	private PetriNetUtils() {
		// do not instantiate
	}

	public static <LETTER, PLACE> boolean similarPredecessorPlaces(
			final Collection<ITransition<LETTER, PLACE>> transitions, final IPetriNetSuccessorProvider<LETTER, PLACE> net) {
		if (transitions.isEmpty()) {
			return true;
		} else {
			final Set<PLACE> predecessorPlaces = net.getPredecessors(transitions.iterator().next());
			for (final ITransition<LETTER, PLACE> transition : transitions) {
				final Set<PLACE> transPredPlaces = net.getPredecessors(transition);
				if (!predecessorPlaces.equals(transPredPlaces)) {
					return false;
				}
			}
			return true;
		}
	}

	/**
	 * Checks equivalent of two Petri nets.
	 * Two Petri nets are equivalent iff they accept the same language.
	 * <p>
	 * This is a naive implementation and may be very slow.
	 *
	 * @param net1 Petri net
	 * @param net2 Petri net
	 * @return net1 and net2 accept the same language
	 * @throws AutomataLibraryException The operation was canceled
	 */
	public static <LETTER, PLACE, CRSF extends
			IPetriNet2FiniteAutomatonStateFactory<PLACE> & INwaInclusionStateFactory<PLACE>>
			boolean isEquivalent( final AutomataLibraryServices services, final CRSF stateFactory,
			final IPetriNet<LETTER, PLACE> net1, final IPetriNet<LETTER, PLACE> net2) throws AutomataLibraryException {
		return new IsEquivalent<>(services, stateFactory, netToNwa(services, stateFactory, net1),
				netToNwa(services, stateFactory, net2)).getResult();
	}

	private static <LETTER, PLACE, CRSF extends IPetriNet2FiniteAutomatonStateFactory<PLACE>> INwaOutgoingLetterAndTransitionProvider<LETTER, PLACE> netToNwa(
			final AutomataLibraryServices mServices, final CRSF stateFactory, final IPetriNet<LETTER, PLACE> net)
			throws AutomataOperationCanceledException {
		return new PetriNet2FiniteAutomaton<>(mServices, stateFactory, net).getResult();
	}

}
