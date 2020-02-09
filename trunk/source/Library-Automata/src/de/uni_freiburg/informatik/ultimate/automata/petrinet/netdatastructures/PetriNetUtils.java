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
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.AutomatonWithImplicitSelfloops;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaInclusionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEquivalent;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsIncluded;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.DifferenceDD;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetSuccessorProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.PetriNet2FiniteAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

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
			throws PetriNetNot1SafeException, AutomataOperationCanceledException {
		return new PetriNet2FiniteAutomaton<>(mServices, stateFactory, net).getResult();
	}

	/**
	 * List hash codes of Petri net's internal objects. Useful for detecting
	 * nondeterminism. Should only be used for debugging.
	 */
	public static <LETTER, PLACE> String printHashCodesOfInternalDataStructures(
			final BoundedPetriNet<LETTER, PLACE> net) {
		final StringBuilder sb = new StringBuilder();
		sb.append("HashCodes of PetriNet data structures ");
		sb.append(System.lineSeparator());
		int placeCounter = 0;
		for (final PLACE place : net.getInitialPlaces()) {
			sb.append("Place " + placeCounter + ": " + place.hashCode());
			sb.append(System.lineSeparator());
			placeCounter++;
		}
		int transitionCounter = 0;
		for (final ITransition<LETTER, PLACE> trans : net.getTransitions()) {
			sb.append(trans.hashCode());
			sb.append("Place " + transitionCounter + ": " + trans.hashCode());
			sb.append(System.lineSeparator());
			transitionCounter++;
		}
		return sb.toString();
	}

	/**
	 * Uses finite automata to check if the result of our Petri net difference operations is correct.
	 */
	public static <LETTER, PLACE, CRSF extends IPetriNet2FiniteAutomatonStateFactory<PLACE> & INwaInclusionStateFactory<PLACE>> boolean doDifferenceLanguageCheck(
			final AutomataLibraryServices services, final CRSF stateFactory, final BoundedPetriNet<LETTER, PLACE> minuend,
			final INestedWordAutomaton<LETTER, PLACE> subtrahend, final BoundedPetriNet<LETTER, PLACE> result)
			throws PetriNetNot1SafeException, AutomataOperationCanceledException, AutomataLibraryException {
		final AutomatonWithImplicitSelfloops<LETTER, PLACE> subtrahendWithSelfloopsInAcceptingStates = new AutomatonWithImplicitSelfloops<>(
				services, subtrahend, subtrahend.getAlphabet(), new HashSet<>(subtrahend.getFinalStates()));
		final INestedWordAutomaton<LETTER, PLACE> op1AsNwa = (new PetriNet2FiniteAutomaton<>(services, stateFactory,
				minuend)).getResult();
		final INwaOutgoingLetterAndTransitionProvider<LETTER, PLACE> rcResult = (new DifferenceDD<>(services,
				stateFactory, op1AsNwa, subtrahendWithSelfloopsInAcceptingStates)).getResult();
		final INwaOutgoingLetterAndTransitionProvider<LETTER, PLACE> resultAsNwa = (new PetriNet2FiniteAutomaton<>(
				services, stateFactory, result)).getResult();

		final IsIncluded<LETTER, PLACE> isSubset = new IsIncluded<>(services, stateFactory, resultAsNwa, rcResult);
		if (!isSubset.getResult()) {
			final NestedWord<LETTER> ctx = isSubset.getCounterexample().getWord();
			final ILogger logger = services.getLoggingService().getLogger(PetriNetUtils.class);
			logger.error("Accepted by resulting net but not in difference of languages : " + ctx);
		}
		final IsIncluded<LETTER, PLACE> isSuperset = new IsIncluded<>(services, stateFactory, rcResult, resultAsNwa);
		if (!isSuperset.getResult()) {
			final NestedWord<LETTER> ctx = isSuperset.getCounterexample().getWord();
			final ILogger logger = services.getLoggingService().getLogger(PetriNetUtils.class);
			logger.error("In difference of languages but not accepted by resulting net : " + ctx);
		}
		return isSubset.getResult() && isSuperset.getResult();
	}


	public static <PLACE> String generateStatesAndPlacesDisjointErrorMessage(final PLACE state) {
		return "Currently, we require that states of the automaton are disjoint from places of Petri net. Please rename: "
				+ state;
	}

}
