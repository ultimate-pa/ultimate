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
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;
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
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNetTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.operations.PetriNet2FiniteAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IPetriNet2FiniteAutomatonStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Provides static methods for Petri nets.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public final class PetriNetUtils {

	private PetriNetUtils() {
		// do not instantiate
	}

	public static <LETTER, PLACE> boolean
			similarPredecessorPlaces(final Collection<Transition<LETTER, PLACE>> transitions) {
		if (transitions.isEmpty()) {
			return true;
		}
		final Set<PLACE> predecessorPlaces = transitions.iterator().next().getPredecessors();
		return transitions.stream().allMatch(x -> predecessorPlaces.equals(x.getPredecessors()));
	}

	/**
	 * Checks equivalent of two Petri nets. Two Petri nets are equivalent iff they accept the same language.
	 * <p>
	 * This is a naive implementation and may be very slow.
	 *
	 * @param net1
	 *            Petri net
	 * @param net2
	 *            Petri net
	 * @return net1 and net2 accept the same language
	 * @throws AutomataLibraryException
	 *             The operation was canceled
	 */
	public static <LETTER, PLACE, CRSF extends IPetriNet2FiniteAutomatonStateFactory<PLACE> & INwaInclusionStateFactory<PLACE>>
			boolean isEquivalent(final AutomataLibraryServices services, final CRSF stateFactory,
					final IPetriNetTransitionProvider<LETTER, PLACE> net1,
					final IPetriNetTransitionProvider<LETTER, PLACE> net2) throws AutomataLibraryException {
		return new IsEquivalent<>(services, stateFactory, netToNwa(services, stateFactory, net1),
				netToNwa(services, stateFactory, net2)).getResult();
	}

	private static <LETTER, PLACE, CRSF extends IPetriNet2FiniteAutomatonStateFactory<PLACE>>
			INwaOutgoingLetterAndTransitionProvider<LETTER, PLACE> netToNwa(final AutomataLibraryServices mServices,
					final CRSF stateFactory, final IPetriNetTransitionProvider<LETTER, PLACE> net)
					throws PetriNetNot1SafeException, AutomataOperationCanceledException {
		return new PetriNet2FiniteAutomaton<>(mServices, stateFactory, net).getResult();
	}

	/**
	 * List hash codes of Petri net's internal objects. Useful for detecting nondeterminism. Should only be used for
	 * debugging.
	 */
	public static <LETTER, PLACE> String printHashCodesOfInternalDataStructures(final IPetriNet<LETTER, PLACE> net) {
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
		for (final Transition<LETTER, PLACE> trans : net.getTransitions()) {
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
	public static <LETTER, PLACE, CRSF extends IPetriNet2FiniteAutomatonStateFactory<PLACE> & INwaInclusionStateFactory<PLACE>>
			boolean doDifferenceLanguageCheck(final AutomataLibraryServices services, final CRSF stateFactory,
					final IPetriNetTransitionProvider<LETTER, PLACE> minuend,
					final INestedWordAutomaton<LETTER, PLACE> subtrahend,
					final IPetriNetTransitionProvider<LETTER, PLACE> result)
					throws PetriNetNot1SafeException, AutomataOperationCanceledException, AutomataLibraryException {
		final AutomatonWithImplicitSelfloops<LETTER, PLACE> subtrahendWithSelfloopsInAcceptingStates =
				new AutomatonWithImplicitSelfloops<>(services, subtrahend, subtrahend.getAlphabet(),
						subtrahend::isFinal);
		final INestedWordAutomaton<LETTER, PLACE> op1AsNwa =
				new PetriNet2FiniteAutomaton<>(services, stateFactory, minuend).getResult();
		final INwaOutgoingLetterAndTransitionProvider<LETTER, PLACE> rcResult =
				new DifferenceDD<>(services, stateFactory, op1AsNwa, subtrahendWithSelfloopsInAcceptingStates)
						.getResult();
		final INwaOutgoingLetterAndTransitionProvider<LETTER, PLACE> resultAsNwa =
				new PetriNet2FiniteAutomaton<>(services, stateFactory, result).getResult();

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

	public static <PLACE> Map<PLACE, PLACE> mergePlaces(final Set<PLACE> places, final UnionFind<PLACE> uf) {
		final Map<PLACE, PLACE> result = new HashMap<>();
		for (final PLACE p : places) {
			final PLACE pRep = uf.find(p);
			if (pRep == null) {
				result.put(p, p);
			} else {
				result.put(p, pRep);
			}
		}
		return result;
	}

	public static <LETTER, PLACE> Map<Transition<LETTER, PLACE>, Transition<LETTER, PLACE>>
			mergePlaces(final IPetriNet<LETTER, PLACE> net, final Map<PLACE, PLACE> map) {
		final Map<Transition<LETTER, PLACE>, Transition<LETTER, PLACE>> result = new HashMap<>();
		for (final Transition<LETTER, PLACE> oldT : net.getTransitions()) {
			final ImmutableSet<PLACE> predecessors =
					oldT.getPredecessors().stream().map(map::get).collect(ImmutableSet.collector());
			final ImmutableSet<PLACE> successors =
					oldT.getSuccessors().stream().map(map::get).collect(ImmutableSet.collector());
			final Transition<LETTER, PLACE> newT = new Transition<>(oldT.getSymbol(), predecessors, successors, 0);
			result.put(oldT, newT);
		}
		return result;
	}

	public static <LETTER, PLACE> IPetriNet<LETTER, PLACE> mergePlaces(final AutomataLibraryServices services,
			final IPetriNet<LETTER, PLACE> net, final Map<PLACE, PLACE> map) {
		final Map<Transition<LETTER, PLACE>, Transition<LETTER, PLACE>> transitionMap = mergePlaces(net, map);
		final BoundedPetriNet<LETTER, PLACE> result = new BoundedPetriNet<>(services, net.getAlphabet(), false);
		final Map<PLACE, Pair<Boolean, Boolean>> newPlaces = new HashMap<>();
		for (final PLACE p : net.getPlaces()) {
			final boolean isInitial = net.getInitialPlaces().contains(p);
			final boolean isAccepting = net.isAccepting(p);
			final PLACE newPlace = map.get(p);
			final Pair<Boolean, Boolean> iniAcc = newPlaces.get(newPlace);
			final boolean oldIsInitial;
			final boolean oldIsAccepting;
			if (iniAcc == null) {
				oldIsInitial = false;
				oldIsAccepting = false;
			} else {
				oldIsInitial = iniAcc.getFirst();
				oldIsAccepting = iniAcc.getSecond();
			}
			newPlaces.put(newPlace, new Pair<>(oldIsInitial || isInitial, oldIsAccepting || isAccepting));
		}
		for (final Entry<PLACE, Pair<Boolean, Boolean>> entry : newPlaces.entrySet()) {
			result.addPlace(entry.getKey(), entry.getValue().getFirst(), entry.getValue().getSecond());
		}
		for (final Entry<Transition<LETTER, PLACE>, Transition<LETTER, PLACE>> entry : transitionMap.entrySet()) {
			result.addTransition(entry.getValue().getSymbol(), entry.getValue().getPredecessors(),
					entry.getValue().getSuccessors());
		}
		return result;
	}

}
