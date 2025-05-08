/*
 * Copyright (C) 2025 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2025 Matthias Zumkeller
 * Copyright (C) 2025 University of Freiburg
 *
 * This file is part of the ULTIMATE Proofs Library.
 *
 * The ULTIMATE Proofs Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Proofs Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Proofs Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Proofs Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Proofs Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire;

import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

public class EmpireAutomaton<L, P> implements IEmpireAutomaton<L, P, EmpireAutomaton.State<L, P>> {
	private final IPetriNet<L, P> mNet;
	private final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> mProduct;

	private final ILogger mLogger;

	public EmpireAutomaton(final IPetriNet<L, P> net,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> product,
			final IUltimateServiceProvider services) {
		mLogger = services.getLoggingService().getLogger(getClass());
		mLogger.setLevel(LogLevel.ERROR);

		mNet = net;
		mProduct = product;
	}

	@Override
	public IPredicate getLaw(final State<L, P> state) {
		return state.law();
	}

	@Override
	public boolean containsPlace(final State<L, P> state, final P place) {
		return state.territory().containsPlace(place);
	}

	@Override
	public VpAlphabet<Transition<L, P>> getVpAlphabet() {
		final var transitions = mNet.getTransitions();
		return new VpAlphabet<>(transitions);
	}

	@Override
	public Iterable<State<L, P>> getInitialStates() {
		final var initialLaw = DataStructureUtils.getOneAndOnly(mProduct.getInitialStates(), "initial law place");
		final var regions = mNet.getInitialPlaces().stream().map(p -> new Region<>(ImmutableSet.singleton(p)))
				.collect(ImmutableSet.collector());
		final State<L, P> state = new State<>(new Territory<>(regions), initialLaw, Collections.emptySet());
		final var markedSuccessor = getMarkedSuccessor(state);
		return List.of(markedSuccessor);
	}

	@Override
	public boolean isInitial(final State<L, P> state) {
		final var initialStates = getInitialStates();
		final Set<State<L, P>> initialState = new HashSet<>();
		initialStates.forEach(initialState::add);
		return initialState.contains(state);
	}

	/**
	 * Determines a state s as final, if it contains an error place and the law is false, OR if there exists at least
	 * one transition in enabled(territory(s)), for which there is no successor in the automaton. In this case, the
	 * successor law must be false.
	 */
	@Override
	public boolean isFinal(final State<L, P> state) {
		final var successors = internalSuccessors(state);
		final var succStates = new HashSet<State<L, P>>();
		for (final OutgoingInternalTransition<Transition<L, P>, State<L, P>> outgoingInternalTransition : successors) {
			final var succState = outgoingInternalTransition.getSucc();
			succStates.add(succState);
			if (state != succState) {
				return false;
			}
		}
		final var territory = state.territory();
		final var enabledTransitions = territory.getEnabledTransitions(mNet).collect(Collectors.toSet());
		final var acceptingPlaces = mNet.getAcceptingPlaces();
		if (DataStructureUtils.haveNonEmptyIntersection(territory.getPlaces(), acceptingPlaces)) {
			if (!SmtUtils.isFalseLiteral(state.law.getFormula())) {
				return false;
			}
			return true;
		}
		if (succStates.size() < enabledTransitions.size()) {
			final var falseSuccessors = enabledTransitions.stream()
					.anyMatch(t -> SmtUtils.isFalseLiteral(getSuccessorLaw(state.law, t).getFormula()));
			assert falseSuccessors
					: "There exists no successor for an enabled transition, but the successor law is not false";
		}
		// Check if there is at least one enabled transition, for which state has no successor
		return succStates.size() < enabledTransitions.size();
	}

	@Override
	public int size() {
		return -1;
	}

	@Override
	public String sizeInformation() {
		return "unknown";
	}

	@Override
	public Set<Transition<L, P>> lettersInternal(final State<L, P> state) {
		// TODO Consider whether we can efficiently override this method
		return IEmpireAutomaton.super.lettersInternal(state);
	}

	@Override
	public Iterable<OutgoingInternalTransition<Transition<L, P>, State<L, P>>>
			internalSuccessors(final State<L, P> state, final Transition<L, P> letter) {

		// (state is marked)

		// step 1: see if letter should lead to any successor at all or can be optimized away
		// (iterate over alphabet and see which other transitions are enabled in the territory)
		final var territory = state.territory;
		final var law = state.law;
		if (!territory.enables(letter)) {
			return List.of();
		}
		if (isExtendingTransition(law, getSuccessorLaw(law, letter), letter) && isCycle(state, letter)) {
			return List.of(new OutgoingInternalTransition<>(letter, state));
		}

		// step 2: compute the "direct" successor state for the given transition
		final var directSucc = getReplacementSuccessor(state, letter);
		final var succLaw = directSucc.law;
		if (SmtUtils.isFalseLiteral(succLaw.getFormula())) {
			return List.of();
		}

		// step 3: while the current successor is not marked, pick one (or a set of) transitions and compute the
		// successor again

		final var maxMarkedSuccessor = getMarkedSuccessor(directSucc);

		// return the edge to the maximal successor
		return List.of(new OutgoingInternalTransition<>(letter, maxMarkedSuccessor));
	}

	public record State<L, P>(Territory<P> territory, IPredicate law, Set<Region<P>> bystanders) {
		// empty body
	}

	private State<L, P> extendAll(final State<L, P> state, final Set<Transition<L, P>> transitions) {
		if (transitions.isEmpty()) {
			return state;
		}
		final var territory = state.territory;
		final Set<Region<P>> territoryRegions = new HashSet<>(territory.getRegions());
		final var extendedRegions = new HashSet<Region<P>>();
		for (final Region<P> region : territory.getRegions()) {
			final var matchingTransitions = findMatchingTransitions(region, transitions);
			if (!matchingTransitions.isEmpty()) {
				transitions.removeAll(matchingTransitions);
				final var successorPlaces = matchingTransitions.stream().flatMap(t -> t.getSuccessors().stream())
						.collect(Collectors.toSet());
				extendedRegions.add(
						new Region<>(ImmutableSet.of(DataStructureUtils.union(region.getPlaces(), successorPlaces))));
				territoryRegions.remove(region);
			}
		}
		final var newTerritory =
				new Territory<>(ImmutableSet.of(DataStructureUtils.union(extendedRegions, territoryRegions)));
		return new State<>(newTerritory, state.law, state.bystanders);
	}

	private Set<Transition<L, P>> findMatchingTransitions(final Region<P> region,
			final Set<Transition<L, P>> transitions) {
		final var predTransitions = new HashSet<Transition<L, P>>();
		final var places = region.getPlaces();
		for (final Transition<L, P> transition : transitions) {
			if (places.containsAll(transition.getPredecessors())) {
				predTransitions.add(transition);
			}
		}
		return predTransitions;
	}

	private Set<Transition<L, P>> getEnabledTransitions(final State<L, P> state) {
		final var territory = state.territory;
		final var lawPlace = state.law;
		final var enabledTransitions = territory.getEnabledTransitions(mNet).collect(Collectors.toSet());
		final var notBotTransitions = new HashSet<Transition<L, P>>();
		for (final Transition<L, P> transition : enabledTransitions) {
			final var succLaw = getSuccessorLaw(lawPlace, transition);
			if (!SmtUtils.isFalseLiteral(succLaw.getFormula())) {
				notBotTransitions.add(transition);
			}
		}
		return notBotTransitions;
	}

	private IPredicate getSuccessorLaw(final IPredicate law, final Transition<L, P> transition) {
		final var succLaw = mProduct.internalSuccessors(law, transition.getSymbol());
		IPredicate newLawPlace = law;
		if (succLaw.iterator().hasNext()) {
			newLawPlace = DataStructureUtils.getOneAndOnly(succLaw, "successor state").getSucc();
		} else {
			mLogger.warn("No successor law for transition: %s and law: %s", transition, law);
		}
		return newLawPlace;
	}

	private boolean isExtendingTransition(final IPredicate lawPlace, final IPredicate newLawPlace,
			final Transition<L, P> transition) {
		final var predecessors = transition.getPredecessors();
		final var successors = transition.getSuccessors();
		if (lawPlace == newLawPlace && predecessors.size() == 1 && successors.size() == 1) {
			return true;
		}
		return false;
	}

	private Set<Transition<L, P>> getExtendingTransitions(final State<L, P> state,
			final Set<Transition<L, P>> transitions) {
		final var lawPlace = state.law;
		final var extendingTransitions = new HashSet<Transition<L, P>>();
		for (final Transition<L, P> transition : transitions) {
			final var succLaw = getSuccessorLaw(lawPlace, transition);
			if (isExtendingTransition(lawPlace, succLaw, transition)) {
				extendingTransitions.add(transition);
			}
		}
		return extendingTransitions;
	}

	private boolean isNecessaryBridge(final State<L, P> state, final Transition<L, P> transition) {
		final var territory = state.territory;
		final var bs = state.bystanders;
		return !territory.getBystanders(transition).containsAll(bs);
	}

	private Set<Transition<L, P>> getUnnecessaryTransitions(final State<L, P> state,
			final Set<Transition<L, P>> transitions) {
		final var extending = getExtendingTransitions(state, transitions);
		return extending.stream().filter(t -> !isNecessaryBridge(state, t)).collect(Collectors.toSet());
	}

	private Boolean isCycle(final State<L, P> state, final Transition<L, P> transition) {
		final var territory = state.territory;
		final var law = state.law;
		final var successors = transition.getSuccessors();
		if (!territory.enables(transition)
				|| !isExtendingTransition(law, getSuccessorLaw(law, transition), transition)) {
			return false;
		}
		return territory.getPlaces().containsAll(successors);
	}

	private State<L, P> getMarkedSuccessor(final State<L, P> state) {
		final var enabledTransitions = getEnabledTransitions(state);
		final var unnecessaryTransitions = getUnnecessaryTransitions(state, enabledTransitions);
		final var nonCyclicTransitions =
				unnecessaryTransitions.stream().filter(t -> !isCycle(state, t)).collect(Collectors.toSet());
		if (nonCyclicTransitions.isEmpty()) {
			return state;
		}
		final var extendedState = extendAll(state, nonCyclicTransitions);
		return getMarkedSuccessor(extendedState);
	}

	private State<L, P> getReplacementSuccessor(final State<L, P> state, final Transition<L, P> transition) {
		final var territory = state.territory;
		final var lawPlace = state.law;

		final IPredicate newLawPlace = getSuccessorLaw(lawPlace, transition);

		var regions = territory.getBystanders(transition);

		regions = replaceRegions(transition, regions);
		final var newTerritory = new Territory<>(ImmutableSet.of(regions));
		final var newBystanders = territory.getBystanders(transition);
		return new State<>(newTerritory, newLawPlace, newBystanders);
	}

	private Set<Region<P>> replaceRegions(final Transition<L, P> transition, final Set<Region<P>> bystanders) {
		final var regions = new HashSet<>(bystanders);
		final var successors = transition.getSuccessors();
		for (final var succ : successors) {
			regions.add(new Region<>(ImmutableSet.singleton(succ)));
		}
		return regions;
	}
}
