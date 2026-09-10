/*
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
package de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.directed;

import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.IEmpire;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.Region;
import de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire.Territory;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

// Matthias Z (2026-06-06): This class was a nearly 1-to-1 copy from the original (SaturatedEmpire) class at the time.
// If we would parametrize the empire and State record with the type of region, with some engineering effort most of
// this class (maybe even the whole class) should be obsolete (besides the method extendAll).
public class DirectedEmpire<L, P> implements IEmpire<L, P, DirectedEmpire.State<L, P>> {
	private final ILogger mLogger;

	private final IPetriNet<L, P> mNet;
	private final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> mProof;

	private final State<L, P> mInitialState;

	public DirectedEmpire(final IPetriNet<L, P> net, final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> proof,
			final IUltimateServiceProvider services) {
		mLogger = services.getLoggingService().getLogger(getClass());
		mNet = net;
		mProof = proof;

		// Construct initial state
		final var initialLaw = DataStructureUtils.getOneAndOnly(mProof.getInitialStates(), "initial law place");
		final var regions = getInitialRegions();
		final State<L, P> state = new State<>(new Territory<>(regions), initialLaw, Collections.emptySet());
		mInitialState = getMarkedSuccessor(state);
	}

	@Override
	public IPredicate getLaw(final State<L, P> state) {
		return state.law();
	}

	@Override
	public Territory<P, Region<P>> getTerritory(final State<L, P> state) {
		return (Territory) state.territory();
	}

	@Override
	public VpAlphabet<Transition<L, P>> getVpAlphabet() {
		return new VpAlphabet<>(mNet.getTransitions());
	}

	@Override
	public Iterable<State<L, P>> getInitialStates() {
		return List.of(mInitialState);
	}

	@Override
	public boolean isInitial(final State<L, P> state) {
		return mInitialState.equals(state);
	}

	/**
	 * Determines a state s as final, if it contains an error place and the law is false, OR if there exists at least
	 * one transition in enabled(territory(s)), for which there is no successor in the automaton. In this case, the
	 * successor law must be false.
	 */
	@Override
	public boolean isFinal(final State<L, P> state) {
		final var territory = state.territory();
		final var enabledTransitions = territory.getEnabledTransitions(mNet).collect(Collectors.toSet());
		for (final Transition<L, P> transition : enabledTransitions) {
			final var succ = internalSuccessors(state, transition);
			if (!succ.iterator().hasNext()) {
				assert SmtUtils.isFalseLiteral(getSuccessorLaw(state.law, transition).getFormula())
						: "There is no successor, but the law is not false";
				return true;
			}
		}
		return false;
	}

	@Override
	public int size() {
		return -1;
	}

	@Override
	public String sizeInformation() {
		return "unknown size";
	}

	@Override
	public Set<Transition<L, P>> lettersInternal(final State<L, P> state) {
		// TODO Consider whether we can efficiently override this method
		return IEmpire.super.lettersInternal(state);
	}

	@Override
	public Iterable<OutgoingInternalTransition<Transition<L, P>, State<L, P>>>
			internalSuccessors(final State<L, P> state, final Transition<L, P> letter) {
		// step 1: see if letter should lead to any successor at all or can be optimized away
		// (iterate over alphabet and see which other transitions are enabled in the territory)
		if (!state.territory().enables(letter)) {
			return List.of();
		}
		if (isExtendingTransition(state.law(), letter) && isCycle(state, letter)) {
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

	private State<L, P> extendAll(final State<L, P> state, final Set<Transition<L, P>> transitions) {
		if (transitions.isEmpty()) {
			return state;
		}
		final var territory = state.territory;
		final var territoryRegions = new HashSet<>(territory.getRegions());
		final var extendedRegions = new HashSet<ConnectedRegion<L, P>>();
		for (final ConnectedRegion<L, P> region : territory.getRegions()) {
			final var matchingTransitions = findMatchingTransitions(region, transitions);
			if (!matchingTransitions.isEmpty()) {
				transitions.removeAll(matchingTransitions);
				final var successorPlaces = matchingTransitions.stream().flatMap(t -> t.getSuccessors().stream())
						.collect(Collectors.toSet());
				final var newPlaces = DataStructureUtils.union(region.getPlaces(), successorPlaces);
				final var newTransitions = DataStructureUtils.union(region.getTransitions(), matchingTransitions);
				extendedRegions.add(new ConnectedRegion<>(ImmutableSet.of(newPlaces), ImmutableSet.of(newTransitions)));
				territoryRegions.remove(region);
			}
		}
		final var newTerritory =
				new Territory<>(ImmutableSet.of(DataStructureUtils.union(extendedRegions, territoryRegions)));
		return new State<>(newTerritory, state.law, state.bystanders);
	}

	private Set<Transition<L, P>> findMatchingTransitions(final ConnectedRegion<L, P> region,
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
		return state.territory().getEnabledTransitions(mNet)
				.filter(transition -> !SmtUtils.isFalseLiteral(getSuccessorLaw(state.law(), transition).getFormula()))
				.collect(Collectors.toSet());
	}

	private IPredicate getSuccessorLaw(final IPredicate law, final Transition<L, P> transition) {
		final var succLaw = mProof.internalSuccessors(law, transition.getSymbol());
		if (succLaw.iterator().hasNext()) {
			return DataStructureUtils.getOneAndOnly(succLaw, "successor state").getSucc();
		}

		// TODO Shouldn't we rather throw an error here?
		mLogger.warn("No successor law for transition: %s and law: %s", transition, law);
		return law;
	}

	private boolean isExtendingTransition(final IPredicate lawPlace, final Transition<L, P> transition) {
		final IPredicate newLawPlace = getSuccessorLaw(lawPlace, transition);
		final var predecessors = transition.getPredecessors();
		final var successors = transition.getSuccessors();
		return lawPlace == newLawPlace && predecessors.size() == 1 && successors.size() == 1;
	}

	private Set<Transition<L, P>> getExtendingTransitions(final State<L, P> state,
			final Set<Transition<L, P>> transitions) {
		return transitions.stream().filter(transition -> isExtendingTransition(state.law, transition))
				.collect(Collectors.toSet());
	}

	private boolean isNecessaryBridge(final State<L, P> state, final Transition<L, P> transition) {
		return !state.territory.getBystanders(transition).containsAll(state.bystanders);
	}

	private Set<Transition<L, P>> getUnnecessaryTransitions(final State<L, P> state,
			final Set<Transition<L, P>> transitions) {
		final var extending = getExtendingTransitions(state, transitions);
		return extending.stream().filter(t -> !isNecessaryBridge(state, t)).collect(Collectors.toSet());
	}

	private boolean isCycle(final State<L, P> state, final Transition<L, P> transition) {
		final var territory = state.territory;
		final var law = state.law;
		if (!territory.enables(transition) || !isExtendingTransition(law, transition)) {
			return false;
		}
		return territory.getPlaces().containsAll(transition.getSuccessors());
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
		final IPredicate newLawPlace = getSuccessorLaw(state.law(), transition);
		final Set<ConnectedRegion<L, P>> newBystanders = state.territory().getBystanders(transition);
		final var regions = replaceRegions(transition, newBystanders);
		final var newTerritory = new Territory<>(ImmutableSet.of(regions));
		return new State<>(newTerritory, newLawPlace, newBystanders);
	}

	private Set<ConnectedRegion<L, P>> replaceRegions(final Transition<L, P> transition,
			final Set<ConnectedRegion<L, P>> bystanders) {
		final var regions = new HashSet<>(bystanders);
		for (final var succ : transition.getSuccessors()) {
			regions.add(ConnectedRegion.connectedSingleton(succ));
		}
		return regions;
	}

	private ImmutableSet<ConnectedRegion<L, P>> getInitialRegions() {
		final Set<ConnectedRegion<L, P>> regions = new HashSet<>();
		for (final P place : mNet.getInitialPlaces()) {
			regions.add(ConnectedRegion.connectedSingleton(place));
		}
		return ImmutableSet.of(regions);
	}

	// TODO use ImmutableSet for bystanders
	public record State<L, P>(Territory<P, ConnectedRegion<L, P>> territory, IPredicate law,
			Set<ConnectedRegion<L, P>> bystanders, int hash) {
		// Convenience constructor that computes the correct hash code. Always use this constructor.
		public State(final Territory<P, ConnectedRegion<L, P>> territory, final IPredicate law,
				final Set<ConnectedRegion<L, P>> bystanders) {
			this(territory, law, bystanders, Objects.hash(territory, law, bystanders));
		}

		@Override
		public int hashCode() {
			// Hash code is cached for performance.
			// TODO This caching is brittle, as accidental constructor misuse can lead to incorrect hash codes.
			// TODO Re-evaluate the impact other implementation details have been improved, and improve or remove it.
			return hash;
		}
	}
}
