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

import java.util.ArrayDeque;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashSet;
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
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * This class computes the <em>saturated empire</em> as defined in our paper:
 *
 * The Ghosts of Empires: Extracting Modularity from Interleaving-Based Proofs. Schüssele, Zumkeller, Lagunes-Rochin and
 * Klumpp, POPL'26
 *
 * See {@link IEmpire} for the general concept of empires. As of now (August 2026), this implementation represents our
 * best algorithm for the construction of compact empires.
 *
 * @param <L>
 *            The type of letters in the empire (and the Petri program for which an empire is computed)
 * @param <P>
 *            The type of places in the Petri program for which an empire is computed
 */
public class SaturatedEmpire<L, P> implements IEmpire<L, P, SaturatedEmpire.State<L, P>> {
	private final ILogger mLogger;

	private final IPetriNet<L, P> mProgram;
	private final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> mInterpolantAutomaton;

	private final State<L, P> mInitialState;

	/**
	 * Create a new instance of a saturated empire. The actual computation will be performed on-demand as the empire is
	 * explored.
	 *
	 * @param program
	 *            The Petri program for which to compute an empire
	 * @param interpolantAutomaton
	 *            An interpolant automaton which proves all traces of the Petri program infeasible
	 */
	public SaturatedEmpire(final IUltimateServiceProvider services, final IPetriNet<L, P> program,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> interpolantAutomaton) {
		mLogger = services.getLoggingService().getLogger(getClass());
		mProgram = program;
		mInterpolantAutomaton = interpolantAutomaton;

		// Construct initial state
		final var initialLaw =
				DataStructureUtils.getOneAndOnly(mInterpolantAutomaton.getInitialStates(), "initial law place");
		final var regions =
				mProgram.getInitialPlaces().stream().map(Region::singleton).collect(ImmutableSet.collector());
		final State<L, P> state = new State<>(new Territory<>(regions), initialLaw);
		mInitialState = getMarkedSuccessor(state, Collections.emptySet());
	}

	@Override
	public IPredicate getLaw(final State<L, P> state) {
		return state.law();
	}

	@Override
	public Territory<P, Region<P>> getTerritory(final State<L, P> state) {
		return state.territory();
	}

	@Override
	public VpAlphabet<Transition<L, P>> getVpAlphabet() {
		return new VpAlphabet<>(mProgram.getTransitions());
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
	public boolean isFinal2(final State<L, P> state) {
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
		final var enabledTransitions = territory.getEnabledTransitions(mProgram).collect(Collectors.toSet());
		if (succStates.size() < enabledTransitions.size()) {
			final var falseSuccessors = enabledTransitions.stream()
					.anyMatch(t -> mInterpolantAutomaton.isFinal(getSuccessorLaw(state.law, t)));
			if (!falseSuccessors) {
				mLogger.debug("Bla");
			}
			assert falseSuccessors
					: "There exists no successor for an enabled transition, but the successor law is not false";
		}
		// Check if there is at least one enabled transition, for which state has no successor
		return succStates.size() < enabledTransitions.size();
	}

	/**
	 * Determines a state s as final, if it contains an error place and the law is false, OR if there exists at least
	 * one transition in enabled(territory(s)), for which there is no successor in the automaton. In this case, the
	 * successor law must be false.
	 */
	@Override
	public boolean isFinal(final State<L, P> state) {
		final var territory = state.territory();
		final var enabledTransitions = territory.getEnabledTransitions(mProgram).collect(Collectors.toSet());
		for (final Transition<L, P> transition : enabledTransitions) {
			final var succ = internalSuccessors(state, transition);
			if (!succ.iterator().hasNext()) {
				assert mInterpolantAutomaton.isFinal(getSuccessorLaw(state.law, transition))
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
		final var places = state.territory().getPlaces();
		return mProgram.getSuccessorTransitionProviders(places, places).stream()
				.flatMap(p -> p.getTransitions().stream()).collect(Collectors.toSet());
	}

	@Override
	public Iterable<OutgoingInternalTransition<Transition<L, P>, State<L, P>>>
			internalSuccessors(final State<L, P> state, final Transition<L, P> letter) {
		// step 1: see if letter should lead to any successor at all or can be optimized away
		// (iterate over alphabet and see which other transitions are enabled in the territory)
		if (!state.territory().enables(letter)) {
			return List.of();
		}

		// compute successor law once and pass it to other methods, to improve performance
		final IPredicate successorLaw = getSuccessorLaw(state.law(), letter);
		if (isExtendingTransition(state.law(), letter, successorLaw) && isCycle(state, letter, successorLaw)) {
			return List.of(new OutgoingInternalTransition<>(letter, state));
		}

		// step 2: compute the "direct" successor state for the given transition
		if (mInterpolantAutomaton.isFinal(successorLaw)) {
			return List.of();
		}
		final var directSucc = getReplacementSuccessor(state, letter, successorLaw);
		final var succState = directSucc.getFirst();
		final var replacementBystanders = directSucc.getSecond();

		// step 3: while the current successor is not marked, pick one (or a set of) transitions and compute the
		// successor again
		final var maxMarkedSuccessor = getMarkedSuccessor(succState, replacementBystanders);

		// return the edge to the maximal successor
		return List.of(new OutgoingInternalTransition<>(letter, maxMarkedSuccessor));
	}

	private IPredicate getSuccessorLaw(final IPredicate law, final Transition<L, P> transition) {
		final var succLaw = mInterpolantAutomaton.internalSuccessors(law, transition.getSymbol());
		if (succLaw.iterator().hasNext()) {
			return DataStructureUtils.getOneAndOnly(succLaw, "successor state").getSucc();
		}

		// TODO Shouldn't we rather throw an error here?
		mLogger.warn("No successor law for transition: %s and law: %s", transition, law);
		return law;
	}

	private boolean isExtendingTransition(final IPredicate currentLaw, final Transition<L, P> transition,
			final IPredicate successorLaw) {
		return currentLaw == successorLaw && isStraightline(transition);
	}

	private boolean isCycle(final State<L, P> state, final Transition<L, P> transition, final IPredicate successorLaw) {
		final var territory = state.territory();
		final var law = state.law();
		return territory.enables(transition) && isExtendingTransition(law, transition, successorLaw)
				&& territory.getPlaces().containsAll(transition.getSuccessors());
	}

	private State<L, P> getMarkedSuccessor(final State<L, P> state, final Set<Region<P>> replacementBystanders) {
		final var newRegions = new LinkedHashSet<Region<P>>(state.territory().size());
		boolean changed = false;
		for (final var region : state.territory().getRegions()) {
			if (replacementBystanders.contains(region)) {
				// Bystanders must remain unchanged.
				newRegions.add(region);
			} else {
				// Extend the region as far as possible.
				final var extendedRegion = extendRegion(state, region, replacementBystanders);
				newRegions.add(extendedRegion);

				// Record whether any region truly changed.
				changed |= extendedRegion != region;
			}
		}
		if (changed) {
			final var extendedTerritory = new Territory<>(ImmutableSet.of(newRegions));
			return new State<>(extendedTerritory, state.law());
		}
		return state;
	}

	private Region<P> extendRegion(final State<L, P> state, final Region<P> region,
			final Set<Region<P>> replacementBystanders) {
		final ArrayDeque<Transition<L, P>> worklist = new ArrayDeque<>();
		for (final var provider : mProgram.getSuccessorTransitionProviders(region.getPlaces(), region.getPlaces())) {
			worklist.addAll(provider.getTransitions());
		}

		final Set<P> addedPlaces = new HashSet<>();
		while (!worklist.isEmpty()) {
			final var transition = worklist.pop();
			if (!isStraightline(transition) || getSuccessorLaw(state.law(), transition) != state.law()) {
				// A new territory must be created for this transition.
				continue;
			}

			// As the transition is straightline, it has exactly one predecessor and successor.
			final P predecessor = DataStructureUtils.getOneAndOnly(transition.getPredecessors(), "predecessor");
			final P successor = DataStructureUtils.getOneAndOnly(transition.getSuccessors(), "successor");

			// Invariant: The transition must be enabled; and it cannot touch a bystander region.
			assert region.contains(predecessor) || addedPlaces.contains(predecessor);
			assert replacementBystanders.stream().noneMatch(r -> r.contains(predecessor));
			assert replacementBystanders.stream().noneMatch(r -> r.contains(successor));

			if (region.contains(successor) || addedPlaces.contains(successor)) {
				// The transition is already cycling, so there is no need to extend by it again.
				continue;
			}
			assert !state.territory().containsPlace(successor) : "violation of 1-safety";

			// The successor is added to the region. Any outgoing transitions become candidates for extension.
			addedPlaces.add(successor);
			worklist.addAll(mProgram.getSuccessors(successor));
		}

		if (addedPlaces.isEmpty()) {
			return region;
		}

		final var newPlaceSet = DataStructureUtils.union(region.getPlaces(), addedPlaces);
		return new Region<>(ImmutableSet.of(newPlaceSet));
	}

	private boolean isStraightline(final Transition<L, P> transition) {
		return transition.getPredecessors().size() == 1 && transition.getSuccessors().size() == 1;
	}

	private Pair<State<L, P>, Set<Region<P>>> getReplacementSuccessor(final State<L, P> state,
			final Transition<L, P> transition, final IPredicate successorLaw) {
		final Set<Region<P>> newBystanders = state.territory().getBystanders(transition);
		final var regions = replaceRegions(transition, newBystanders);
		final var newTerritory = new Territory<>(ImmutableSet.of(regions));
		final var replacementState = new State<L, P>(newTerritory, successorLaw);
		return new Pair<>(replacementState, newBystanders);
	}

	private Set<Region<P>> replaceRegions(final Transition<L, P> transition,
			final Set<Region<P>> replacementBystanders) {
		final var regions = new HashSet<>(replacementBystanders);
		for (final var succ : transition.getSuccessors()) {
			regions.add(Region.singleton(succ));
		}
		return regions;
	}

	public record State<L, P>(Territory<P, Region<P>> territory, IPredicate law, int hash) {
		// Convenience constructor that computes the correct hash code. Always use this constructor.
		public State(final Territory<P, Region<P>> territory, final IPredicate law) {
			this(territory, law, Objects.hash(territory, law));
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
