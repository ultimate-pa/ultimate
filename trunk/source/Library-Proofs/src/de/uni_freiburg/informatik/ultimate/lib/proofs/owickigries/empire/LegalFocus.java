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
package de.uni_freiburg.informatik.ultimate.lib.proofs.owickigries.empire;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateWithConjuncts;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class LegalFocus<S, L, P> implements ILegalFocusFunction<S, P> {
	private final IPetriNet<L, P> mProgram;
	private final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> mInterpolantAutomaton;
	private final IExplicitEmpire<L, P, S> mEmpire;

	private final int mNumLaws;
	private final Function<IPredicate, List<IPredicate>> mSplitConjuncts;
	private final IFocusedRegionHeuristic<P> mHeuristic;

	private final HashRelation<Pair<S, Integer>, Region<P>> mLegalFocus;

	public LegalFocus(final IExplicitEmpire<L, P, S> empire, final IPetriNet<L, P> net,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> interpolantAutomaton, final int numLaws,
			final Function<IPredicate, List<IPredicate>> splitConjuncts) {
		this(empire, net, interpolantAutomaton, numLaws, splitConjuncts,
				IFocusedRegionHeuristic.bySizeExcludingAuxilliaryPlaces());
	}

	public LegalFocus(final IExplicitEmpire<L, P, S> empire, final IPetriNet<L, P> program,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> interpolantAutomaton, final int numLaws,
			final Function<IPredicate, List<IPredicate>> splitConjuncts, final IFocusedRegionHeuristic<P> heuristic) {
		mProgram = program;
		mInterpolantAutomaton = interpolantAutomaton;
		mEmpire = empire;

		mNumLaws = numLaws;
		mSplitConjuncts = Objects.requireNonNull(splitConjuncts);
		mHeuristic = heuristic;

		mLegalFocus = computeLegalFocus();
	}

	private HashRelation<Pair<S, Integer>, Region<P>> computeLegalFocus() {
		// Begin the focus computation with states that enable transitions that would lead to "false".
		// (Rule: inductive-false)
		final var focus = computeFinalStateFocus(mEmpire.getFinalStates());

		// Perform a backwards-BFS to propagate focus.
		// (Rules: inductive-edge, bystanders)
		final var queue = new ArrayDeque<>(focus.getDomain());
		while (!queue.isEmpty()) {
			final var entry = queue.poll();
			final var state = entry.getFirst();
			final int index = entry.getSecond();

			final var predecessors = mEmpire.internalPredecessors(state);

			for (final IncomingInternalTransition<Transition<L, P>, S> edge : predecessors) {
				final var laws = mSplitConjuncts.apply(mEmpire.getLaw(edge.getPred()));

				final boolean modified = propagateFocus(state, edge, focus, index, laws);
				if (modified) {
					queue.offer(new Pair<>(edge.getPred(), index));
				}
			}
		}
		return focus;
	}

	// returns true if the focus was modified, false otherwise
	private boolean propagateFocus(final S state, final IncomingInternalTransition<Transition<L, P>, S> edge,
			final HashRelation<Pair<S, Integer>, Region<P>> focus, final int lawIndex,
			final List<IPredicate> predecessorLaws) {
		final var currentFocus = focus.getImage(new Pair<>(state, lawIndex));
		if (currentFocus.isEmpty()) {
			// Nothing to propagate
			return false;
		}

		final var predecessor = edge.getPred();
		final var predecessorPair = new Pair<>(predecessor, lawIndex);
		final var focusedRegions = chooseFocusedRegions(predecessor, currentFocus, edge.getLetter(),
				predecessorLaws.get(lawIndex), focus.getImage(predecessorPair));
		return focus.addAllPairs(predecessorPair, focusedRegions);
	}

	private Set<Region<P>> chooseFocusedRegions(final S predecessor, final Set<Region<P>> successorFocus,
			final Transition<L, P> transition, final IPredicate predecessorLaw, final Set<Region<P>> predecessorFocus) {
		final var territory = mEmpire.getTerritory(predecessor);

		// Any bystanders that are in focus after the transition must already be in focus before the transition.
		// (Rule: bystanders)
		final var bystanders = territory.getBystanders(transition);
		final var focusedBystanders = DataStructureUtils.intersection(bystanders, successorFocus);

		if (successorFocus.size() == focusedBystanders.size()) {
			// Only bystanders are focused; we can skip the application of the inductive-edge rule (rest of the method).
			return focusedBystanders;
		}

		// At this point, we know that at least one successor region of the transition is focused.
		// Hence, at least one predecessor region of the transition must also be focused.
		// (Rule: inductive-edge)
		final var predecessorRegions = territory.getPlacesRegions(transition.getPredecessors());

		assert !predecessorRegions.isEmpty() : "territory enables transition but has no predecessor regions";

		final boolean alreadyFocused = predecessorRegions.stream().anyMatch(predecessorFocus::contains);
		if (alreadyFocused) {
			// No need to add any predecessor regions to the focus, they are already there.
			return focusedBystanders;
		}

		final var focused = new HashSet<>(focusedBystanders);
		focused.add(chooseBestRegion(predecessorRegions, predecessorLaw));
		return focused;
	}

	// When a state's territory enables a transition but the state has no outgoing edge for it, some of the conjuncts
	// must go to "false" after the transition. For at least one such conjunct, at least one predecessor region of the
	// transition must be focused.
	// (Rule: inductive-false)
	private HashRelation<Pair<S, Integer>, Region<P>> computeFinalStateFocus(final Collection<S> finalStates) {
		final var focus = new HashRelation<Pair<S, Integer>, Region<P>>();
		for (final S state : finalStates) {
			final var territory = mEmpire.getTerritory(state);
			final var enabledTransitions = territory.getEnabledTransitions(mProgram);
			final var successorlessTransitions =
					enabledTransitions.filter(t -> !mEmpire.internalSuccessors(state, t).iterator().hasNext())
							.collect(Collectors.toList());
			for (final Transition<L, P> transition : successorlessTransitions) {
				final var predecessorRegions = territory.getPlacesRegions(transition.getPredecessors());
				assert !predecessorRegions.isEmpty() : "territory enables transition but has no predecessor regions";

				final var successorLawList = getSuccessorLaw(mEmpire.getLaw(state), transition);
				final var falseSuccessors = getFalseSuccessors(successorLawList);

				// Check if for any law index leading to false, a predecessor region is already focused.
				// If so, nothing else needs to be done.
				final boolean alreadyFocused = falseSuccessors.stream().anyMatch(i -> DataStructureUtils
						.haveNonEmptyIntersection(predecessorRegions, focus.getImage(new Pair<>(state, i))));
				if (alreadyFocused) {
					continue;
				}

				// Otherwise, for at least one law index leading to false, a predecessor region must be focused.
				// Choose the best law index and region according to a heuristic.
				final var predecessorLaws = mSplitConjuncts.apply(mEmpire.getLaw(state));
				final Comparator<IndexAndRegion<P>> comparator = Comparator.comparing(
						// map (index, region) to (region, law) pairs
						indexAndRegion -> new Pair<>(indexAndRegion.region(),
								predecessorLaws.get(indexAndRegion.lawIndex())),
						// compare (region, law) pairs according to our heuristic
						mHeuristic.getPreference());
				final IndexAndRegion<P> bestIndexAndRegion = falseSuccessors.stream()
						.flatMap(i -> predecessorRegions.stream().map(r -> new IndexAndRegion<>(i, r))).min(comparator)
						.orElseThrow();
				focus.addPair(new Pair<>(state, bestIndexAndRegion.lawIndex()), bestIndexAndRegion.region());
			}
		}
		return focus;
	}

	private record IndexAndRegion<P>(int lawIndex, Region<P> region) {
		// small helper record
	}

	private Region<P> chooseBestRegion(final Set<Region<P>> possibleRegions, final IPredicate law) {
		assert !possibleRegions.isEmpty() : "cannot choose best region from empty set";

		// Heuristically choose the best predecessor region to focus.
		final var minRegion = possibleRegions.stream().min(mHeuristic.getPreference(law));
		assert minRegion.isPresent() : "could not find best region";

		return minRegion.orElseThrow();
	}

	private List<IPredicate> getSuccessorLaw(final IPredicate law, final Transition<L, P> transition) {
		final var succLaw = mInterpolantAutomaton.internalSuccessors(law, transition.getSymbol());
		return mSplitConjuncts.apply(DataStructureUtils.getOneAndOnly(succLaw, "successor state").getSucc());
	}

	private List<Integer> getFalseSuccessors(final List<IPredicate> successorLaws) {
		return IntStream.range(0, mNumLaws).filter(i -> isFalseLiteral(successorLaws.get(i))).mapToObj(Integer::valueOf)
				.collect(Collectors.toList());
	}

	public Set<Region<P>> getLegalFocus(final S state, final int lawIndex) {
		return mLegalFocus.getImage(new Pair<>(state, lawIndex));
	}

	public boolean isFocused(final P place, final S state, final int lawIndex) {
		final var legalFocus = getLegalFocus(state, lawIndex);
		return legalFocus.stream().anyMatch(r -> r.contains(place));
	}

	@Override
	public List<IPredicate> getFocusedLaws(final S state, final Region<P> region) {
		final List<IPredicate> focusedLaws = new ArrayList<>();
		final var laws = mSplitConjuncts.apply(mEmpire.getLaw(state));
		for (int i = 0; i < mNumLaws; i++) {
			final var focus = getLegalFocus(state, i);
			if (focus.contains(region)) {
				final var law = laws.get(i);
				if (law instanceof final PredicateWithConjuncts conjunction) {
					focusedLaws.addAll(conjunction.getConjuncts());
				} else {
					focusedLaws.add(law);
				}
			}
		}
		return focusedLaws;
	}

	private boolean isFalseLiteral(final IPredicate predicate) {
		if (predicate instanceof final PredicateWithConjuncts conjunction) {
			return conjunction.getConjuncts().stream().anyMatch(this::isFalseLiteral);
		}
		return SmtUtils.isFalseLiteral(predicate.getFormula());
	}

	public interface IFocusedRegionHeuristic<P> {
		Comparator<Pair<Region<P>, IPredicate>> getPreference();

		default Comparator<Region<P>> getPreference(final IPredicate law) {
			final var comparator = getPreference();
			return (r1, r2) -> comparator.compare(new Pair<>(r1, law), new Pair<>(r2, law));
		}

		static <P> IFocusedRegionHeuristic<P> bySize() {
			return new IFocusedRegionHeuristic<>() {
				@Override
				public Comparator<Pair<Region<P>, IPredicate>> getPreference() {
					return Comparator.comparing(Pair::getFirst, Comparator.comparing(Region::size));
				}

				@Override
				public Comparator<Region<P>> getPreference(final IPredicate law) {
					return Comparator.comparing(Region::size);
				}
			};
		}

		static <P> IFocusedRegionHeuristic<P> bySizeExcludingAuxilliaryPlaces() {
			return new IFocusedRegionHeuristic<>() {
				@Override
				public Comparator<Pair<Region<P>, IPredicate>> getPreference() {
					return Comparator.comparing(Pair::getFirst, Comparator.comparing(this::containsNotOnlyISLPredicate)
							.thenComparing(Comparator.comparing(Region::size)));
				}

				@Override
				public Comparator<Region<P>> getPreference(final IPredicate law) {
					return Comparator.comparing(this::containsNotOnlyISLPredicate)
							.thenComparing(Comparator.comparing(Region::size));
				}

				private boolean containsNotOnlyISLPredicate(final Region<P> region) {
					return region.getPlaces().stream().anyMatch(p -> !(p instanceof ISLPredicate));
				}
			};
		}
	}
}
