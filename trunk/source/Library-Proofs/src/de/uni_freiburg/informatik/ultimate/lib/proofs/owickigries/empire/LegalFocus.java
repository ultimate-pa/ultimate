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
import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class LegalFocus<S, L, P> implements ILegalFocusFunction<S, P> {
	private final IPetriNet<L, P> mNet;
	private final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> mInterpolantAutomaton;
	private final IExplicitEmpireAutomaton<L, P, S> mEmpire;
	private final Function<IPredicate, List<IPredicate>> mSplitConjuncts;

	private final HashRelation<Pair<S, Integer>, Region<P>> mLegalFocus;
	private final int mNumLaws;

	public LegalFocus(final IUltimateServiceProvider services, final IEmpireAutomaton<L, P, S> empire,
			final IPetriNet<L, P> net,
			final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> interpolantAutomaton, final int numLaws,
			final Function<IPredicate, List<IPredicate>> splitConjuncts) {
		mNet = net;
		mInterpolantAutomaton = interpolantAutomaton;
		mNumLaws = numLaws;
		mSplitConjuncts = Objects.requireNonNull(splitConjuncts);

		if (empire instanceof final IExplicitEmpireAutomaton<L, P, S> explicitEmpire) {
			mEmpire = explicitEmpire;
		} else {
			mEmpire = new EmpireReachableStates<>(services, empire);
		}

		mLegalFocus = computeLegalFocus();
	}

	private HashRelation<Pair<S, Integer>, Region<P>> computeLegalFocus() {
		final var finalStates = mEmpire.getFinalStates().stream().collect(Collectors.toSet());
		final var queue = new ArrayDeque<S>();
		final var focus = computeFinalStateFocus(finalStates);
		for (final S state : finalStates) {
			queue.offer(state);
		}
		while (!queue.isEmpty()) {
			final var state = queue.poll();
			for (int i = 0; i < mNumLaws; i++) {
				final var j = i;
				final var currentFocus = focus.getImage(new Pair<>(state, j));
				if (currentFocus.isEmpty()) {
					continue;
				}
				final var predecessors = mEmpire.internalPredecessors(state);
				for (final IncomingInternalTransition<Transition<L, P>, S> incomingInternalTransition : predecessors) {
					final var predecessor = incomingInternalTransition.getPred();
					final var predecessorPair = new Pair<>(predecessor, j);
					final var transition = incomingInternalTransition.getLetter();
					final var focusedRegions =
							getFocusedRegions(predecessor, currentFocus, transition, focus.getImage(predecessorPair));
					final var added = focus.addAllPairs(predecessorPair, focusedRegions);
					if (added) {
						queue.offer(predecessor);
					}
				}
			}
		}
		return focus;
	}

	private Set<Region<P>> getFocusedRegions(final S predecessor, final Set<Region<P>> successorFocus,
			final Transition<L, P> transition, final Set<Region<P>> predecessorFocus) {
		final var territory = mEmpire.getTerritory(predecessor);
		final var bystanders = territory.getBystanders(transition);
		final var focusedBystanders = DataStructureUtils.intersection(bystanders, successorFocus);
		if (successorFocus.size() == focusedBystanders.size()) {
			return focusedBystanders;
		}

		var mayRegions = territory.getPlacesRegions(transition.getPredecessors());
		assert !mayRegions.isEmpty() : "territory enables transition but has no predecessor regions";

		final var alreadyFocused = DataStructureUtils.intersection(mayRegions, predecessorFocus);
		mayRegions = alreadyFocused.isEmpty() ? mayRegions : alreadyFocused;

		final var minRegion = mayRegions.stream().min(Comparator.comparingInt(Region::size));
		assert minRegion.isPresent() : "could not find best predecessor region";

		final var focused = new HashSet<>(focusedBystanders);
		focused.add(minRegion.orElseThrow());
		return focused;
	}

	private List<IPredicate> getSuccessorLaw(final IPredicate law, final Transition<L, P> transition) {
		final var succLaw = mInterpolantAutomaton.internalSuccessors(law, transition.getSymbol());
		return mSplitConjuncts.apply(DataStructureUtils.getOneAndOnly(succLaw, "successor state").getSucc());
	}

	private HashRelation<Pair<S, Integer>, Region<P>> computeFinalStateFocus(final Set<S> finalStates) {
		final var focus = new HashRelation<Pair<S, Integer>, Region<P>>();
		for (final S state : finalStates) {
			final var territory = mEmpire.getTerritory(state);
			final var enabledTransitions = territory.getEnabledTransitions(mNet);
			final var successorlessTransitions =
					enabledTransitions.filter(t -> !mEmpire.internalSuccessors(state, t).iterator().hasNext())
							.collect(Collectors.toSet());
			for (final Transition<L, P> transition : successorlessTransitions) {
				final var successorLawList = getSuccessorLaw(mEmpire.getLaw(state), transition);
				for (int i = 0; i < mNumLaws; i++) {
					if (!SmtUtils.isFalseLiteral(successorLawList.get(i).getFormula())) {
						continue;
					}
					var mayRegions = territory.getPlacesRegions(transition.getPredecessors());
					assert !mayRegions.isEmpty() : "territory enables transition but has no predecessor regions";

					final var j = i;
					final var alreadyFocused = mayRegions.stream()
							.filter(r -> focus.getImage(new Pair<>(state, j)).contains(r)).collect(Collectors.toSet());
					mayRegions = alreadyFocused.isEmpty() ? mayRegions : alreadyFocused;
					final var minRegion = mayRegions.stream().min(Comparator.comparingInt(Region::size));
					assert minRegion.isPresent() : "could not find best predecessor region";
					focus.addPair(new Pair<>(state, j), minRegion.orElseThrow());
				}
			}
		}
		return focus;
	}

	public Set<Region<P>> getLegalFocus(final S state, final Integer lawIndex) {
		return mLegalFocus.getImage(new Pair<>(state, lawIndex));
	}

	public boolean isFocused(final P place, final S state, final Integer lawIndex) {
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
				focusedLaws.add(laws.get(i));
			}
		}
		return focusedLaws;
	}
}
