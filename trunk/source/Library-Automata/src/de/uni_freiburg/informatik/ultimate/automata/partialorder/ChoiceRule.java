/*
 * Copyright (C) 2019 Elisabeth Schanno
 * Copyright (C) 2019 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2019-2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2019-2021 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.partialorder;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.CachedIndependenceRelation.IIndependenceCache;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Implements the choice rule for {@link LiptonReduction}: "Parallel" transitions in a Petri net, i.e., transitions with
 * the same predecessor places and the same successor places, are composed.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of letters in the Petri net
 * @param <P>
 *            The type of places in the Petri net
 */
public class ChoiceRule<L, P> extends ReductionRule<L, P> {
	private final ICompositionFactory<L> mCompositionFactory;
	private final Map<Transition<L, P>, List<Transition<L, P>>> mCompositions = new HashMap<>();

	/**
	 * Creates a new instance of the rule.
	 *
	 * @param statistics
	 *            Used to collect statistics about the reduction.
	 * @param net
	 *            The Petri net to which the rule should be applied.
	 * @param coenabledRelation
	 *            The coenabled relation between transitions of the given net
	 * @param compositionFactory
	 *            A composition factory used to combine letters
	 * @param independenceCache
	 *            Optionally, cached independence information. When letters are composed, their independence information
	 *            stored in the cache is combined for the composed letter.
	 */
	public ChoiceRule(final AutomataLibraryServices services, final LiptonReductionStatisticsGenerator statistics,
			final BoundedPetriNet<L, P> net, final CoenabledRelation<L, P> coenabledRelation,
			final ICompositionFactory<L> compositionFactory, final IIndependenceCache<?, L> independenceCache) {
		super(services, statistics, net, coenabledRelation, independenceCache);
		mCompositionFactory = compositionFactory;
	}

	@Override
	protected void applyInternal(final IPetriNet<L, P> net) {
		final Set<Pair<L, List<Transition<L, P>>>> pendingCompositions = findCompositions(net);

		for (final Pair<L, List<Transition<L, P>>> pair : pendingCompositions) {
			final L composedLetter = pair.getFirst();
			final List<Transition<L, P>> components = pair.getSecond();
			final Transition<L, P> firstComponent = components.get(0);

			// add composed transition
			final Transition<L, P> composed =
					addTransition(composedLetter, firstComponent.getPredecessors(), firstComponent.getSuccessors());

			// remove obsolete transitions
			for (final Transition<L, P> component : components) {
				removeTransition(component);
				mCoenabledRelation.removeElement(component);
			}

			// update coenabled relation
			assert components.stream().allMatch(x -> mCoenabledRelation.getImage(x).equals(mCoenabledRelation
					.getImage(firstComponent))) : "parallel letters with different coenabled transitions";
			mCoenabledRelation.copyRelationships(firstComponent, composed);

			// add mover information for composition
			transferMoverProperties(composedLetter,
					components.stream().map(Transition::getSymbol).collect(Collectors.toList()));

			mStatistics.reportComposition(LiptonReductionStatisticsDefinitions.ChoiceCompositions);
			mCompositions.put(composed, components);
		}

		pruneAlphabet();
	}

	private Set<Pair<L, List<Transition<L, P>>>> findCompositions(final IPetriNet<L, P> net) {
		final NestedMap2<Set<P>, Set<P>, List<Transition<L, P>>> groupedTransitions = new NestedMap2<>();
		for (final Transition<L, P> transition : net.getTransitions()) {
			final List<Transition<L, P>> group = groupedTransitions.computeIfAbsent(transition.getPredecessors(),
					transition.getSuccessors(), (x, y) -> new ArrayList<>());
			group.add(transition);
		}

		final Set<Pair<L, List<Transition<L, P>>>> compositions = new HashSet<>();
		for (final var triple : groupedTransitions.entrySet()) {
			final List<Transition<L, P>> parallelTransitions = triple.getThird();
			if (parallelTransitions.size() <= 1) {
				continue;
			}

			final List<L> parallelLetters =
					parallelTransitions.stream().map(Transition::getSymbol).collect(Collectors.toList());
			if (!mCompositionFactory.isParallelyComposable(parallelLetters)) {
				continue;
			}

			final L composedLetter = mCompositionFactory.composeParallel(parallelLetters);
			compositions.add(new Pair<>(composedLetter, parallelTransitions));
		}
		return compositions;
	}

	public Map<Transition<L, P>, List<Transition<L, P>>> getCompositions() {
		return mCompositions;
	}
}
