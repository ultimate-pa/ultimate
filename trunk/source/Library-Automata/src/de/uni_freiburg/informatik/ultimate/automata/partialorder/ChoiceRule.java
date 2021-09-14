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

import de.uni_freiburg.informatik.ultimate.automata.partialorder.CachedIndependenceRelation.IIndependenceCache;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
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
	private final Map<ITransition<L, P>, List<ITransition<L, P>>> mCompositions = new HashMap<>();

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
	public ChoiceRule(final LiptonReductionStatisticsGenerator statistics, final BoundedPetriNet<L, P> net,
			final CoenabledRelation<L, P> coenabledRelation, final ICompositionFactory<L> compositionFactory,
			final IIndependenceCache<?, L> independenceCache) {
		super(statistics, net, coenabledRelation, compositionFactory, independenceCache);
	}

	@Override
	protected void applyInternal(final IPetriNet<L, P> net) {
		final Set<Pair<L, List<ITransition<L, P>>>> pendingCompositions = findCompositions(net);

		for (final Pair<L, List<ITransition<L, P>>> pair : pendingCompositions) {
			final L composedLetter = pair.getFirst();
			final List<ITransition<L, P>> components = pair.getSecond();
			final ITransition<L, P> firstComponent = components.get(0);

			// add composed transition
			final ITransition<L, P> composed = addTransition(composedLetter, net.getPredecessors(firstComponent),
					net.getSuccessors(firstComponent));
			assert components.stream().allMatch(x -> mCoenabledRelation.getImage(x).equals(mCoenabledRelation
					.getImage(firstComponent))) : "parallel letters with different coenabled transitions";
			mCoenabledRelation.copyRelationships(firstComponent, composed);

			// remove obsolete transitions
			for (final ITransition<L, P> component : components) {
				removeTransition(component);
				mCoenabledRelation.deleteElement(component);
			}

			// add mover information for composition
			transferMoverProperties(composedLetter,
					components.stream().map(ITransition::getSymbol).collect(Collectors.toList()));

			mStatistics.reportComposition(LiptonReductionStatisticsDefinitions.ChoiceCompositions);
			mCompositions.put(composed, components);
		}
	}

	private Set<Pair<L, List<ITransition<L, P>>>> findCompositions(final IPetriNet<L, P> net) {
		final NestedMap2<Set<P>, Set<P>, List<ITransition<L, P>>> groupedTransitions = new NestedMap2<>();
		for (final ITransition<L, P> transition : net.getTransitions()) {
			final List<ITransition<L, P>> group = groupedTransitions.computeIfAbsent(net.getPredecessors(transition),
					net.getSuccessors(transition), (x, y) -> new ArrayList<>());
			group.add(transition);
		}

		final Set<Pair<L, List<ITransition<L, P>>>> compositions = new HashSet<>();
		for (final var triple : groupedTransitions.entrySet()) {
			final List<ITransition<L, P>> parallelTransitions = triple.getThird();
			if (parallelTransitions.size() <= 1) {
				continue;
			}

			final List<L> parallelLetters =
					parallelTransitions.stream().map(ITransition::getSymbol).collect(Collectors.toList());
			if (!mCompositionFactory.isParallelyComposable(parallelLetters)) {
				continue;
			}

			final L composedLetter = mCompositionFactory.composeParallel(parallelLetters);
			compositions.add(new Pair<>(composedLetter, parallelTransitions));
		}
		return compositions;
	}

	public Map<ITransition<L, P>, List<ITransition<L, P>>> getCompositions() {
		return mCompositions;
	}
}
