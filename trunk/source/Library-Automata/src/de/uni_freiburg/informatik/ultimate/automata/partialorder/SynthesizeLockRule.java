/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
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

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.CachedIndependenceRelation.IIndependenceCache;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * Implements a reduction rule for Petri nets, by synthesizing lock places that prevent a transition from firing while
 * some other place has a token.
 *
 * This rule supplements the sequence rule: It allows to consider loops as atomic, which the sequence rule is unable to
 * do. Where both are applicable, the sequence rule might be preferable. Therefore this rule can be instantiated in such
 * a way that it is only applied if at least one loop is present.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of letters in the Petri net
 * @param <P>
 *            The type of places in the Petri net
 */
public class SynthesizeLockRule<L, P> extends ReductionRule<L, P> {
	private final boolean mRequireLoop;
	private final IIndependenceRelation<Set<P>, L> mIndependence;
	private final ICopyPlaceFactory<P> mPlaceFactory;

	public SynthesizeLockRule(final LiptonReductionStatisticsGenerator statistics, final BoundedPetriNet<L, P> net,
			final CoenabledRelation<L, P> coenabledRelation, final IIndependenceCache<?, L> independenceCache,
			final IIndependenceRelation<Set<P>, L> independence, final ICopyPlaceFactory<P> placeFactory,
			final boolean requireLoop) {
		super(statistics, net, coenabledRelation, independenceCache);
		mIndependence = independence;
		mPlaceFactory = placeFactory;
		mRequireLoop = requireLoop;
	}

	@Override
	protected void applyInternal(final IPetriNet<L, P> net) {
		final Map<P, Set<Transition<L, P>>> compositions = findCompositions(net);
		for (final var entry : compositions.entrySet()) {
			inhibitTransitions(net, entry.getKey(), entry.getValue());
		}
	}

	private void inhibitTransitions(final IPetriNet<L, P> net, final P place, final Set<Transition<L, P>> transitions) {
		// TODO If Lipton is repeatedly applied, a negatedPlace may already exist. Can we find / remember it?
		final P negatedPlace = mPlaceFactory.createFreshPlace();
		addPlace(negatedPlace, !net.getInitialPlaces().contains(place), false);

		for (final var incoming : new HashSet<>(net.getPredecessors(place))) {
			if (incoming.getSuccessors().contains(place)) {
				continue;
			}

			final var pre = new HashSet<>(incoming.getPredecessors());
			pre.add(negatedPlace);
			final var newIncoming = addTransition(incoming.getSymbol(), ImmutableSet.of(pre), incoming.getSuccessors());
			mCoenabledRelation.copyRelationships(incoming, newIncoming);

			removeTransition(incoming);
			mCoenabledRelation.removeElement(incoming);
		}

		for (final var outgoing : new HashSet<>(net.getSuccessors(place))) {
			if (outgoing.getPredecessors().contains(place)) {
				continue;
			}

			final var succ = new HashSet<>(outgoing.getSuccessors());
			succ.add(negatedPlace);
			final var newOutgoing =
					addTransition(outgoing.getSymbol(), outgoing.getPredecessors(), ImmutableSet.of(succ));
			mCoenabledRelation.copyRelationships(outgoing, newOutgoing);

			removeTransition(outgoing);
			mCoenabledRelation.removeElement(outgoing);
		}

		for (final var inhibitable : transitions) {
			final var pre = new HashSet<>(inhibitable.getPredecessors());
			pre.add(negatedPlace);
			final var succ = new HashSet<>(inhibitable.getSuccessors());
			succ.add(negatedPlace);

			final var inhibited = addTransition(inhibitable.getSymbol(), ImmutableSet.of(pre), ImmutableSet.of(succ));
			for (final var coenabled : mCoenabledRelation.getImage(inhibitable)) {
				if (!coenabled.getPredecessors().contains(place)) {
					mCoenabledRelation.addPair(inhibited, coenabled);
				}
			}

			removeTransition(inhibitable);
			mCoenabledRelation.removeElement(inhibitable);
		}
	}

	private Map<P, Set<Transition<L, P>>> findCompositions(final IPetriNet<L, P> net) {
		final Map<P, Set<Transition<L, P>>> result = new HashMap<>();
		final Set<Transition<L, P>> involved = new HashSet<>();

		for (final P place : net.getPlaces()) {
			final Set<Transition<L, P>> incoming = net.getPredecessors(place);
			if (DataStructureUtils.haveNonEmptyIntersection(involved, incoming)) {
				continue;
			}

			final Set<Transition<L, P>> outgoing = net.getSuccessors(place);
			if (DataStructureUtils.haveNonEmptyIntersection(involved, outgoing)) {
				continue;
			}

			if (mRequireLoop && DataStructureUtils.haveEmptyIntersection(incoming, outgoing)) {
				continue;
			}

			boolean isLeftMover = true;
			final Set<Transition<L, P>> inhibitable = new HashSet<>();
			for (final Transition<L, P> trans : outgoing) {
				final Set<Transition<L, P>> coenabled = mCoenabledRelation.getImage(trans);
				isLeftMover = isLeftMover && DataStructureUtils.haveNonEmptyIntersection(involved, coenabled)
						&& coenabled.stream().flatMap(t -> t.getSuccessors().stream()).anyMatch(net::isAccepting)
						&& coenabled.stream().allMatch(t -> checkCommutativity(net, t, trans));

				// TODO If only some co-enabled transitions commute, wouldn't it be sound to only block these?
				if (!isLeftMover) {
					break;
				}
				inhibitable.addAll(coenabled);
			}
			if (!isLeftMover || inhibitable.isEmpty()) {
				continue;
			}

			involved.addAll(inhibitable);
			involved.addAll(incoming);
			involved.addAll(outgoing);
			result.put(place, inhibitable);
		}

		return result;
	}

	private boolean checkCommutativity(final IPetriNet<L, P> net, final Transition<L, P> first,
			final Transition<L, P> second) {
		final Set<P> preconditions;
		if (mIndependence.isConditional()) {
			preconditions = DataStructureUtils.union(first.getPredecessors(), second.getPredecessors());
		} else {
			preconditions = null;
		}
		return mIndependence.contains(preconditions, first.getSymbol(), second.getSymbol());
	}
}
