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

import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.CachedIndependenceRelation.IIndependenceCache;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.IPetriNet;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * A common base class for reduction rules that can be applied to Petri nets, used in {@link LiptonReduction}.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of letters in the Petri net
 * @param <P>
 *            The type of places in the Petri net
 */
public abstract class ReductionRule<L, P> {
	private final BoundedPetriNet<L, P> mNet;
	protected final CoenabledRelation<L, P> mCoenabledRelation;

	protected final LiptonReductionStatisticsGenerator mStatistics;
	private final IIndependenceCache<?, L> mIndependenceCache;

	public ReductionRule(final LiptonReductionStatisticsGenerator statistics, final BoundedPetriNet<L, P> net,
			final CoenabledRelation<L, P> coenabledRelation, final IIndependenceCache<?, L> independenceCache) {
		mNet = net;
		mCoenabledRelation = coenabledRelation;
		mStatistics = statistics;
		mIndependenceCache = independenceCache;
	}

	/**
	 * Implements the actual logic of the reduction rule.
	 *
	 * @param net
	 *            A read-only view of the input net. All modifications of the net should be made through methods
	 *            provided by this class.
	 */
	protected abstract void applyInternal(IPetriNet<L, P> net);

	public void apply() {
		// TODO reset per-application data
		applyInternal(mNet);
		// TODO fixed-point iteration
		// TODO return data about application
	}

	protected void transferMoverProperties(final L composition, final List<L> components) {
		if (mIndependenceCache != null) {
			mIndependenceCache.mergeIndependencies(components, composition);
		}
	}

	protected void addPlace(final P place, final boolean isInitial, final boolean isAccepting) {
		// TODO record data about PN change
		mNet.addPlace(place, isInitial, isAccepting);
	}

	protected ITransition<L, P> addTransition(final L letter, final ImmutableSet<P> preds,
			final ImmutableSet<P> succs) {
		// TODO record data about PN change
		mNet.getAlphabet().add(letter);
		return mNet.addTransition(letter, preds, succs);
	}

	protected void removeTransition(final ITransition<L, P> transition) {
		// TODO record data about PN change
		mNet.removeTransition(transition);
	}
}
