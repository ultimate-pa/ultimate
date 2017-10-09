/*
 * Copyright (C) 2014-2017 Daniel Tischner <zabuza.dev@gmail.com>
 * Copyright (C) 2009-2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.tree.operations.minimization.performance;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.automata.statefactory.IIntersectionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IMergeStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.ISinkStateFactory;

/**
 * State factory which is able to create sink states, merge and intersect
 * states.
 * 
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 *
 * @param <STATE>
 *            The type of the states
 */
public final class SinkMergeIntersectStateFactory<STATE>
		implements IMergeStateFactory<STATE>, ISinkStateFactory<STATE>, IIntersectionStateFactory<STATE> {
	/**
	 * Factory used to intersect states.
	 */
	private final IIntersectionStateFactory<STATE> mIntersectFactory;
	/**
	 * Factory used to merge states.
	 */
	private final IMergeStateFactory<STATE> mMergeFactory;
	/**
	 * Factory used to create sink states.
	 */
	private final ISinkStateFactory<STATE> mSinkFactory;

	/**
	 * Creates a new sink, merge and intersect factory which delegates operations to
	 * the given factories.
	 * 
	 * @param sinkFactory
	 *            The sink factory to use
	 * @param mergeFactory
	 *            The merge factory to use
	 * @param intersectFactory
	 *            The intersect factory to use
	 */
	public SinkMergeIntersectStateFactory(final ISinkStateFactory<STATE> sinkFactory,
			final IMergeStateFactory<STATE> mergeFactory, final IIntersectionStateFactory<STATE> intersectFactory) {
		this.mMergeFactory = mergeFactory;
		this.mSinkFactory = sinkFactory;
		this.mIntersectFactory = intersectFactory;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.statefactory.
	 * IEmptyStackStateFactory#createEmptyStackState()
	 */
	@Override
	public STATE createEmptyStackState() {
		return this.mMergeFactory.createEmptyStackState();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.automata.statefactory.ISinkStateFactory#
	 * createSinkStateContent()
	 */
	@Override
	public STATE createSinkStateContent() {
		return this.mSinkFactory.createSinkStateContent();
	}

	@Override
	public STATE intersection(final STATE state1, final STATE state2) {
		return this.mIntersectFactory.intersection(state1, state2);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.automata.statefactory.IMergeStateFactory#
	 * merge(java.util.Collection)
	 */
	@Override
	public STATE merge(final Collection<STATE> states) {
		return this.mMergeFactory.merge(states);
	}
}
