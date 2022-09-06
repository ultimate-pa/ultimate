/*
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
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
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.MonitoredIndependence.IndependenceMonitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.abstraction.IAbstraction;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.ILattice;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Quad;

public class AbstractionAwareDeadEndOptimizingVisitor<L, S, H, V extends IDfsVisitor<L, S>>
		extends WrapperVisitor<L, S, V> {
	private final AbstractionAwareDeadEndStore<?, S, H> mDeadEndStore;
	private final IndependenceMonitor<L, S, H> mMonitor;
	private final boolean mIsReadOnly;
	private final boolean mIsMonotonic;

	private final H mLevel;
	private final IAbstraction<H, L> mAbstraction;
	private final ILattice<H> mHierarchy;

	private final Map<L, H> mRestrictionCache = new HashMap<>();

	/**
	 * Wraps a given visitor with dead-end detection and pruning.
	 *
	 * @param underlying
	 *            The underlying visitor
	 * @param store
	 *            A dead end store which is used to store and query dead end information
	 * @param isReadOnly
	 *            Whether the dead end store should be treated as read-only (backtracked states should not be added)
	 */
	public AbstractionAwareDeadEndOptimizingVisitor(final V underlying, final H level,
			final AbstractionAwareDeadEndStore<?, S, H> store, final boolean isReadOnly, final boolean isMonotonic,
			final IAbstraction<H, L> abstraction) {
		super(underlying);

		mLevel = level;
		mDeadEndStore = store;

		mIsReadOnly = isReadOnly;
		mIsMonotonic = isMonotonic;
		mAbstraction = abstraction;
		mHierarchy = mAbstraction.getHierarchy();

		mMonitor = new IndependenceMonitor<>(mHierarchy::supremum, this::gradeQuery);
	}

	private H gradeQuery(final H old, final Quad<?, L, L, Boolean> query, final int x) {
		if (mIsMonotonic && !query.getFourth()) {
			// Ignore failed queries. This is sound if more independence always means more dead ends.
			return old;
		}
		if (mLevel.equals(old)) {
			// If we have already reached the maximal possible level, the value cannot change further.
			return mLevel;
		}

		final H levelA = restrict(query.getSecond());
		if (mLevel.equals(levelA)) {
			return mLevel;
		}
		final H withA = mHierarchy.supremum(old, levelA);
		if (mLevel.equals(withA)) {
			return mLevel;
		}

		final H levelB = restrict(query.getThird());
		if (mLevel.equals(levelB)) {
			return mLevel;
		}
		return mHierarchy.supremum(withA, levelB);
	}

	private H restrict(final L letter) {
		return mRestrictionCache.computeIfAbsent(letter, l -> mAbstraction.restrict(l, mLevel));
	}

	@Override
	public boolean addStartState(final S state) {
		final boolean result = mUnderlying.addStartState(state);
		mMonitor.push(mHierarchy.getBottom());
		return result || mDeadEndStore.isDeadEndState(state);
	}

	@Override
	public boolean discoverState(final S state) {
		final boolean result = mUnderlying.discoverState(state);
		mMonitor.push(mHierarchy.getBottom());
		return result || mDeadEndStore.isDeadEndState(state);
	}

	@Override
	public void backtrackState(final S state, final boolean isComplete) {
		final H level = mMonitor.popAndCombine();
		mUnderlying.backtrackState(state, isComplete);
		if (!mIsReadOnly && isComplete) {
			// System.out.println("Recording dead end at level " + level + " :: " + state);
			mDeadEndStore.addDeadEndState(state, level);
		}
	}

	public IndependenceMonitor<L, S, H> getMonitor() {
		return mMonitor;
	}
}
