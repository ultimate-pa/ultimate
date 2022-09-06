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

import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.ILattice;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

public class AbstractionAwareDeadEndStore<S, R, H> implements IDeadEndStore<S, R> {
	private final Function<R, S> mState2Original;
	private final Function<R, ?> mState2ExtraInfo;
	private final ILattice<H> mLevelLattice;

	private final NestedMap2<S, Object, H> mDeadEndRelation = new NestedMap2<>();
	private H mLevel;

	public AbstractionAwareDeadEndStore(final Function<R, S> state2Original, final Function<R, ?> state2ExtraInfo,
			final ILattice<H> levelLattice) {
		mState2Original = state2Original;
		mState2ExtraInfo = state2ExtraInfo;
		mLevelLattice = levelLattice;
		mLevel = mLevelLattice.getTop();
	}

	public void updateLevel(final H newLevel) {
		assert mLevelLattice.compare(newLevel, mLevel).isLessOrEqual() : "level only expected to decrease";
		mLevel = newLevel;
	}

	@Override
	public boolean isDeadEndState(final R state) {
		final S original = mState2Original.apply(state);
		final Object extra = mState2ExtraInfo.apply(state);

		final H deadUntil = mDeadEndRelation.get(original, extra);
		if (deadUntil == null) {
			// not marked as dead end
			return false;
		}

		if (mLevelLattice.compare(deadUntil, mLevel).isLessOrEqual()) {
			// dead end marker exists and is still valid
			System.out.println("dead end marked at level " + deadUntil);
			System.out.println("  still valid at level " + mLevel);
			return true;
		}

		// remove now invalid dead end marker
		mDeadEndRelation.remove(original, extra);
		return false;
	}

	@Override
	public void addDeadEndState(final R state) {
		throw new UnsupportedOperationException();
	}

	public void addDeadEndState(final R state, final H level) {
		assert mLevelLattice.compare(level, mLevel).isLessOrEqual();
		mDeadEndRelation.put(mState2Original.apply(state), mState2ExtraInfo.apply(state), level);
	}

	@Override
	public void copyDeadEndInformation(final S originalState, final S newState) {
		final var entries = mDeadEndRelation.get(originalState);
		if (entries == null) {
			return;
		}

		for (final var entry : entries.entrySet()) {
			mDeadEndRelation.put(newState, entry.getKey(), entry.getValue());
		}
	}
}
