/*
 * Copyright (C) 2022 Marcel Ebbinghaus
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
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder;

import java.util.Comparator;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsOrder;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class Preference2DfsOrder<L, S1, S2, S> implements IDfsOrder<L, S> {
	private final IPreferenceOrder<L, S1, S2> mPreferenceOrder;
	private final Function<S, Pair<S1, S2>> mSplitState;

	public Preference2DfsOrder(final IPreferenceOrder<L, S1, S2> underlying,
			final Function<S, Pair<S1, S2>> splitState) {
		mPreferenceOrder = underlying;
		mSplitState = splitState;
	}

	@Override
	public Comparator<L> getOrder(final S state) {

		final Pair<S1, S2> statePair = mSplitState.apply(state);
		return mPreferenceOrder.getOrder(statePair.getFirst(), statePair.getSecond());
	}

	@Override
	public boolean isPositional() {
		return mPreferenceOrder.isPositional() || mPreferenceOrder.getMonitor() != null;
	}
}
