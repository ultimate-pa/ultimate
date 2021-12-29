/*
 * Copyright (C) 2021 Dennis Wölfing
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Objects;

/**
 * A Dependency Rank.
 *
 * @author Dennis Wölfing
 *
 */
public class DependencyRank implements Comparable<DependencyRank> {
	private final List<Integer> mRanks;

	/**
	 * Constructs a new empty dependency rank.
	 */
	public DependencyRank() {
		mRanks = Collections.emptyList();
	}

	private DependencyRank(final List<Integer> ranks) {
		mRanks = ranks;
	}

	/**
	 * Calculates a new dependency ranks that includes the given rank.
	 *
	 * @param rank
	 *            A rank.
	 * @return The same dependency rank if rank is already included, otherwise a larger dependency rank.
	 */
	public DependencyRank add(final int rank) {
		if (mRanks.contains(rank)) {
			return this;
		}
		final List<Integer> newRanks = new ArrayList<>();
		for (final int r : mRanks) {
			if (r > rank) {
				newRanks.add(r);
			}
		}
		newRanks.add(rank);
		return new DependencyRank(newRanks);
	}

	/**
	 * Calculates the maximal dependency rank out of two dependency ranks.
	 *
	 * @param other
	 *            The other dependency rank.
	 * @return The larger dependency rank of the two.
	 */
	public DependencyRank getMax(final DependencyRank other) {
		if (other == null || compareTo(other) >= 0) {
			return this;
		}
		return other;
	}

	@Override
	public int compareTo(final DependencyRank other) {
		for (int i = 0;; i++) {
			if (mRanks.size() == i) {
				if (other.mRanks.size() > i) {
					return -1;
				}
				return 0;
			}
			if (other.mRanks.size() == i) {
				return 1;
			}
			if (mRanks.get(i) < other.mRanks.get(i)) {
				return -1;
			}
			if (mRanks.get(i) > other.mRanks.get(i)) {
				return 1;
			}
		}
	}

	@Override
	public int hashCode() {
		return Objects.hash(mRanks);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final DependencyRank other = (DependencyRank) obj;
		return Objects.equals(mRanks, other.mRanks);
	}
}
