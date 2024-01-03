/*
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE Util Library.
 *
 * The ULTIMATE Util Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Util Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Util Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Util Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Util Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.util.statistics;

import java.util.Collection;
import java.util.function.ToLongFunction;

public final class MinMaxMed {
	private long mMinimum;
	private long mMaximum;
	private long mMedian;

	public <T> void report(final Collection<T> items, final ToLongFunction<T> measure) {
		if (items.isEmpty()) {
			mMinimum = 0;
			mMaximum = 0;
			mMedian = 0;
			return;
		}

		final var numbers = items.stream().mapToLong(measure).sorted().toArray();
		mMinimum = numbers[0];
		mMaximum = numbers[numbers.length - 1];
		mMedian = numbers[numbers.length / 2];
	}

	public long getMinimum() {
		return mMinimum;
	}

	public long getMaximum() {
		return mMaximum;
	}

	public long getMedian() {
		return mMedian;
	}
}