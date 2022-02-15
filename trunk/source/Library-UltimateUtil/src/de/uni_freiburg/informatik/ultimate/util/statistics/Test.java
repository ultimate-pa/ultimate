/*
 * Copyright (C) 2021 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
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

import java.util.Arrays;
import java.util.concurrent.TimeUnit;

import de.uni_freiburg.informatik.ultimate.util.statistics.measures.InCaReCounter;
import de.uni_freiburg.informatik.ultimate.util.statistics.measures.TimeTracker;

/**
 * Functions to check statistic objects in primitive types for conditions like readiness (the object can be read from)
 * or emptiness (the object was never changed since construction).
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public final class Test {

	private Test() {
		// objects of this class have no use ==> forbid construction
	}

	public static boolean alwaysReady(final Object o) {
		return true;
	}

	public static boolean longIsEmpty(final Object o) {
		return (long) o == 0L;
	}

	public static boolean intIsEmpty(final Object o) {
		return intIsEmpty(o, 0);
	}

	public static boolean intIsEmpty(final Object o, final int value) {
		return (int) o == value;
	}

	public static boolean intArrayIsEmpty(final Object o) {
		final int[] array = (int[]) o;
		return array.length == 0 || Arrays.stream(array).allMatch(a -> a == 0);
	}

	public static boolean doubleIsEmpty(final Object o) {
		return (double) o == 0.0;
	}

	public static boolean timeTrackerIsEmpty(final Object o) {
		final TimeTracker tt = (TimeTracker) o;
		return !tt.isRunning() && tt.elapsedTime(TimeUnit.NANOSECONDS) == 0L;
	}

	public static boolean timeTrackerIsReady(final Object obj) {
		return !((TimeTracker) obj).isRunning();
	}

	public static boolean statisticsDataProviderIsEmpty(final Object o) {
		return ((IStatisticsDataProvider) o).isEmpty();
	}

	public static boolean inCaReIsEmpty(final Object o) {
		return ((InCaReCounter) o).getSum() == 0;
	}

	public static boolean flagIsEmpty(final Object o) {
		return o == null;
	}

}
