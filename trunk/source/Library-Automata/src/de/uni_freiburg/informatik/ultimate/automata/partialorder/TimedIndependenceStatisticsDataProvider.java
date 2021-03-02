package de.uni_freiburg.informatik.ultimate.automata.partialorder;

import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.util.statistics.KeyType;

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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
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

/**
 * Collects statistics for independence relation, in particular the (aggregated) time required for various kinds of
 * queries (conditional or not; positive, negative or unknown).
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public class TimedIndependenceStatisticsDataProvider extends IndependenceStatisticsDataProvider {
	public static final String TOTAL_TIME = "Total query time";
	public static final String POSITIVE_QUERY_TIME = "Time for positive queries";
	public static final String POSITIVE_CONDITIONAL_QUERY_TIME = "Time for positive conditional queries";
	public static final String POSITIVE_UNCONDITIONAL_QUERY_TIME = "Time for positive unconditional queries";
	public static final String NEGATIVE_QUERY_TIME = "Time for negative queries";
	public static final String NEGATIVE_CONDITIONAL_QUERY_TIME = "Time for negative conditional queries";
	public static final String NEGATIVE_UNCONDITIONAL_QUERY_TIME = "Time for negative unconditional queries";
	public static final String UNKNOWN_QUERY_TIME = "Time for unknown queries";
	public static final String UNKNOWN_CONDITIONAL_QUERY_TIME = "Time for unknown conditional queries";
	public static final String UNKNOWN_UNCONDITIONAL_QUERY_TIME = "Time for unknown unconditional queries";

	private long mPositiveConditionalTime;
	private long mPositiveUnconditionalTime;
	private long mNegativeConditionalTime;
	private long mNegativeUnconditionalTime;
	private long mUnknownConditionalTime;
	private long mUnknownUnconditionalTime;

	/**
	 * Create a new instance with the default fields (number and required time for various kinds of queries).
	 */
	public TimedIndependenceStatisticsDataProvider() {
		declare(TOTAL_TIME, this::getTotalTime, KeyType.TIMER);
		declare(POSITIVE_QUERY_TIME, () -> mPositiveConditionalTime + mPositiveUnconditionalTime, KeyType.TIMER);
		declare(POSITIVE_CONDITIONAL_QUERY_TIME, () -> mPositiveConditionalTime, KeyType.TIMER);
		declare(POSITIVE_UNCONDITIONAL_QUERY_TIME, () -> mPositiveUnconditionalTime, KeyType.TIMER);
		declare(NEGATIVE_QUERY_TIME, () -> mNegativeConditionalTime + mNegativeUnconditionalTime, KeyType.TIMER);
		declare(NEGATIVE_CONDITIONAL_QUERY_TIME, () -> mNegativeConditionalTime, KeyType.TIMER);
		declare(NEGATIVE_UNCONDITIONAL_QUERY_TIME, () -> mNegativeUnconditionalTime, KeyType.TIMER);
		declare(UNKNOWN_QUERY_TIME, () -> mUnknownConditionalTime + mUnknownUnconditionalTime, KeyType.TIMER);
		declare(UNKNOWN_CONDITIONAL_QUERY_TIME, () -> mUnknownConditionalTime, KeyType.TIMER);
		declare(UNKNOWN_UNCONDITIONAL_QUERY_TIME, () -> mUnknownConditionalTime, KeyType.TIMER);
	}

	public void reportQuery(final LBool result, final long time, final boolean conditional) {
		switch (result) {
		case UNSAT:
			reportPositiveQuery(time, conditional);
			break;
		case SAT:
			reportNegativeQuery(time, conditional);
			break;
		case UNKNOWN:
			reportUnknownQuery(time, conditional);
			break;
		}
	}

	public void reportPositiveQuery(final long time, final boolean conditional) {
		reportNegativeQuery(conditional);
		if (conditional) {
			mPositiveConditionalTime += time;
		} else {
			mPositiveUnconditionalTime += time;
		}
	}

	public void reportNegativeQuery(final long time, final boolean conditional) {
		reportNegativeQuery(conditional);
		if (conditional) {
			mNegativeConditionalTime += time;
		} else {
			mNegativeUnconditionalTime += time;
		}
	}

	public void reportUnknownQuery(final long time, final boolean conditional) {
		reportUnknownQuery(conditional);
		if (conditional) {
			mUnknownConditionalTime += time;
		} else {
			mUnknownUnconditionalTime += time;
		}
	}

	public long getTotalTime() {
		return mPositiveConditionalTime + mPositiveUnconditionalTime + mNegativeConditionalTime
				+ mNegativeUnconditionalTime + mUnknownConditionalTime + mUnknownUnconditionalTime;
	}
}