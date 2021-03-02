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
package de.uni_freiburg.informatik.ultimate.automata.partialorder;

import de.uni_freiburg.informatik.ultimate.util.statistics.AbstractStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.KeyType;

/**
 * Collects statistics for independence relations. Implementors of {@link IIndependenceRelation} can use this class to
 * implement {@link IIndependenceRelation#getStatistics()}.
 *
 * This class collects data on how many queries were made, with what result, and whether or not they were conditional.
 * If more data should be collected, derive a subclass and add the additional fields using the mechanism described in
 * {@link AbstractStatisticsDataProvider#declare(String, java.util.function.Supplier, KeyType)}.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public class IndependenceStatisticsDataProvider extends AbstractStatisticsDataProvider {

	public static final String TOTAL_QUERIES = "Total Queries";
	public static final String POSITIVE_QUERIES = "Positive Queries";
	public static final String POSITIVE_CONDITIONAL_QUERIES = "Positive Conditional Queries";
	public static final String POSITIVE_UNCONDITIONAL_QUERIES = "Positive Unconditional Queries";
	public static final String NEGATIVE_QUERIES = "Negative Queries";
	public static final String UNKNOWN_QUERIES = "Unknown Queries";

	private int mPositiveConditionalQueries;
	private int mPositiveUnconditionalQueries;
	private int mNegativeConditionalQueries;
	private int mNegativeUnconditionalQueries;
	private int mUnknownConditionalQueries;
	private int mUnknownUnconditionalQueries;

	/**
	 * Create a new instance to collect data, with the default data fields.
	 */
	public IndependenceStatisticsDataProvider() {
		declare(TOTAL_QUERIES, this::getTotalQueries, KeyType.COUNTER);
		declare(POSITIVE_QUERIES, this::getPositiveQueries, KeyType.COUNTER);
		declare(POSITIVE_CONDITIONAL_QUERIES, this::getPositiveConditionalQueries, KeyType.COUNTER);
		declare(POSITIVE_UNCONDITIONAL_QUERIES, this::getPositiveUnconditionalQueries, KeyType.COUNTER);
		declare(NEGATIVE_QUERIES, this::getNegativeQueries, KeyType.COUNTER);
		declare(UNKNOWN_QUERIES, this::getUnknownQueries, KeyType.COUNTER);
	}

	public int getTotalQueries() {
		return getPositiveQueries() + getNegativeQueries() + getUnknownQueries();
	}

	public int getPositiveQueries() {
		return getPositiveConditionalQueries() + getPositiveUnconditionalQueries();
	}

	public int getPositiveConditionalQueries() {
		return mPositiveConditionalQueries;
	}

	public int getPositiveUnconditionalQueries() {
		return mPositiveUnconditionalQueries;
	}

	public int getNegativeQueries() {
		return getNegativeConditionalQueries() + getNegativeUnconditionalQueries();
	}

	public int getNegativeConditionalQueries() {
		return mNegativeConditionalQueries;
	}

	public int getNegativeUnconditionalQueries() {
		return mNegativeUnconditionalQueries;
	}

	public int getUnknownQueries() {
		return getUnknownConditionalQueries() + getUnknownUnconditionalQueries();
	}

	public int getUnknownConditionalQueries() {
		return mUnknownConditionalQueries;
	}

	public int getUnknownUnconditionalQueries() {
		return mUnknownUnconditionalQueries;
	}

	public void reportQuery(final boolean positive, final boolean conditional) {
		if (positive) {
			reportPositiveQuery(conditional);
		} else {
			reportNegativeQuery(conditional);
		}
	}

	public void reportPositiveQuery(final boolean conditional) {
		if (conditional) {
			mPositiveConditionalQueries++;
		} else {
			mPositiveUnconditionalQueries++;
		}
	}

	public void reportNegativeQuery(final boolean conditional) {
		if (conditional) {
			mNegativeConditionalQueries++;
		} else {
			mNegativeUnconditionalQueries++;
		}
	}

	public void reportUnknownQuery(final boolean conditional) {
		if (conditional) {
			mUnknownConditionalQueries++;
		} else {
			mUnknownUnconditionalQueries++;
		}
	}
}
