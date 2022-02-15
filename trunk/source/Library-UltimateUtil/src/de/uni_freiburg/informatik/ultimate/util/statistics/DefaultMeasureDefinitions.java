/*
 * Copyright (C) 2022 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
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

/**
 * Wrapper around {@link MeasureDefinition} that allows to use it in attributes.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public enum DefaultMeasureDefinitions {
	INT_COUNTER(MeasureDefinition.INT_COUNTER),

	DOUBLE_COUNTER(MeasureDefinition.DOUBLE_COUNTER),

	INT_MAX(MeasureDefinition.INT_MAX),

	INT_MULTI_COUNTER(MeasureDefinition.INT_MULTI_COUNTER),

	/**
	 * An Integer counter that is initialized with -1
	 */
	INT_COUNTER_ZERO(MeasureDefinition.INT_COUNTER_ZERO),

	LONG_COUNTER(MeasureDefinition.LONG_COUNTER),

	STRING_COUNTER(MeasureDefinition.STRING_COUNTER),

	LONG_TIME(MeasureDefinition.LONG_TIME),

	LONG_TIME_MAX(MeasureDefinition.LONG_TIME_MAX),

	TT_TIMER(MeasureDefinition.TT_TIMER),

	TT_MAX_TIMER(MeasureDefinition.TT_MAX_TIMER),

	IN_CA_RE_COUNTER(MeasureDefinition.IN_CA_RE_COUNTER),

	/**
	 * Aggregate by assuming existing {@link StatisticsAggregator} instance.
	 */
	STATISTICS_AGGREGATOR(MeasureDefinition.STATISTICS_AGGREGATOR),

	/**
	 * Aggregate by inserting into fresh {@link StatisticsAggregator}.
	 */
	STATISTICS_CONVERT_AGGREGATE(MeasureDefinition.STATISTICS_CONVERT_AGGREGATE),

	BACKWARD_COVERING_INFORMATION(MeasureDefinition.BACKWARD_COVERING_INFORMATION),

	FLAG_AND(MeasureDefinition.FLAG_AND),

	;

	private final MeasureDefinition mType;

	DefaultMeasureDefinitions(final MeasureDefinition type) {
		mType = type;
	}

	public final MeasureDefinition keyType() {
		return mType;
	}

}