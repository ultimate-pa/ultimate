/*
 * Copyright (C) 2020 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2020 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
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

import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsElement;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsType;

/**
 * Describes statistics collected about a {@link LiptonReduction}.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 */
public enum LiptonReductionStatisticsDefinitions implements IStatisticsElement {
	ReductionTime(Long.class, StatisticsType.LONG_ADDITION, StatisticsType.KEY_BEFORE_NANOS),

	PlacesBefore(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.DATA_BEFORE_KEY),

	PlacesAfterwards(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.DATA_BEFORE_KEY),

	TransitionsBefore(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.DATA_BEFORE_KEY),

	TransitionsAfterwards(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.DATA_BEFORE_KEY),

	CoEnabledTransitionPairs(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.DATA_BEFORE_KEY),

	FixpointIterations(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.DATA_BEFORE_KEY),

	TrivialSequentialCompositions(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.DATA_BEFORE_KEY),

	ConcurrentSequentialCompositions(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.DATA_BEFORE_KEY),

	TrivialYvCompositions(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.DATA_BEFORE_KEY),

	ConcurrentYvCompositions(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.DATA_BEFORE_KEY),

	ChoiceCompositions(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.DATA_BEFORE_KEY),

	TotalNumberOfCompositions(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.DATA_BEFORE_KEY),

	MoverChecksTotal(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.DATA_BEFORE_KEY),;

	private final Class<?> mClazz;
	private final Function<Object, Function<Object, Object>> mAggr;
	private final Function<String, Function<Object, String>> mPrettyprinter;

	LiptonReductionStatisticsDefinitions(final Class<?> clazz, final Function<Object, Function<Object, Object>> aggr,
			final Function<String, Function<Object, String>> prettyprinter) {
		mClazz = clazz;
		mAggr = aggr;
		mPrettyprinter = prettyprinter;
	}

	@Override
	public Object aggregate(final Object o1, final Object o2) {
		return mAggr.apply(o1).apply(o2);
	}

	@Override
	public String prettyprint(final Object o) {
		return mPrettyprinter.apply(name()).apply(o);
	}
}
