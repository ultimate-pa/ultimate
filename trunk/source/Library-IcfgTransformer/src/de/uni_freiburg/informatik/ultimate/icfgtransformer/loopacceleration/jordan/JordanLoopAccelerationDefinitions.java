/*
 * Copyright (C) 2021 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
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
package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.jordan;

import java.util.Objects;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsElement;
import de.uni_freiburg.informatik.ultimate.util.statistics.StatisticsType;

public enum JordanLoopAccelerationDefinitions implements IStatisticsElement {

	HavocedVariables(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.DATA_BEFORE_KEY),

	AssignedVariables(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.DATA_BEFORE_KEY),

	ReadonlyVariables(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.DATA_BEFORE_KEY),

	Eigenvalues(NestedMap2.class, StatisticsType.INTEGER_ADDITION, StatisticsType.KEY_BEFORE_DATA),

	SequentialAcceleration(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.DATA_BEFORE_KEY),

	AlternatingAcceleration(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.DATA_BEFORE_KEY),

	QuantifierFreeResult(Integer.class, StatisticsType.INTEGER_ADDITION, StatisticsType.DATA_BEFORE_KEY),
	;

	private final Class<?> mClazz;
	private final Function<Object, Function<Object, Object>> mAggr;
	private final Function<String, Function<Object, String>> mPrettyprinter;


	JordanLoopAccelerationDefinitions(final Class<?> clazz, final Function<Object, Function<Object, Object>> aggr,
			final Function<String, Function<Object, String>> prettyprinter) {
		mClazz = Objects.requireNonNull(clazz);
		mAggr = Objects.requireNonNull(aggr);
		mPrettyprinter = Objects.requireNonNull(prettyprinter);
	}

	@Override
	public Object aggregate(final Object o1, final Object o2) {
		return mAggr.apply(o1).apply(o2);
	}

	@Override
	public String prettyprint(final Object o) {
		return mPrettyprinter.apply(name()).apply(o);
	}

	@Override
	public Class<?> getDataType() {
		return mClazz;
	}

}