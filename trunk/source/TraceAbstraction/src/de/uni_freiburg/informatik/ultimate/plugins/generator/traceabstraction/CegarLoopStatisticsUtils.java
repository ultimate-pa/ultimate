/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.HashSet;
import java.util.Set;
import java.util.function.Function;

/**
 * Provides auxiliary methods for aggregating CEGAR loop statistics.
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class CegarLoopStatisticsUtils {
	
	static final Function<Object, Function<Object, Object>> DEFAULT_AGGREGATION_FUN =
			x -> y -> CegarLoopStatisticsDefinitions.aggregateResult(x, y);

	private static AbstractCegarLoop.Result aggregateResult(final Object value1, final Object value2) {
		final AbstractCegarLoop.Result result1 = (AbstractCegarLoop.Result) value1;
		final AbstractCegarLoop.Result result2 = (AbstractCegarLoop.Result) value2;
		final Set<AbstractCegarLoop.Result> results = new HashSet<>();
		results.add(result1);
		results.add(result2);
		if (results.contains(AbstractCegarLoop.Result.UNSAFE)) {
			return AbstractCegarLoop.Result.UNSAFE;
		} else if (results.contains(AbstractCegarLoop.Result.UNKNOWN)) {
			return AbstractCegarLoop.Result.UNKNOWN;
		} else if (results.contains(AbstractCegarLoop.Result.TIMEOUT)) {
			return AbstractCegarLoop.Result.TIMEOUT;
		} else if (results.contains(AbstractCegarLoop.Result.SAFE)) {
			return AbstractCegarLoop.Result.SAFE;
		} else {
			throw new AssertionError();
		}
	}
}