/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple;

import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker.HoareTripleCheckerStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsType;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class HoareTripleCheckerStatisticsType implements IStatisticsType {

	private static final HoareTripleCheckerStatisticsType INSTANCE = new HoareTripleCheckerStatisticsType();

	private final Map<String, Function<Object, Function<Object, Object>>> mAggrFuns;
	private final Map<String, Function<String, Function<Object, String>>> mPrintFuns;

	private HoareTripleCheckerStatisticsType() {
		mAggrFuns = new LinkedHashMap<>();
		mPrintFuns = new LinkedHashMap<>();
		for (final HoareTripleCheckerStatisticsDefinitions val : HoareTripleCheckerStatisticsDefinitions.values()) {
			registerKey(val.name(), x -> y -> val.aggregate(x, y), x -> val::prettyprint);
		}
	}

	public static HoareTripleCheckerStatisticsType getInstance() {
		return INSTANCE;
	}

	@Override
	public Collection<String> getKeys() {
		return mPrintFuns.keySet();
	}

	public void registerKey(final String key, final Function<Object, Function<Object, Object>> funAggregate,
			final Function<String, Function<Object, String>> funPrettyPrint) {
		final Function<Object, Function<Object, Object>> oldAgr = mAggrFuns.put(key, funAggregate);
		if (oldAgr != null) {
			throw new IllegalArgumentException();
		}
		final Function<String, Function<Object, String>> oldPrint = mPrintFuns.put(key, funPrettyPrint);
		if (oldPrint != null) {
			throw new IllegalArgumentException();
		}
	}

	@Override
	public Object aggregate(final String key, final Object value1, final Object value2) {
		final Function<Object, Function<Object, Object>> fun = mAggrFuns.get(key);
		if (fun == null) {
			throw new IllegalStateException(String.format("Key %s is unknown", key));
		}
		return fun.apply(value1).apply(value2);
	}

	@Override
	public String prettyprintBenchmarkData(final IStatisticsDataProvider benchmarkData) {
		final StringBuilder sb = new StringBuilder();
		final Iterator<Entry<String, Function<String, Function<Object, String>>>> iter =
				mPrintFuns.entrySet().iterator();
		sb.append(getClass().getSimpleName());
		sb.append(" [");
		while (iter.hasNext()) {
			final Entry<String, Function<String, Function<Object, String>>> entry = iter.next();
			final Object value = benchmarkData.getValue(entry.getKey());
			sb.append(entry.getValue().apply(entry.getKey()).apply(value));
			if (iter.hasNext()) {
				sb.append(", ");
			}
		}
		sb.append("]");
		return sb.toString();
	}

}
