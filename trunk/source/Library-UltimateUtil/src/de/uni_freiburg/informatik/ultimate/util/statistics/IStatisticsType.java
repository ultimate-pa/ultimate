/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
import java.util.Map;
import java.util.function.Supplier;

/**
 * Classes that implement this interface define a set of measurements that is represented as a key-value store. These
 * classes define the following.
 * <ul>
 * <li>the allowed keys
 * <li>the {@link MeasureDefinition} for each key, i.e., how measures of the same key can be aggregated, pretty
 * printed, etc.
 * </ul>
 *
 * @author Matthias Heizmann
 */
public interface IStatisticsType {

	Collection<String> getKeys();

	Measure getMeasure(String key);

	Object getValue(String key);

	Map<String, Measure> getMeasures();

	/**
	 * Wrapper around a {@link MeasureDefinition} that describes how to aggregate, print, check a metric, and a getter
	 * function that retrieves the metric from somewhere.
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 */
	final class Measure {
		private final MeasureDefinition mKeyType;
		private final Supplier<Object> mGetter;

		public Measure(final MeasureDefinition keyType, final Supplier<Object> getter) {
			mKeyType = keyType;
			mGetter = getter;
		}

		public MeasureDefinition getMeasureDefinition() {
			return mKeyType;
		}

		public Supplier<Object> getGetter() {
			return mGetter;
		}
	}

}
