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
package de.uni_freiburg.informatik.ultimate.util;

import java.util.Objects;
import java.util.function.Supplier;

/**
 * Allows to construct a single object lazily, similar to {@link ConstructionCache} for a map of values.
 *
 * This cache supports null values, i.e., the construction function is only called once.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class Lazy<V> {
	private V mValue;
	private Supplier<V> mFun;

	public Lazy(final Supplier<V> valueConstruction) {
		mFun = Objects.requireNonNull(valueConstruction);
	}

	public Lazy(final V value) {
		mValue = value;
	}

	/**
	 * Get or construct the cached value.
	 */
	public V get() {
		if (mFun == null) {
			return mValue;
		}
		mValue = mFun.get();
		mFun = null;
		return mValue;
	}
}
