/*
 * Copyright (C) 2016 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE Core.
 *
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.core.model.translation;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;

/**
 * This class represents a mapping of variable names to values.
 *
 * <p>
 * Note that this class was primarily introduced to resolve Java build issues involving type resolution over multiple
 * plugin boundaries. <b>These issues are most likely a bug in Java. Feel free to remove this wrapper class once the bug
 * is resolved.</b>
 * </p>
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class VariableValuesMap {
	private final Map<String, Entry<IBoogieType, List<String>>> mInternalMap;

	/**
	 * Creates a new instance of a map from variable names to values. Names are strings, where values are of type
	 * {@link Entry}&lt;{@link IBoogieType}, {@link List}&lt;{@link String}&gt;&gt;.
	 */
	public VariableValuesMap() {
		mInternalMap = new HashMap<>();
	}

	/**
	 * Creates a new instance of a map from variable names to values. Names are strings, where values are of type
	 * {@link Entry}&lt;{@link IBoogieType}, {@link List}&lt;{@link String}&gt;&gt;.
	 *
	 * @param map
	 *            The base map to use.
	 */
	public VariableValuesMap(final Map<String, Entry<IBoogieType, List<String>>> map) {
		mInternalMap = map;
	}

	/**
	 * @return The Map from variable names to values.
	 */
	public Map<String, Entry<IBoogieType, List<String>>> getMap() {
		return mInternalMap;
	}
}
