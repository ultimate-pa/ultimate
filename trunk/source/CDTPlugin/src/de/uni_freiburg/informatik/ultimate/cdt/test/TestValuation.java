/*
 * Copyright (C) 2012-2015 Stefan Wissert
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE CDTPlugin plug-in.
 *
 * The ULTIMATE CDTPlugin plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CDTPlugin plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CDTPlugin plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CDTPlugin plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CDTPlugin plug-in grant you additional permission
 * to convey the resulting work.
 */
/**
 *
 */
package de.uni_freiburg.informatik.ultimate.cdt.test;

import java.util.AbstractMap.SimpleEntry;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IValuation;

/**
 * Objects return Test Data.
 *
 * @author Stefan Wissert
 *
 */
public class TestValuation implements IValuation {

	@Override
	public Map<String, Entry<IBoogieType, List<String>>> getValuesForFailurePathIndex(final int index) {
		final Map<String, Entry<IBoogieType, List<String>>> map = new HashMap<>();
		switch (index) {
		case 0:
			map.put("x", new SimpleEntry<>(BoogieType.TYPE_INT, Arrays.asList("11")));
			break;
		case 1:
			map.put("names", new SimpleEntry<>(
					BoogieType.createArrayType(3, new BoogieType[] { BoogieType.TYPE_INT }, BoogieType.TYPE_INT),
					Arrays.asList("Stefan", "Alex", "Markus")));
			break;
		default:
			map.put("x", new SimpleEntry<>(BoogieType.TYPE_INT, Arrays.asList("11")));
			map.put("y", new SimpleEntry<>(BoogieType.TYPE_INT, Arrays.asList("4711")));
			map.put("counter", new SimpleEntry<>(BoogieType.TYPE_INT, Arrays.asList("133423421")));
			break;
		}
		return map;
	}
}
