/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
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
package de.uni_freiburg.informatik.ultimate.automata;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.SimpleCsvProvider;

/**
 * Object that stores benchmark data of an automata library operation
 * Stores a single row of a CSV as a key-value map.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class AutomataOperationBenchmark implements ICsvProviderProvider<Object> {
	
	private final LinkedHashMap<String, Object> m_KeyValueMap = new LinkedHashMap<>();

	@Override
	public ICsvProvider<Object> createCvsProvider() {
		List<String> columnTitles = new ArrayList<>(m_KeyValueMap.size());
		List<Object> firstRow = new ArrayList<>(m_KeyValueMap.size());
		for (Entry<String, Object> entry : m_KeyValueMap.entrySet()) {
			columnTitles.add(entry.getKey());
			firstRow.add(entry.getValue());
			
		}
		SimpleCsvProvider<Object> result = new SimpleCsvProvider<>(columnTitles);
		result.addRow(firstRow);
		return result;
	}
	
	public Object addKeyValuePair(String key, Object value) {
		return m_KeyValueMap.put(key, value);
	}

}
