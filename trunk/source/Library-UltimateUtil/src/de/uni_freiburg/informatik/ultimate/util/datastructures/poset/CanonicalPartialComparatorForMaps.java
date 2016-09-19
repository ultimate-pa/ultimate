/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.util.datastructures.poset;

import java.util.Comparator;
import java.util.Map;
import java.util.Map.Entry;

/**
 * Comparator for partially ordered sets.
 * @author Matthias Heizmann
 *
 * @param <T>
 */
public class CanonicalPartialComparatorForMaps<K,V> implements IPartialComparator<Map<K,V>> {
	
	private final Comparator<V> mComperator;
	
	public CanonicalPartialComparatorForMaps(final Comparator<V> comperator) {
		super();
		mComperator = comperator;
	}


	@Override
	public ComparisonResult compare(final Map<K, V> o1, final Map<K, V> o2) {
		ComparisonResult result = ComparisonResult.EQUAL;
		for (final Entry<K, V> entry : o1.entrySet()) {
			ComparisonResult currentPartialComparionResult;
			final V value2 = o2.get(entry.getKey());
			if (value2 == null) {
				currentPartialComparionResult = ComparisonResult.STRICTLY_GREATER;
			} else {
				currentPartialComparionResult = ComparisonResult.fromNonPartialComparison(
						mComperator.compare(entry.getValue(), value2));
			}
			result = ComparisonResult.aggregate(result, currentPartialComparionResult);
			if (result == ComparisonResult.INCOMPARABLE) {
				return result;
			}
		}
		if (result == ComparisonResult.EQUAL && o1.size() < o2.size()) {
			//not equal but strictly smaller since o2 has elements that o1 does not have.
			result = ComparisonResult.STRICTLY_SMALLER;
		}
		return result;
	}

}
