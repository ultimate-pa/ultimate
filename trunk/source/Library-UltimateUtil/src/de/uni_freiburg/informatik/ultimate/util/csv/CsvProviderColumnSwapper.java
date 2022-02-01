/*
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.util.csv;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

/**
 * Sorts all columns according to a predefined order.
 * <p>
 * Any column not found in the predefined ones is removed.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <T>
 *            CSV provider type
 */
public class CsvProviderColumnSwapper<T> implements ICsvProviderTransformer<T> {
	private final Map<String, Integer> mArchetypeColumnTitle2index;
	private final List<String> mArchetypeColumnTitles;
	
	/**
	 * Constructor from a list.
	 * 
	 * @param archetypeColumnTitles
	 *            archetype order of column titles (the list is shared assuming that it is not changed)
	 */
	public CsvProviderColumnSwapper(final List<String> archetypeColumnTitles) {
		this(list2map(archetypeColumnTitles), archetypeColumnTitles);
	}
	
	/**
	 * Constructor from a map.
	 * 
	 * @param archetypeColumnTitle2index
	 *            archetype order of column titles (column title -> index)
	 */
	public CsvProviderColumnSwapper(final Map<String, Integer> archetypeColumnTitle2index) {
		this(archetypeColumnTitle2index, map2list(archetypeColumnTitle2index));
	}
	
	/**
	 * Constructor with both map and list.
	 * <p>
	 * Intentionally private to avoid consistency issues.
	 * 
	 * @param archetypeColumnTitles
	 *            archetype order of column titles
	 * @param archetypeColumnTitle2index
	 *            archetype order of column titles
	 */
	private CsvProviderColumnSwapper(final Map<String, Integer> archetypeColumnTitle2index,
			final List<String> archetypeColumnTitles) {
		mArchetypeColumnTitle2index = archetypeColumnTitle2index;
		mArchetypeColumnTitles = archetypeColumnTitles;
	}
	
	private static final Map<String, Integer> list2map(final List<String> archetypeColumnTitles) {
		final HashMap<String, Integer> map = new HashMap<>();
		final Iterator<String> iterator = archetypeColumnTitles.iterator();
		for (int i = 0; i < archetypeColumnTitles.size(); ++i) {
			map.put(iterator.next(), i);
		}
		return map;
	}
	
	private static final List<String> map2list(final Map<String, Integer> archetypeColumnTitle2index) {
		final ArrayList<String> result = new ArrayList<>(archetypeColumnTitle2index.size());
		for (final Entry<String, Integer> entry : archetypeColumnTitle2index.entrySet()) {
			final int index = entry.getValue();
			if (index < 0 || index >= result.size()) {
				throw new IllegalArgumentException("Illegal index, value was " + index + ", allowed range was [0, "
						+ (result.size() - 1) + "].");
			}
			result.set(index, entry.getKey());
		}
		return result;
	}
	
	@Override
	public ICsvProvider<T> transform(final ICsvProvider<T> csvProvider) {
		final List<String> oldColumnTitles = csvProvider.getColumnTitles();
		final int[] new2oldIndex = new int[mArchetypeColumnTitle2index.size()];
		int oldIndex = 0;
		boolean swapNeeded = false;
		for (final String columnTitle : oldColumnTitles) {
			final int newIndex = mArchetypeColumnTitle2index.get(columnTitle);
			if (oldIndex != newIndex) {
				swapNeeded = true;
			}
			new2oldIndex[newIndex] = oldIndex;
			++oldIndex;
		}
		
		if (!swapNeeded) {
			// if no swapping is needed, return the original object
			return csvProvider;
		}
		
		final SimpleCsvProvider<T> result = new SimpleCsvProvider<>(new ArrayList<>(mArchetypeColumnTitles));
		for (int i = 0; i < csvProvider.getRowHeaders().size(); ++i) {
			@SuppressWarnings("unchecked")
			final T[] oldRow = (T[]) csvProvider.getRow(i).toArray();
			final List<T> newRow = new ArrayList<>(oldRow.length);
			for (int j = 0; j < oldRow.length; ++j) {
				newRow.add(oldRow[new2oldIndex[j]]);
			}
		}
		
		return result;
	}
}
