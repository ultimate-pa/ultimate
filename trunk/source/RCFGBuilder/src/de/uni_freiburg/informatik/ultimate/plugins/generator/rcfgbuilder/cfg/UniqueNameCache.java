/*
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
 *
 * This file is part of the ULTIMATE RCFGBuilder plug-in.
 *
 * The ULTIMATE RCFGBuilder plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE RCFGBuilder plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE RCFGBuilder plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE RCFGBuilder plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE RCFGBuilder plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Small cache that optimizes the creation of unique names with certain suffixes.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class UniqueNameCache {

	private final List<String> mSuffixCache;
	private final Map<String, Integer> mSuffixCount;
	private final String mSuffix;

	/**
	 * @param suffix
	 *            The suffix you want to use to make strings unique.
	 */
	public UniqueNameCache(final String suffix) {
		mSuffixCache = new ArrayList<>();
		mSuffixCount = new HashMap<>();
		mSuffix = suffix;
	}

	/**
	 * Gives you a unique string for a certain basename. Each call to this method will generate a new unique string by
	 * appending the suffix another time to the last result.
	 *
	 * Note that it assumes that the parameter itself is already unique, i.e., the following code will fail because b
	 * will equal c. <code>
	 * String a = "hans";
	 * String b = getUniqueString(a);
	 * String c = getUniqueString(b);
	 * assert b != c;
	 * </code>
	 *
	 * @param name
	 *            The base string.
	 * @return A unique string relative to this base string.
	 */
	public String getUniqueName(final String name) {
		assert !name.endsWith(mSuffix) : "You should only use the initial name";
		final Integer suffixCount = mSuffixCount.get(name);
		if (suffixCount == null) {
			mSuffixCount.put(name, 0);
			return name;
		}
		final int newSuffixCount = suffixCount + 1;
		mSuffixCount.put(name, newSuffixCount);
		return name + getSuffix(newSuffixCount);
	}

	private String getSuffix(final int numOfSuffixes) {
		if (numOfSuffixes < 1) {
			throw new IllegalArgumentException("numOfSuffixes have to be positive");
		}
		final int repetitions = numOfSuffixes - 1;
		final int cachesize = mSuffixCache.size();
		if (repetitions < cachesize) {
			return mSuffixCache.get(repetitions);
		}
		if (repetitions != cachesize) {
			throw new AssertionError("Cannot grow non-monotone");
		}

		final String lastSuffix;
		if (repetitions == 0) {
			lastSuffix = "";
		} else {
			lastSuffix = mSuffixCache.get(cachesize - 1);
		}
		final String newSuffix = lastSuffix + mSuffix;
		mSuffixCache.add(newSuffix);
		return newSuffix;
	}

}
