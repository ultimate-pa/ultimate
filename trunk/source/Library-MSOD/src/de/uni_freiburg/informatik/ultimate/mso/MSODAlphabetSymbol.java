/*
 * Copyright (C) 2019 Nico Hauff (hauffn@informatik.uni-freiburg.de)
 * Copyright (C) 2019 Elisabeth Henkel (henkele@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE MSOD Library package.
 *
 * The ULTIMATE MSOD Library package library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE MSOD Library package library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE MSOD Library package. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE MSOD Library package, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE MSOD Library package library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.mso;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * An {@link MSODAlphabetSymbol} represents a MSOD-alphabet symbol. Each MSOD-alphabet symbol has a mapping from terms
 * to values.
 *
 * @author Elisabeth Henkel (henkele@informatik.uni-freiburg.de)
 * @author Nico Hauff (hauffn@informatik.uni-freiburg.de)
 */
public class MSODAlphabetSymbol {

	private final Map<Term, Boolean> mMap;

	/**
	 * Constructor for empty alphabet symbol.
	 */
	public MSODAlphabetSymbol() {
		mMap = new HashMap<>();
	}

	/**
	 * Constructor for alphabet symbol that contains a single variable.
	 */
	public MSODAlphabetSymbol(final Term term, final boolean value) {
		mMap = new HashMap<>();
		add(term, value);
	}

	/**
	 * Constructor for alphabet symbol that contains two variables.
	 */
	public MSODAlphabetSymbol(final Term term1, final Term term2, final boolean value1, final boolean value2) {
		mMap = new HashMap<>();
		add(term1, value1);
		add(term2, value2);
	}

	/**
	 * Constructor for alphabet symbol that contains multiple variables matching the given value.
	 */
	public MSODAlphabetSymbol(final List<Term> terms, final boolean value) {
		mMap = new HashMap<>();
		terms.forEach(e -> add(e, value));
	}

	/**
	 * Returns a map with variables forming this alphabet symbol.
	 */
	public final Map<Term, Boolean> getMap() {
		return mMap;
	}

	/**
	 * Returns a set view of the terms contained in this alphabet symbol.
	 */
	public final Set<Term> getTerms() {
		return mMap.keySet();
	}

	/**
	 * Adds the given variable to this alphabet symbol.
	 *
	 * @throws IllegalArgumentException
	 *             if term is not of type Int or SetOfInt.
	 */
	public void add(final Term term, final boolean value) {
		if (!MSODUtils.isConstantOrTermVariable(term)) {
			throw new IllegalArgumentException("Input term must be an Int or SetOfInt variable.");
		}

		mMap.put(term, value);
	}

	/**
	 * Returns true if all entries (variable and corresponding value) of the given alphabet symbol are included in this
	 * alphabet symbol.
	 */
	public boolean contains(final MSODAlphabetSymbol alphabetSymbol) {
		return mMap.entrySet().containsAll(alphabetSymbol.mMap.entrySet());
	}

	/**
	 * Returns true if all but the excluded variables of this alphabet symbol match the given value.
	 */
	public boolean allMatches(final boolean value, final Term... excludedTerms) {
		final Set<Term> excluded = new HashSet<>(Arrays.asList(excludedTerms));
		final Iterator<Entry<Term, Boolean>> it = mMap.entrySet().iterator();

		while (it.hasNext()) {
			final Entry<Term, Boolean> entry = it.next();

			if (!excluded.contains(entry.getKey()) && !entry.getValue().equals(value)) {
				return false;
			}
		}

		return true;
	}

	/*
	 * Returns a set with terms that match the given sorts.
	 */
	public Set<Term> containsSort(final String... sorts) {
		final Set<Term> result = new HashSet<>();

		for (final Term term : getTerms()) {
			for (final String sort : sorts) {
				if (term.getSort().getName().equals(sort)) {
					result.add(term);
				}
			}
		}

		return result;
	}

	@Override
	public String toString() {
		if (mMap.isEmpty()) {
			return "ε";
		}
		final StringBuilder sb = new StringBuilder();
		for (final Map.Entry<Term, Boolean> entry : mMap.entrySet()) {
			sb.append(entry.getKey().toString()).append("=").append((entry.getValue() ? "1 " : "0 "));
		}
		return sb.toString().trim();
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		return prime + mMap.hashCode();
	}

	@Override
	public boolean equals(final Object obj) {
		if (obj == null || getClass() != obj.getClass()) {
			return false;
		}

		return this == obj || ((MSODAlphabetSymbol) obj).mMap.equals(mMap);
	}
}