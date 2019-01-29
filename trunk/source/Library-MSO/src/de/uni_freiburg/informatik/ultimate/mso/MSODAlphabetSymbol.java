/**
 * TODO: Copyright.
 */

package de.uni_freiburg.informatik.ultimate.mso;

import java.security.InvalidParameterException;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * TODO: Comment.
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
		mMap = new HashMap<Term, Boolean>();
	}

	/**
	 * Constructor for alphabet symbol that contains a single variable.
	 */
	public MSODAlphabetSymbol(final Term term, final boolean value) {
		mMap = new HashMap<Term, Boolean>();
		add(term, value);
	}
	
	/**
	 * Constructor for alphabet symbol that contains two variables.
	 */
	public MSODAlphabetSymbol(final Term term1, final Term term2, final boolean value1, final boolean value2) {
		mMap = new HashMap<Term, Boolean>();
		add(term1, value1);
		add(term2, value2);
	}

	/**
	 * Constructor for alphabet symbol that contains multiple variables.
	 *
	 * @throws InvalidParameterException
	 *             if lengths of terms and values differ.
	 */
	public MSODAlphabetSymbol(final Term[] terms, final boolean[] values) {
		if (terms.length != values.length) {
			throw new InvalidParameterException("Input terms, values of different length.");
		}

		mMap = new HashMap<Term, Boolean>();
		for (int i = 0; i < terms.length; i++) {
			add(terms[i], values[i]);
		}
	}

	/**
	 * Returns a map with variables forming this alphabet symbol.
	 */
	public final Map<Term, Boolean> getMap() {
		return mMap;
	}

	/**
	 * Returns the terms contained in this alphabet symbol.
	 */
	public final Term[] getTerms() {
		return mMap.keySet().toArray(new Term[0]);
	}

	/**
	 * Adds the given variable to this alphabet symbol.
	 *
	 * @throws InvalidParameterException
	 *             if term is not of type Int or SetOfInt.
	 */
	public void add(final Term term, final boolean value) {
		if (!MSODUtils.isVariable(term)) {
			throw new IllegalArgumentException("Input term must be an Int or SetOfInt variable.");
		}

		mMap.put(term, value);
	}

	/**
	 * Returns true if all variables of the given alphabet symbol are included in this alphabet symbol.
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

	/**
	 * Returns a string representation of this alphabet symbol.
	 */
	@Override
	public String toString() {
		String str = new String();

		if (mMap.isEmpty()) {
			return "empty";
		}

		for (final Map.Entry<Term, Boolean> entry : mMap.entrySet()) {
			str += entry.getKey().toString() + "=" + (entry.getValue() ? "1 " : "0 ");
		}

		return str.trim();
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
		
		if (this == obj) {
			return true;
		}
		
		final MSODAlphabetSymbol other = (MSODAlphabetSymbol) obj;
		return mMap.equals(other.mMap);
	}
}