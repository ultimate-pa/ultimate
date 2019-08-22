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

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Represents a MSOD-alphabet symbol. Each MSOD-alphabet symbol has a HashMap of term-value pairs.
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
	 * Constructor for alphabet symbol that contains multiple variables.
	 *
	 * @throws InvalidParameterException
	 *             if lengths of terms and values differ.
	 */
	public MSODAlphabetSymbol(final Term[] terms, final boolean[] values) {
		if (terms.length != values.length) {
			throw new InvalidParameterException("Input terms, values of different length.");
		}

		mMap = new HashMap<>();
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

	/*
	 * Returns a set with terms that match the given sorts.
	 */
	public Set<Term> containsSort(final String sort) {

		return containsSort(new HashSet<>(Arrays.asList(sort)));
	}

	/*
	 * Returns a set with terms that match the given sorts.
	 */
	public Set<Term> containsSort(final Set<String> sorts) {
		final Set<Term> result = new HashSet<>();

		for (final Term term : getTerms()) {
			if (sorts.contains(term.getSort().getName())) {
				result.add(term);
			}
		}

		return result;
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

	/**
	 * @deprecated
	 *
	 * 			TODO: Function should probably be removed. Deal with term length. Function mixes up different
	 *             functionalities.
	 */
	@Deprecated
	public static Map<String, MSODAlphabetSymbol>
			createAlphabet(final NestedWordAutomaton<MSODAlphabetSymbol, String> automaton, final Term... terms) {
		final Map<String, MSODAlphabetSymbol> alphabetSymbols = new HashMap<>();

		if (terms.length == 1) {
			final MSODAlphabetSymbol x0, x1;
			x0 = new MSODAlphabetSymbol(terms[0], false);
			x1 = new MSODAlphabetSymbol(terms[0], true);
			alphabetSymbols.put("x0", x0);
			alphabetSymbols.put("x1", x1);
			automaton.getAlphabet().addAll(Arrays.asList(x0, x1));
		}

		if (terms.length == 2) {
			final MSODAlphabetSymbol xy00, xy01, xy10, xy11;
			xy00 = new MSODAlphabetSymbol(new Term[] { terms[0], terms[1] }, new boolean[] { false, false });
			xy01 = new MSODAlphabetSymbol(new Term[] { terms[0], terms[1] }, new boolean[] { false, true });
			xy10 = new MSODAlphabetSymbol(new Term[] { terms[0], terms[1] }, new boolean[] { true, false });
			xy11 = new MSODAlphabetSymbol(new Term[] { terms[0], terms[1] }, new boolean[] { true, true });
			alphabetSymbols.put("xy00", xy00);
			alphabetSymbols.put("xy01", xy01);
			alphabetSymbols.put("xy10", xy10);
			alphabetSymbols.put("xy11", xy11);
			automaton.getAlphabet().addAll(Arrays.asList(xy00, xy01, xy10, xy11));
		}

		return alphabetSymbols;
	}
}