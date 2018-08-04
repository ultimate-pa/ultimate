/*
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

/*
 * TODO: Comment.
 */
public class MoNatDiffAlphabetSymbol {

	private Map<Term, Boolean> mMap;

	/*
	 * TODO: Comment.
	 */
	public MoNatDiffAlphabetSymbol() {
		mMap = new HashMap<Term, Boolean>();
	}
	
	/*
	 * TODO: Comment.
	 */
	public MoNatDiffAlphabetSymbol(Term term, int value) {
		mMap = new HashMap<Term, Boolean>();
		add(term, value);
	}

	/*
	 * TODO: Comment.
	 */
	public MoNatDiffAlphabetSymbol(Term term1, Term term2, int value1, int value2) {
		mMap = new HashMap<Term, Boolean>();
		add(term1, value1);
		add(term2, value2);
	}

	/*
	 * TODO: Comment.
	 */
	public MoNatDiffAlphabetSymbol(Term[] terms, int[] values) {
		if (terms.length != values.length)
			throw new InvalidParameterException("Input terms, values of different length.");

		mMap = new HashMap<Term, Boolean>();
		for (int i = 0; i < terms.length; i++)
			add(terms[i], values[i]);
	}
	
	/*
	 * TODO: Comment.
	 */
	public Map<Term, Boolean> getMap() {
		return mMap;
	}

	/*
	 * TODO: Comment.
	 */
	public void add(Term term, int value) {
		if (!MoNatDiffUtils.isVariable(term))
			throw new InvalidParameterException("Input term must be a Int or SetOfInt variable.");

		if (value < 0 || value > 1)
			throw new InvalidParameterException("Input value must be 0 or 1.");

		mMap.put(term, value != 0);
	}
	
//	@Override
//	public boolean equals(Object object) {
//		if (object == this)
//			return true;
//		
//		return (object instanceof MoNatDiffAlphabetSymbol && ((MoNatDiffAlphabetSymbol)object).mMap.equals(mMap));
//	}
	
	/*
	 * TODO: Comment.
	 */
	public boolean contains(MoNatDiffAlphabetSymbol alphabetSymbol) {
		return mMap.entrySet().containsAll(alphabetSymbol.mMap.entrySet());
	}
	
	/*
	 * TODO: Comment.
	 */
	public boolean allMatches(Boolean value, Term... excludedTerms) {
		Set<Term> excluded = new HashSet<Term>(Arrays.asList(excludedTerms));
		Iterator<Entry<Term, Boolean>> it = mMap.entrySet().iterator();
		
		while (it.hasNext()) {
			Entry<Term, Boolean> entry = it.next();
			
			if (!excluded.contains(entry.getKey()) && !entry.getValue().equals(value))
				return false;
		}

		return true;
	}

	/*
	 * TODO: Comment.
	 */
	public String toString() {
		String str = new String();
		
		if (mMap.isEmpty())
			str += "empty";

		Iterator<Map.Entry<Term, Boolean>> it = mMap.entrySet().iterator();
		while (it.hasNext()) {
			Map.Entry<Term, Boolean> entry = it.next();
			str += entry.getKey().toString() + "=" + (entry.getValue() ? "1" : "0");
			str += it.hasNext() ? " " : "";
		}

		return str;
	}
}