package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Literal;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Literal.Polarity;

/**
 * TODO: Documentation
 * @author Matthias Heizmann
 *
 */
public class XJunction {
	
	private final Map<Term, Polarity> m_PolarityMap;
	
	
	
	/**
	 * Returns a map that contains each parameter param of the input.
	 * If param is of the form (not φ) the map contains the tuple (φ, NEGATIVE)
	 * otherwise the map contains (param, POSITIVE).
	 * If params contains  φ as well as (not φ) we return null.
	 * @param Arrays of Terms whose sort is Bool.
	 * @throws AtomAndNegationException 
	 */
	public XJunction(Term[] params) throws AtomAndNegationException {
		m_PolarityMap = new HashMap<Term, Polarity>(params.length);
		for (Term param : params) {
			addTermWithUnknownPolarity(param);
		}
	}
	
	
	public XJunction(XJunction innerJunction) {
		m_PolarityMap = new HashMap<Term, Polarity>(innerJunction.m_PolarityMap);
	}
	
	public XJunction() {
		m_PolarityMap = new HashMap<Term, Polarity>();
	}


	public boolean addTermWithUnknownPolarity(Term term) throws AtomAndNegationException {
		Literal btwp = new Literal(term);
		return add(btwp.getAtom(), btwp.getPolarity());
	}
	
	
	/**
	 * 
	 * @param term
	 * @param polarity
	 * @return true iff XJunction was modified (i.e. was not already contained)
	 * @throws AtomAndNegationException
	 */
	boolean add(Term term, Polarity polarity) throws AtomAndNegationException {
		boolean containsNegation = containsNegation(term, polarity);
		if (containsNegation) {
			// param contained φ as well as (not φ), we return null
			throw new AtomAndNegationException();
		} else {
			return m_PolarityMap.put(term, polarity) == null;
		}
	}
	
	
	
	public boolean contains(Entry<Term, Polarity> atom) {
		return contains(atom.getKey(), atom.getValue());
	}

	public boolean contains(Term term, Polarity polarity) {
		return m_PolarityMap.get(term) == polarity;
	}

	public boolean containsNegation(Entry<Term, Polarity> atom) {
		return containsNegation(atom.getKey(), atom.getValue());
	}

	/**
	 * Return true iff a given set of atoms contains the negation of a single
	 * given atom.
	 * 
	 * @param polarityMap representation for set of atoms
	 * @term term of given atom
	 * @polarity polarity of given atom.
	 */
	public boolean containsNegation(Term term, Polarity polarity) {
		Polarity existing = m_PolarityMap.get(term);
		if (existing != null) {
			if (existing == polarity) {
				return false;
			} else {
				return true;
			}
		} else {
			return false;
		}
	}
	
	

	
	
	public List<Term> toTermList(Script script) {
		List<Term> result = new ArrayList<Term>(m_PolarityMap.size());
		for (Entry<Term, Polarity> entry : m_PolarityMap.entrySet()) {
			if (entry.getValue() == Polarity.POSITIVE) {
				result.add(entry.getKey());
			} else {
				result.add(Util.not(script, entry.getKey()));
			}
		}
		return result;
	}
	
	
	
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		XJunction other = (XJunction) obj;
		if (m_PolarityMap == null) {
			if (other.m_PolarityMap != null)
				return false;
		} else if (!m_PolarityMap.equals(other.m_PolarityMap))
			return false;
		return true;
	}


	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result
				+ ((m_PolarityMap == null) ? 0 : m_PolarityMap.hashCode());
		return result;
	}





	public Set<Entry<Term, Polarity>> entrySet() {
		return m_PolarityMap.entrySet();
	}


	public int size() {
		return m_PolarityMap.size();
	}





	public Polarity getPolarity(Object key) {
		return m_PolarityMap.get(key);
	}


	public Polarity remove(Object key) {
		return m_PolarityMap.remove(key);
	}





	@Override
	public String toString() {
		return m_PolarityMap.toString();
	}
	
	public boolean isSubset(XJunction xjunction) {
		if (xjunction.size() < size()) {
			return false;
		} else {
		return xjunction.m_PolarityMap.entrySet().containsAll(this.m_PolarityMap.entrySet());
//		return xjunction.m_PolarityMap.keySet().containsAll(this.m_PolarityMap.keySet());
		}
	}





	public class AtomAndNegationException extends Exception {

		/**
		 * 
		 */
		private static final long serialVersionUID = -5506932837927008768L;
		
	}





	public static XJunction disjointUnion(XJunction xjunction1, XJunction xjunction2) throws AtomAndNegationException {
		XJunction result = new XJunction(xjunction1);
		for (Entry<Term, Polarity> atom : xjunction2.entrySet()) {
			boolean modified = result.add(atom.getKey(), atom.getValue());
			if (modified == false) {
				throw new IllegalArgumentException("inputs were not disjoint");
			}
		}
		return result;
	}






	
	

}
