/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 * 
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms;

import java.util.ArrayList;
import java.util.Collections;
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
 * Represents a set of literals {@see Literal} as a map that assigns to each
 * atom its polarity. This can be used to represent conjunctions and 
 * disjunctions.
 * This data structure is unable to represent sets where a literal occurs
 * positive and negative. Instead this data structure throws an 
 * AtomAndNegationException whenever a modification would result in a set where
 * a literal occurs positive an negative.
 * 
 * @author Matthias Heizmann
 */
public class XJunction {
	
	/**
	 * Maps atoms to POSITIVE/NEGATIVE
	 */
	private final Map<Term, Polarity> m_PolarityMap;
	
	
	
	/**
	 * Construct an XJunction that represents a set of terms.
	 * @throws AtomAndNegationException if a literal occurs positive and 
	 * negative in terms.
	 */
	public XJunction(Term[] terms) throws AtomAndNegationException {
		m_PolarityMap = new HashMap<Term, Polarity>(terms.length);
		for (Term term : terms) {
			addTermWithUnknownPolarity(term);
		}
	}
	
	/**
	 * Copy constructor
	 */
	public XJunction(XJunction xJunction) {
		m_PolarityMap = new HashMap<Term, Polarity>(xJunction.m_PolarityMap);
	}

	/**
	 * Constructs an empty XJunction.
	 */
	public XJunction() {
		m_PolarityMap = new HashMap<Term, Polarity>();
	}
	
	/**
	 * Constructs an XJunction hat contains a single literal given by the pair
	 * (atom, polarity).
	 */
	public XJunction(Term atom, Polarity polarity) {
		m_PolarityMap = new HashMap<Term, Polarity>();
		m_PolarityMap.put(atom, polarity);
	}


	/**
	 * Converts a term into a literal and adds it to this xJunction.
	 * @return true iff XJunction was modified (i.e. input was not already contained)
	 * @throws AtomAndNegationException If the literal with the opposite
	 * polarity is already contained in this xjunction.
	 */
	public boolean addTermWithUnknownPolarity(Term term) throws AtomAndNegationException {
		Literal literal = new Literal(term);
		return add(literal.getAtom(), literal.getPolarity());
	}
	
	
	/**
	 * Adds a literal given as (atom, polarity) pair to this XJunction. 
	 * @return true iff XJunction was modified (i.e. was not already contained)
	 * @throws AtomAndNegationException
	 */
	boolean add(Term atom, Polarity polarity) throws AtomAndNegationException {
		boolean containsNegation = containsNegation(atom, polarity);
		if (containsNegation) {
			// param contained φ as well as (not φ), we return null
			throw new AtomAndNegationException();
		} else {
			return m_PolarityMap.put(atom, polarity) == null;
		}
	}
	
	/**
	 * @return true iff this XJunction contains the literal given by the pair
	 * (atom, polarity).
	 */
	public boolean contains(Term atom, Polarity polarity) {
		return m_PolarityMap.get(atom) == polarity;
	}

	/**
	 * @return true iff this XJunction contains the negation of the literal 
	 * given by the pair (atom, polarity).
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
	
	

	
	/**
	 * @return a list of terms such that each term represents one literal of
	 * this XJunction.
	 */
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
	
	
	/**
	 * Two XJunctions are equivalent if they contain the same literals. 
	 */
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


	/**
	 * Hashcode of the underlying Map
	 */
	@Override
	public int hashCode() {
		return m_PolarityMap.hashCode();
	}


	/**
	 * @return All literals of this XJunction as (atom,polarity) pairs.
	 */
	public Set<Entry<Term, Polarity>> entrySet() {
		return Collections.unmodifiableSet(m_PolarityMap.entrySet());
	}


	/**
	 * @return numer of literals of this XJunction.
	 */
	public int size() {
		return m_PolarityMap.size();
	}

	/**
	 * @return the polarity of a given atom and null if no literal with that
	 * atom is contained.
	 */
	public Polarity getPolarity(Term atom) {
		return m_PolarityMap.get(atom);
	}


	/**
	 * Returns the literal (atom, polarity) for the given atom. 
	 * @return The polarity of the removed literal and null if no literal with
	 * this atom was contained.
	 */
	public Polarity remove(Term atom) {
		return m_PolarityMap.remove(atom);
	}


	@Override
	public String toString() {
		return m_PolarityMap.toString();
	}
	
	/**
	 * @return true iff all literals of this XJunction are a subset of the
	 * given XJunction.
	 */
	public boolean isSubset(XJunction xjunction) {
		if (xjunction.size() < size()) {
			return false;
		} else {
		return xjunction.m_PolarityMap.entrySet().containsAll(
				this.m_PolarityMap.entrySet());
		}
	}

	/**
	 * Exception that is thrown if a modification of a XJunction would result
	 * in a set where an literal and its negation are contained.
	 * 
	 * @author Matthias Heizmann
	 *
	 */
	public class AtomAndNegationException extends Exception {
		private static final long serialVersionUID = -5506932837927008768L;
	}


	/**
	 * @return Returns the disjoint union of two XJunctions
	 * @throws AtomAndNegationException if the result would contain a
	 * positive and a negative literal for the same atom.
	 * @throws IllegalArgumentException if both XJunctions are not disjoint.
	 */
	public static XJunction disjointUnion(XJunction xjunction1, 
						XJunction xjunction2) throws AtomAndNegationException {
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
