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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.normalforms;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.Literal;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.Literal.Polarity;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Represents a set of literals {@see Literal} as a map that assigns to each atom its polarity. This can be used to
 * represent conjunctions and disjunctions. This data structure is unable to represent sets where a literal occurs
 * positive and negative. Instead this data structure throws an AtomAndNegationException whenever a modification would
 * result in a set where a literal occurs positive an negative.
 *
 * @author Matthias Heizmann
 */
public class XJunction {

	/**
	 * Maps atoms to POSITIVE/NEGATIVE
	 */
	private final Map<Term, Polarity> mPolarityMap;

	/**
	 * Construct an XJunction that represents a set of terms.
	 *
	 * @throws AtomAndNegationException
	 *             if a literal occurs positive and negative in terms.
	 */
	public XJunction(final Term[] terms) throws AtomAndNegationException {
		mPolarityMap = new HashMap<>(terms.length);
		for (final Term term : terms) {
			addTermWithUnknownPolarity(term);
		}
	}

	/**
	 * Copy constructor
	 */
	public XJunction(final XJunction xJunction) {
		mPolarityMap = new HashMap<>(xJunction.mPolarityMap);
	}

	/**
	 * Constructs an empty XJunction.
	 */
	public XJunction() {
		mPolarityMap = new HashMap<>();
	}

	/**
	 * Constructs an XJunction hat contains a single literal given by the pair (atom, polarity).
	 */
	public XJunction(final Term atom, final Polarity polarity) {
		mPolarityMap = new HashMap<>();
		mPolarityMap.put(atom, polarity);
	}

	/**
	 * Converts a term into a literal and adds it to this xJunction.
	 *
	 * @return true iff XJunction was modified (i.e. input was not already contained)
	 * @throws AtomAndNegationException
	 *             If the literal with the opposite polarity is already contained in this xjunction.
	 */
	public boolean addTermWithUnknownPolarity(final Term term) throws AtomAndNegationException {
		final Literal literal = new Literal(term);
		return add(literal.getAtom(), literal.getPolarity());
	}

	/**
	 * Adds a literal given as (atom, polarity) pair to this XJunction.
	 *
	 * @return true iff XJunction was modified (i.e. was not already contained)
	 * @throws AtomAndNegationException
	 */
	boolean add(final Term atom, final Polarity polarity) throws AtomAndNegationException {
		final boolean containsNegation = containsNegation(atom, polarity);
		if (containsNegation) {
			// param contained φ as well as (not φ), we return null
			throw new AtomAndNegationException();
		}
		return mPolarityMap.put(atom, polarity) == null;
	}

	/**
	 * @return true iff this XJunction contains the literal given by the pair (atom, polarity).
	 */
	public boolean contains(final Term atom, final Polarity polarity) {
		return mPolarityMap.get(atom) == polarity;
	}

	/**
	 * @return true iff this XJunction contains the negation of the literal given by the pair (atom, polarity).
	 */
	public boolean containsNegation(final Term term, final Polarity polarity) {
		final Polarity existing = mPolarityMap.get(term);
		if (existing != null) {
			return existing != polarity;
		}
		return false;
	}

	/**
	 * @return a list of terms such that each term represents one literal of this XJunction.
	 */
	public List<Term> toTermList(final Script script) {
		final List<Term> result = new ArrayList<>(mPolarityMap.size());
		for (final Entry<Term, Polarity> entry : mPolarityMap.entrySet()) {
			if (entry.getValue() == Polarity.POSITIVE) {
				result.add(entry.getKey());
			} else {
				result.add(SmtUtils.not(script, entry.getKey()));
			}
		}
		return result;
	}

	/**
	 * Two XJunctions are equivalent if they contain the same literals.
	 */
	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final XJunction other = (XJunction) obj;
		if (mPolarityMap == null) {
			if (other.mPolarityMap != null) {
				return false;
			}
		} else if (!mPolarityMap.equals(other.mPolarityMap)) {
			return false;
		}
		return true;
	}

	/**
	 * Hashcode of the underlying Map
	 */
	@Override
	public int hashCode() {
		return mPolarityMap.hashCode();
	}

	/**
	 * @return All literals of this XJunction as (atom,polarity) pairs.
	 */
	public Set<Entry<Term, Polarity>> entrySet() {
		return Collections.unmodifiableSet(mPolarityMap.entrySet());
	}

	/**
	 * @return numer of literals of this XJunction.
	 */
	public int size() {
		return mPolarityMap.size();
	}

	/**
	 * @return the polarity of a given atom and null if no literal with that atom is contained.
	 */
	public Polarity getPolarity(final Term atom) {
		return mPolarityMap.get(atom);
	}

	/**
	 * Returns the literal (atom, polarity) for the given atom.
	 *
	 * @return The polarity of the removed literal and null if no literal with this atom was contained.
	 */
	public Polarity remove(final Term atom) {
		return mPolarityMap.remove(atom);
	}

	@Override
	public String toString() {
		return mPolarityMap.toString();
	}

	/**
	 * @return true iff all literals of this XJunction are a subset of the given XJunction.
	 */
	public boolean isSubset(final XJunction xjunction) {
		if (xjunction.size() < size()) {
			return false;
		}
		return xjunction.mPolarityMap.entrySet().containsAll(mPolarityMap.entrySet());
	}

	/**
	 * Exception that is thrown if a modification of a XJunction would result in a set where an literal and its negation
	 * are contained.
	 *
	 * @author Matthias Heizmann
	 *
	 */
	public class AtomAndNegationException extends Exception {
		private static final long serialVersionUID = -5506932837927008768L;
	}

	/**
	 * @return Returns the disjoint union of two XJunctions
	 * @throws AtomAndNegationException
	 *             if the result would contain a positive and a negative literal for the same atom.
	 * @throws IllegalArgumentException
	 *             if both XJunctions are not disjoint.
	 */
	public static XJunction disjointUnion(final XJunction xjunction1, final XJunction xjunction2)
			throws AtomAndNegationException {
		final XJunction result = new XJunction(xjunction1);
		for (final Entry<Term, Polarity> atom : xjunction2.entrySet()) {
			final boolean modified = result.add(atom.getKey(), atom.getValue());
			if (!modified) {
				throw new IllegalArgumentException("inputs were not disjoint");
			}
		}
		return result;
	}
}
