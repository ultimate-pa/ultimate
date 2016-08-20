/*
 * Copyright (C) 2014-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automata Library.
 * 
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

/**
 * Salomaa style representation of a DNF as a list of conjunctions.
 * Each conjunction is stored as two {@code int}s.
 * alpha says which state variables appear in the conjunction.
 * beta says whether the appearing ones appear positive or negative.
 * 
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 */
public class DNFAsBitSetList {
	private BitSet mAlpha;
	private final BitSet mBeta;
	private DNFAsBitSetList mNext;
	
	/**
	 * Standard constructor.
	 * 
	 * @param alpha
	 *            which state variables appear in the conjunction
	 * @param beta
	 *            whether the appearing variables appear positive or negative
	 * @param next
	 *            next conjunction (next-pointer in the list)
	 */
	public DNFAsBitSetList(final BitSet alpha, final BitSet beta, final DNFAsBitSetList next) {
		mAlpha = alpha;
		mBeta = beta;
		mNext = next;
	}
	
	/**
	 * Copy constructor ("deep copy").
	 * 
	 * @param obj
	 *            object to copy
	 */
	public DNFAsBitSetList(final DNFAsBitSetList obj) {
		this((BitSet) obj.mAlpha.clone(), (BitSet) obj.mBeta.clone(), null);
		/*
		 * TODO Christian 2016-08-20: I fixed this, the pointer of the object should be used, this.mNext was set to
		 *      'null'. Remove this comment and the following commented line after testing/agreeing.
		 */
		// DNFAsBitSetList nextEl = mNext;
		DNFAsBitSetList nextEl = obj.mNext;
		while (nextEl != null) {
			insert(new DNFAsBitSetList((BitSet) nextEl.mAlpha.clone(), (BitSet) nextEl.mBeta.clone(), null));
			nextEl = nextEl.mNext;
		}
	}
	
	/**
	 * @param elem
	 *            Element to insert.
	 */
	public void insert(final DNFAsBitSetList elem) {
		if (mNext == null) {
			mNext = elem;
		} else {
			mNext.insert(elem);
		}
	}
	
	/**
	 * "this" is a DNF where the indices refer to the entries of oldStateList. This method
	 * yields a DNF whose indices refer to the predicates as given by newStateToIndex.
	 * 
	 * @param oldStateList
	 *            List indicating the old (predicate -> index) mapping
	 * @param newStateToIndex
	 *            Map indicating the new (predicate -> index) mapping
	 * @param <STATE>
	 *            state type
	 * @return new DNF
	 */
	public <STATE> DNFAsBitSetList rewriteWithNewStateList(
			final ArrayList<STATE> oldStateList,
			final Map<STATE, Integer> newStateToIndex) {
		DNFAsBitSetList current = new DNFAsBitSetList(this);
		do {
			current.mAlpha = rewriteBitSet(mAlpha, oldStateList, newStateToIndex);
			current = current.mNext;
		} while (current != null);
		return null;
	}
	
	/**
	 * Helper method for {@link #rewriteWithNewStateList()}.
	 */
	private <STATE> BitSet rewriteBitSet(final BitSet bs, final ArrayList<STATE> oldStateList,
			final Map<STATE, Integer> newStateToIndex) {
		final BitSet newBs = new BitSet();
		int setBit = bs.nextSetBit(0);
		while (setBit != -1) {
			newBs.set(newStateToIndex.get(oldStateList.get(setBit)));
			setBit = bs.nextSetBit(setBit + 1);
		}
		return newBs;
	}
	
	/**
	 * Pretty printer to a provided {@link StringBuilder}.
	 * 
	 * @param sb
	 *            string builder
	 * @param stateList
	 *            list of states
	 * @param <STATE>
	 *            state type
	 */
	public <STATE> void prettyPrintDnf(final StringBuilder sb, final List<STATE> stateList) {
		if (sb.length() == 0) {
			sb.append(" \\/ (");
		}
		
		String comma = "";
		final Iterator<STATE> it = stateList.iterator();
		for (int i = 0; i < stateList.size(); i++) {
			final STATE state = it.next();
			if (!mAlpha.isEmpty() && i == 0) {
				sb.append(" /\\ {");
			}
			final boolean isStateVariablePresent = mAlpha.get(i);
			final boolean isStateVariablePositive = mBeta.get(i);
			if (isStateVariablePresent) {
				if (!isStateVariablePositive) {
					sb.append(" not");
				}
				sb.append(comma + state);
				comma = ", ";
			}
			if (!mAlpha.isEmpty() && i == stateList.size() - 1) {
				sb.append("}, ");
			}
		}
		if (mNext != null) {
			mNext.prettyPrintDnf(sb, stateList);
		} else {
			sb.append(")\n");
		}
	}
	
	/**
	 * Function application to a {@link BitSet}.
	 * This is the same as an evaluation under a given assignment.
	 * <p>
	 * The idea (Salomaa 2010) is as follows:<br>
	 * <tt>f(u) = 1 <-> (alpha & u) xor beta == 0</tt>
	 * 
	 * @param u
	 *            bit set to apply to
	 * @return result of function application
	 */
	public boolean applyTo(final BitSet u) {
		final BitSet alphaAndUxorBeta = (BitSet) mAlpha.clone();
		alphaAndUxorBeta.and(u);
		alphaAndUxorBeta.xor(mBeta);
		
		if (alphaAndUxorBeta.isEmpty()) {
			return true;
		} else if (mNext == null) {
			return false;
		} else {
			return mNext.applyTo(u);
		}
	}
}
