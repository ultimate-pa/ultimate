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
package de.uni_freiburg.informatik.ultimate.automata.alternating;

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
public class DnfAsBitSetList {
	private BitSet mAlpha;
	private final BitSet mBeta;
	private DnfAsBitSetList mNext;
	
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
	public DnfAsBitSetList(final BitSet alpha, final BitSet beta, final DnfAsBitSetList next) {
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
	public DnfAsBitSetList(final DnfAsBitSetList obj) {
		this((BitSet) obj.mAlpha.clone(), (BitSet) obj.mBeta.clone(), null);
		/*
		 * TODO Christian 2016-08-20: I fixed this, the pointer of the object should be used, this.mNext was set to
		 *      'null'. Remove this comment and the following commented line after testing/agreeing.
		 */
		// DNFAsBitSetList nextEl = mNext;
		DnfAsBitSetList nextEl = obj.mNext;
		while (nextEl != null) {
			insert(new DnfAsBitSetList((BitSet) nextEl.mAlpha.clone(), (BitSet) nextEl.mBeta.clone(), null));
			nextEl = nextEl.mNext;
		}
	}
	
	/**
	 * @param elem
	 *            Element to insert.
	 */
	public final void insert(final DnfAsBitSetList elem) {
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
	public <STATE> DnfAsBitSetList rewriteWithNewStateList(
			final ArrayList<STATE> oldStateList,
			final Map<STATE, Integer> newStateToIndex) {
		DnfAsBitSetList current = new DnfAsBitSetList(this);
		do {
			current.mAlpha = rewriteBitSet(mAlpha, oldStateList, newStateToIndex);
			current = current.mNext;
		} while (current != null);
		return null;
	}
	
	/**
	 * Helper method for {@link #rewriteWithNewStateList()}.
	 */
	private <STATE> BitSet rewriteBitSet(final BitSet bitSet, final ArrayList<STATE> oldStateList,
			final Map<STATE, Integer> newStateToIndex) {
		final BitSet newBitSet = new BitSet();
		int setBit = bitSet.nextSetBit(0);
		while (setBit != -1) {
			newBitSet.set(newStateToIndex.get(oldStateList.get(setBit)));
			setBit = bitSet.nextSetBit(setBit + 1);
		}
		return newBitSet;
	}
	
	/**
	 * Pretty printer to a provided {@link StringBuilder}.
	 * 
	 * @param builder
	 *            string builder
	 * @param stateList
	 *            list of states
	 * @param <STATE>
	 *            state type
	 */
	public <STATE> void prettyPrintDnf(final StringBuilder builder, final List<STATE> stateList) {
		if (builder.length() == 0) {
			builder.append(" \\/ (");
		}
		
		String comma = "";
		final Iterator<STATE> iterator = stateList.iterator();
		for (int i = 0; i < stateList.size(); i++) {
			final STATE state = iterator.next();
			if (!mAlpha.isEmpty() && i == 0) {
				builder.append(" /\\ {");
			}
			final boolean isStateVariablePresent = mAlpha.get(i);
			final boolean isStateVariablePositive = mBeta.get(i);
			if (isStateVariablePresent) {
				if (!isStateVariablePositive) {
					builder.append(" not");
				}
				builder.append(comma);
				builder.append(state);
				comma = ", ";
			}
			if (!mAlpha.isEmpty() && i == stateList.size() - 1) {
				builder.append("}, ");
			}
		}
		if (mNext == null) {
			builder.append(")\n");
		} else {
			mNext.prettyPrintDnf(builder, stateList);
		}
	}
	
	/**
	 * Function application to a {@link BitSet}.
	 * This is the same as an evaluation under a given assignment.
	 * <p>
	 * The idea (Salomaa 2010) is as follows:<br>
	 * <tt>f(u) = 1 <-> (alpha & u) xor beta == 0</tt>
	 * 
	 * @param argumentU
	 *            bit set to apply to
	 * @return result of function application
	 */
	public boolean applyTo(final BitSet argumentU) {
		final BitSet alphaAndUxorBeta = (BitSet) mAlpha.clone();
		alphaAndUxorBeta.and(argumentU);
		alphaAndUxorBeta.xor(mBeta);
		
		if (alphaAndUxorBeta.isEmpty()) {
			return true;
		} else if (mNext == null) {
			return false;
		} else {
			return mNext.applyTo(argumentU);
		}
	}
}
