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
import java.util.HashMap;

/**
 * Salomaa style representation of a DNF as a list of conjunctions.
 * Each conjunction is stored as two ints.
 * alpha says which state variables appear in the conjunction.
 * beta says whether the appearing ones appear positive or negative.
 */
public class DNFAsBitSetList {
	private BitSet mAlpha;
	private final BitSet mBeta;
	private DNFAsBitSetList mNext;

	/**
	 * @param alpha which state variables appear in the conjunction
	 * @param beta whether the appearing variables appear positive or negative
	 * @param next next
	 */
	public DNFAsBitSetList(final BitSet alpha, final BitSet beta, final DNFAsBitSetList next) {
		this.mAlpha = alpha;
		this.mBeta = beta;
		this.mNext = next;
	}

	/**
	 * copy constructor, yields another linked list of DNFAsInts, with new objects ("deep copy")
	 * @param daa next
	 */
	public DNFAsBitSetList(final DNFAsBitSetList daa) {
		this((BitSet) daa.mAlpha.clone(), (BitSet) daa.mBeta.clone(), null);
		DNFAsBitSetList nextEl = mNext;
		while (nextEl != null) {
			insert(new DNFAsBitSetList((BitSet) nextEl.mAlpha.clone(), (BitSet) nextEl.mBeta.clone(), null));
			nextEl = nextEl.mNext;
		}
	}
	
	public void insert(final DNFAsBitSetList dai) {
		if (mNext == null) {
			mNext = dai;
		} else {
			mNext.insert(dai);
		}
	}
	
	/**
	 * "this" is a DNF where the indexes refer to the entries of oldStateList. This method
	 * yields a DNF whose indexes refer to the predicates as given by newStateToIndex.
	 * @param oldStateList List indicating the old (predicate -> index) mapping
	 * @param newStateToIndex HashMap indicating the new (predicate -> index) mapping
	 */
	public <STATE> DNFAsBitSetList rewriteWithNewStateList(
			final ArrayList<STATE> oldStateList,
			final HashMap<STATE, Integer> newStateToIndex) {
		final DNFAsBitSetList newDNF = new DNFAsBitSetList(this);
		DNFAsBitSetList current = newDNF;
		while (current != null) {
			current.mAlpha = rewriteBitSet(mAlpha, oldStateList, newStateToIndex);
			current = current.mNext;
		}
		return null;
	}
	
	/**
	 * Helper method for rewriteWithNewStateList.
	 */
	private <STATE> BitSet rewriteBitSet(final BitSet bs, final ArrayList<STATE> oldStateList, 
			final HashMap<STATE, Integer> newStateToIndex) {
		final BitSet newBs = new BitSet();
		int setBit = bs.nextSetBit(0);
		while (setBit != -1) {
			newBs.set(newStateToIndex.get(oldStateList.get(setBit)));
			setBit = bs.nextSetBit(setBit + 1);
		}
		return newBs;
	}
	
	public void prettyPrintDNF(final StringBuilder sb, final ArrayList stateList) {
		if (sb.toString().equals("")) {
			sb.append(" \\/ (");
		}
		
		String comma = "";
		for (int i = 0; i < stateList.size(); i++) {
			if (!mAlpha.isEmpty() && i == 0) {
				sb.append(" /\\ {");
			}
			final boolean isStateVariablePresent = mAlpha.get(i);
			final boolean isStateVariablePositive = mBeta.get(i);
			if (isStateVariablePresent) {
				if (!isStateVariablePositive) {
					sb.append(" not");
				}
				sb.append(comma + stateList.get(i)); // or put the state here?
				comma = ", ";
			}
			if (!mAlpha.isEmpty() && i == stateList.size() - 1) {
				sb.append("}, ");
			}
		}
		if (mNext != null) {
			mNext.prettyPrintDNF(sb, stateList);
		} else {
			sb.append(")\n");
		}
	}

	public boolean applyTo(final BitSet u) {
		final BitSet alphaAndUXorBeta = (BitSet) mAlpha.clone();
		alphaAndUXorBeta.and(u);
		alphaAndUXorBeta.xor(mBeta);
//		Salomaa(2010): f(u) = 1 <-> (alpha & u) xor beta == 0
		if (alphaAndUXorBeta.isEmpty()) {
			return true;
		} else if (mNext == null) {
			return false;
		} else {
			return mNext.applyTo(u);
		}
	}
}
