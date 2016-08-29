/*
 * Copyright (C) 2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Carl Kuesters
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

import java.util.BitSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

public class BooleanExpression {

	public BooleanExpression(final BitSet alpha, final BitSet beta) {
		this.mAlpha = alpha;
		this.mBeta = beta;
	}
	
	private final BitSet mAlpha;
	private final BitSet mBeta;
	private BooleanExpression mNextConjunctExpression;
	
	public void addConjunction(final BooleanExpression booleanExpression) {
		if (!containsConjunction(booleanExpression)) {
			if (mNextConjunctExpression != null) {
				mNextConjunctExpression.addConjunction(booleanExpression);
			} else {
				mNextConjunctExpression = booleanExpression;
			}
		}
	}
	
	public boolean containsConjunction(final BooleanExpression booleanExpression) {
		if (equals(booleanExpression)) {
			return true;
		} else if (mNextConjunctExpression != null) {
			mNextConjunctExpression.containsConjunction(booleanExpression);
		}
		return false;
	}
	
	public boolean getResult(final BitSet bitVector) {
		final BitSet result = (BitSet) bitVector.clone();
		result.and(mAlpha);
		result.xor(mBeta);
		if (result.isEmpty()) {
			return true;
		} else if (mNextConjunctExpression != null) {
			return mNextConjunctExpression.getResult(bitVector);
		}
		return false;
	}
	
	public BooleanExpression cloneShifted(final Map<Integer,Integer> shiftMap, final int newSize) {
		final BitSet shiftedAlpha = new BitSet(newSize);
		final BitSet shiftedBeta = new BitSet(newSize);
		for (final Entry<Integer, Integer> entry : shiftMap.entrySet()) {
			if (mAlpha.get(entry.getKey())) {
				shiftedAlpha.set(entry.getValue());
			}
			if (mBeta.get(entry.getKey())) {
				shiftedBeta.set(entry.getValue());
			}
		}	
		final BooleanExpression result = new BooleanExpression(shiftedAlpha, shiftedBeta);
		if (mNextConjunctExpression != null) {
			result.mNextConjunctExpression = mNextConjunctExpression.cloneShifted(shiftMap, newSize);
		}	
		return result;
	}
	
	/**
	 * TODO Christian 2016-08-16: This does not override the Object.equals()
	 *      method. It may be confusing when using in Collections.
	 */
	public boolean equals(final BooleanExpression booleanExpression) {
		return (mAlpha.equals(booleanExpression.mAlpha)
				&& mBeta.equals(booleanExpression.mBeta));
	}
	
	public <T> String toString(final List<T> variables) {
		String text = "";
		int r = 0;
		for (int i = 0; i < variables.size(); i++) {
			if (mAlpha.get(i)) {
				if (r != 0) {
					text += " ^ ";
				}
				if (!mBeta.get(i)) {
					text += "~";
				}
				text += variables.get(i);
				r++;
			}
		}
		if (mNextConjunctExpression != null) {
			if (r > 1) {
				text = "(" + text + ")";
			}
			text += " v " + mNextConjunctExpression.toString(variables);
		}
		return text;
	}
	
	public BitSet getAlpha() {
		return mAlpha;
	}
	
	public BitSet getBeta() {
		return mBeta;
	}
	
	public BooleanExpression getNextConjunctExpression() {
		return mNextConjunctExpression;
	}
}
