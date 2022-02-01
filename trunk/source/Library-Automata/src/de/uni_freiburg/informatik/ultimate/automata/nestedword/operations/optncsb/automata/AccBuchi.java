/*
 * Copyright (C) 2017 Yong Li (liyong@ios.ac.cn)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.automata;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.IntSet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.UtilIntSet;



public class AccBuchi implements Acc {

	private final IntSet mFinalStates;
	public static final int ACC_SIZE_ONE = 1; 
	public static final int ACC_LABEL_ZERO = 0;
	
	public AccBuchi(IntSet finalStates) {
		this.mFinalStates = finalStates;
	}
	
	@Override
	public boolean isAccepted(IntSet set) {
		return mFinalStates.overlap(set);
	}

	@Override
	public IntSet getLabels(int state) {
		IntSet labels = UtilIntSet.newIntSet();
		if(mFinalStates.get(state)) {
			labels.set(ACC_LABEL_ZERO);
		}
		return labels;
	}

	@Override
	public int getAccSize() {
		return ACC_SIZE_ONE;
	}

	@Override
	public void setLabel(int state, int label) {
		if(label != ACC_LABEL_ZERO) {
			return ;
		}
		mFinalStates.set(state);
	}

	@Override
	public void setLabel(int state, IntSet labels) {
		for(final int label : labels.iterable()) {
			if(label != ACC_LABEL_ZERO) {
				return ;
			}
		}
		mFinalStates.set(state);
	}

}
