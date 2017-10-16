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


package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;


import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.automata.StateWa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.IntIterator;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.IntSet;

/**
 * @author Yong Li (liyong@ios.ac.cn)
 * */

public class StateWA<LETTER, STATE> extends StateWa {

	private WaToBuchiWrapper<LETTER, STATE> mBuchi;
	
	private Set<Integer> mEnabledLetters;
	
	public StateWA(WaToBuchiWrapper<LETTER, STATE> buchi, int id) {
		super(id);
		this.mBuchi = buchi;
		this.mEnabledLetters = new HashSet<>();
	}
	
	@Override
	public Set<Integer> getEnabledLetters() {
		return Collections.unmodifiableSet(mEnabledLetters);
	}
	
	// support on-the-fly exploration
	@Override
	public IntSet getSuccessors(int letter) {
		if(mEnabledLetters.contains(letter)) {
			return super.getSuccessors(letter);
		}else {
			mEnabledLetters.add(letter);
			IntSet succs = mBuchi.computeSuccessors(getId(), letter);
			IntIterator iter = succs.iterator();
			while(iter.hasNext()) {
				super.addSuccessor(letter, iter.next());
			}
			return succs;
		}
	}
	
	

}
