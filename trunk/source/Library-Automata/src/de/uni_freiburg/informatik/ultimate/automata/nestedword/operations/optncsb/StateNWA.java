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

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.automata.StateNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.IntIterator;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.IntSet;

/**
 * @author Yong Li (liyong@ios.ac.cn)
 */

public class StateNWA<LETTER, STATE> extends StateNwa {

	private final NwaToBuchiWrapper<LETTER, STATE> mBuchi;

	public StateNWA(final NwaToBuchiWrapper<LETTER, STATE> buchi, final int id) {
		super(buchi, id);
		mBuchi = buchi;
	}

	// support on-the-fly exploration
	@Override
	public IntSet getSuccessorsInternal(final int letter) {
		if (super.getEnabledLettersInternal().contains(letter)) {
			return super.getSuccessorsInternal(letter);
		} else {
			final IntSet succs = mBuchi.computeSuccessorsInternal(getId(), letter);
			final IntIterator iter = succs.iterator();
			while (iter.hasNext()) {
				super.addSuccessorInternal(letter, iter.next());
			}
			return succs;
		}
	}

	@Override
	public IntSet getSuccessorsCall(final int letter) {
		if (super.getEnabledLettersCall().contains(letter)) {
			return super.getSuccessorsCall(letter);
		} else {
			final IntSet succs = mBuchi.computeSuccessorsCall(getId(), letter);
			final IntIterator iter = succs.iterator();
			while (iter.hasNext()) {
				super.addSuccessorCall(letter, iter.next());
			}
			return succs;
		}
	}

	@Override
	public IntSet getSuccessorsReturn(final int hier, final int letter) {
		if (super.getEnabledLettersReturn().contains(letter) && super.getEnabledHiersReturn(letter).contains(hier)) {
			return super.getSuccessorsReturn(hier, letter);
		} else {
			final IntSet succs = mBuchi.computeSuccessorsReturn(getId(), hier, letter);
			final IntIterator iter = succs.iterator();
			while (iter.hasNext()) {
				super.addSuccessorReturn(hier, letter, iter.next());
			}
			return succs;
		}
	}

}
