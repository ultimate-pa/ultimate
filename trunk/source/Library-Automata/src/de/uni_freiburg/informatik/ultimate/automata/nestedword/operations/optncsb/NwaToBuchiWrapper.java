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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.automata.BuchiNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.automata.IStateNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.IntSet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.UtilIntSet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;

/**
 * @author Yong Li (liyong@ios.ac.cn)
 */

// TODO support on-demand exploration
public class NwaToBuchiWrapper<LETTER, STATE> extends BuchiNwa {

	private final Map<LETTER, Integer> mLetterMap;
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mInnerBuchi;

	private final Map<STATE, IStateNwa> mStateMap;
	private final List<STATE> mStateArr;
	private final List<LETTER> mLetterArr;

	public NwaToBuchiWrapper(final IntSet mAlphabetCall, final IntSet mAlphabetInternal, final IntSet mAlphabetReturn,
			final Map<LETTER, Integer> letterMap, final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> buchi) {
		super(mAlphabetCall, mAlphabetInternal, mAlphabetReturn);
		mLetterMap = letterMap;
		mInnerBuchi = buchi;
		mStateMap = new HashMap<>();
		mStateArr = new ArrayList<>();
		mLetterArr = new ArrayList<>(mLetterMap.size());
		for (int i = 0; i < mLetterMap.size(); i++) {
			mLetterArr.add(null);
		}
		for (final Entry<LETTER, Integer> entry : mLetterMap.entrySet()) {
			assert entry.getValue() < mLetterMap.size();
			mLetterArr.set(entry.getValue(), entry.getKey());
		}
		computeInitialStates();
	}

	private IStateNwa getOrAddState(final STATE str) {
		IStateNwa state = mStateMap.get(str);
		if (state == null) {
			state = addState();
			mStateMap.put(str, state);
			mStateArr.add(str);
			if (mInnerBuchi.isFinal(str)) {
				this.setFinal(state.getId());
			}
		}
		return state;
	}

	private void computeInitialStates() {
		final Iterable<STATE> states = mInnerBuchi.getInitialStates();
		for (final STATE s : states) {
			final IStateNwa state = getOrAddState(s);
			this.setInitial(state);
		}
	}

	@Override
	public StateNWA<LETTER, STATE> makeState(final int id) {
		return new StateNWA<>(this, id);
	}

	protected IntSet computeSuccessorsCall(final int state, final int letter) {
		assert getAlphabetCall().get(letter);

		final LETTER letterStr = mLetterArr.get(letter);
		final STATE currStateStr = mStateArr.get(state);

		final IntSet succs = UtilIntSet.newIntSet();
		final Iterable<OutgoingCallTransition<LETTER, STATE>> transIter =
				mInnerBuchi.callSuccessors(currStateStr, letterStr);
		for (final OutgoingCallTransition<LETTER, STATE> trans : transIter) {
			final IStateNwa succ = getOrAddState(trans.getSucc());
			final Integer letterId = mLetterMap.get(trans.getLetter());
			assert letterId == letter;
			succs.set(succ.getId());
		}

		return succs;
	}

	protected IntSet computeSuccessorsInternal(final int state, final int letter) {
		assert getAlphabetInternal().get(letter);

		final LETTER letterStr = mLetterArr.get(letter);
		final STATE currStateStr = mStateArr.get(state);

		final IntSet succs = UtilIntSet.newIntSet();
		final Iterable<OutgoingInternalTransition<LETTER, STATE>> transIter =
				mInnerBuchi.internalSuccessors(currStateStr, letterStr);
		for (final OutgoingInternalTransition<LETTER, STATE> trans : transIter) {
			final IStateNwa succ = getOrAddState(trans.getSucc());
			final Integer letterId = mLetterMap.get(trans.getLetter());
			assert letterId == letter;
			succs.set(succ.getId());
		}

		return succs;
	}

	protected IntSet computeSuccessorsReturn(final int state, final int hier, final int letter) {
		assert getAlphabetReturn().get(letter);
		final LETTER letterStr = mLetterArr.get(letter);
		final STATE currStateStr = mStateArr.get(state);
		final STATE currHierStr = mStateArr.get(hier);

		final IntSet succs = UtilIntSet.newIntSet();
		final Iterable<OutgoingReturnTransition<LETTER, STATE>> transIter =
				mInnerBuchi.returnSuccessors(currStateStr, currHierStr, letterStr);
		for (final OutgoingReturnTransition<LETTER, STATE> trans : transIter) {
			final IStateNwa succ = getOrAddState(trans.getSucc());
			final Integer letterId = mLetterMap.get(trans.getLetter());
			assert letterId == letter;
			succs.set(succ.getId());
		}

		return succs;
	}

	public STATE getNwaSTATE(final int sid) {
		return mStateArr.get(sid);
	}

	public LETTER getNwaLETTER(final int aid) {
		return mLetterArr.get(aid);
	}

}
