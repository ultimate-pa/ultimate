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

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.IntSet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.UtilIntSet;


public class BuchiNwa implements IBuchiNwa {
	
	private final IntSet mInitialStates;
	private final IntSet mFinalStates;
	private final List<IStateNwa> mStates;
	private final IntSet mCallAlphabet;
	private final IntSet mInternalAlphabet;
	private final IntSet mReturnAlphabet;
	
	
	public BuchiNwa(IntSet aCall, IntSet aInternal, IntSet aReturn) {
		this.mInitialStates = UtilIntSet.newIntSet();
		this.mFinalStates = UtilIntSet.newIntSet();
		this.mStates = new ArrayList<>();
		this.mCallAlphabet = aCall.clone();
		this.mInternalAlphabet = aInternal.clone();
		this.mReturnAlphabet = aReturn.clone();
	}

	@Override
	public Acc getAcceptance() {
		return new AccBuchi(mFinalStates);
	}

	@Override
	public IntSet getAlphabetInternal() {
		return mInternalAlphabet;
	}

	@Override
	public IntSet getAlphabetCall() {
		return mCallAlphabet;
	}

	@Override
	public IntSet getAlphabetReturn() {
		return mReturnAlphabet;
	}

	@Override
	public int getStateSize() {
		return mStates.size();
	}

	@Override
	public IStateNwa addState() {
		int id = mStates.size();
		IStateNwa state = makeState(id);
		mStates.add(state);
		assert state == mStates.get(id);
		return state;
	}

	@Override
	public int addState(IStateNwa state) {
		int id = mStates.size();
		mStates.add(state);
		return id;
	}

	@Override
	public IStateNwa getState(int id) {
		if(id < mStates.size()) {
			return mStates.get(id);
		}
		return null;
	}

	@Override
	public IntSet getInitialStates() {
		return mInitialStates;
	}

	@Override
	public IntSet getFinalStates() {
		return mFinalStates;
	}

	@Override
	public boolean isInitial(int id) {
		return mInitialStates.get(id);
	}

	@Override
	public boolean isFinal(int id) {
		return mFinalStates.get(id);
	}

	@Override
	public void setInitial(int id) {
		mInitialStates.set(id);
	}

	@Override
	public void setFinal(int id) {
		mFinalStates.set(id);
	}

	@Override
	public IntSet getSuccessorsInternal(int state, int letter) {
		assert state < mStates.size();
		return getState(state).getSuccessorsInternal(letter);
	}

	@Override
	public IntSet getSuccessorsCall(int state, int letter) {
		assert state < mStates.size();
		return getState(state).getSuccessorsCall(letter);
	}

	@Override
	public IntSet getSuccessorsReturn(int state, int hier, int letter) {
		assert state < mStates.size();
		return getState(state).getSuccessorsReturn(hier, letter);
	}

	@Override
	public Collection<IStateNwa> getStates() {
		return Collections.unmodifiableList(mStates);
	}

	@Override
	public IStateNwa makeState(int id) {
		return new StateNwa(this, id);
	}


}
