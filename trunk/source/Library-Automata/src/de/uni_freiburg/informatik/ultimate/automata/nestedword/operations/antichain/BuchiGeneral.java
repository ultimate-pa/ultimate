/*
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

package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.antichain;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.Collection;
import java.util.Collections;
import java.util.List;


/**
 * @author Yong Li (liyong@ios.ac.cn)
 * */
public class BuchiGeneral implements IBuchi {

	private final BitSet mInitStates;
	
	private final BitSet mFinalStates;
	
	private final List<IState> mStates;
	
	private final int mAlphabetSize;
	
	public BuchiGeneral(int alphabetSize) {
		this.mAlphabetSize = alphabetSize;
		this.mInitStates  = new BitSet();
		this.mFinalStates = new BitSet();
		this.mStates = new ArrayList<>();
	}
	
	@Override
	public int getAlphabetSize() {
		// TODO Auto-generated method stub
		return mAlphabetSize;
	}

	@Override
	public IState addState() {
		int id = mStates.size();
		mStates.add(new StateGeneral(id));
		return mStates.get(id);
	}
	
	/** should keep it safe */
	@Override
	public int addState(IState state) {
		// TODO Auto-generated method stub
		int id = mStates.size();
		mStates.add(state);
		return id;
	}

	@Override
	public IState getState(int id) {
		// TODO Auto-generated method stub
		if(id < mStates.size()) {
			return mStates.get(id);
		}
		return null;
	}

	@Override
	public BitSet getInitialStates() {
		// TODO Auto-generated method stub
		return (BitSet) mInitStates.clone();
	}

	@Override
	public boolean isInitial(int id) {
		// TODO Auto-generated method stub
		return mInitStates.get(id);
	}

	@Override
	public boolean isFinal(int id) {
		// TODO Auto-generated method stub
		return mFinalStates.get(id);
	}

	@Override
	public void setInitial(int id) {
		// TODO Auto-generated method stub
		mInitStates.set(id);
	}

	@Override
	public void setFinal(int id) {
		// TODO Auto-generated method stub
		mFinalStates.set(id);
	}

	@Override
	public Collection<IState> getStates() {
		// TODO Auto-generated method stub
		return Collections.unmodifiableList(mStates);
	}

	@Override
	public BitSet getFinalStates() {
		// TODO Auto-generated method stub
		return (BitSet) mFinalStates.clone();
	}

	@Override
	public int getStateSize() {
		// TODO Auto-generated method stub
		return mStates.size();
	}
	
	public String toString() {
		return toDot();
	}

	@Override
	public BitSet getSuccessors(int state, int letter) {
		// TODO Auto-generated method stub
		System.out.println("Hello");
		return mStates.get(state).getSuccessors(letter);
	}



}
