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



public class BuchiWa implements IBuchiWa {

	private final IntSet mInitStates;
	
	private final IntSet mFinalStates;
	
	private final List<IStateWa> mStates;
	
	private final int mAlphabetSize;
		
	public BuchiWa(int alphabetSize) {
		this.mAlphabetSize = alphabetSize;
		this.mInitStates  = UtilIntSet.newIntSet();
		this.mFinalStates = UtilIntSet.newIntSet();
		this.mStates = new ArrayList<>();
	}
	
	@Override
	public int getAlphabetSize() {
		return mAlphabetSize;
	}

	@Override
	public IStateWa addState() {
		int id = mStates.size();
		mStates.add(makeState(id));
		return mStates.get(id);
	}
	
	@Override
	public IStateWa makeState(int id) {
		return new StateWa(id);
	}
	
	/** should keep it safe */
	@Override
	public int addState(IStateWa state) {
		int id = mStates.size();
		mStates.add(state);
		return id;
	}

	@Override
	public IStateWa getState(int id) {
		assert id < mStates.size();
		if(id < mStates.size()) {
			return mStates.get(id);
		}
		return null;
	}

	@Override
	public IntSet getInitialStates() {
		return mInitStates;
	}

	@Override
	public boolean isInitial(int id) {
		return mInitStates.get(id);
	}

	@Override
	public boolean isFinal(int id) {
		return mFinalStates.get(id);
	}

	@Override
	public void setInitial(int id) {
		mInitStates.set(id);
	}

	@Override
	public void setFinal(int id) {
		mFinalStates.set(id);
	}

	@Override
	public Collection<IStateWa> getStates() {
		return Collections.unmodifiableList(mStates);
	}

	@Override
	public IntSet getFinalStates() {
		return mFinalStates;
	}

	@Override
	public int getStateSize() {
		return mStates.size();
	}
	
	public String toString() {
		return toDot();
	}

	@Override
	public IntSet getSuccessors(int state, int letter) {
		return mStates.get(state).getSuccessors(letter);
	}

	protected Acc acc;
	
	@Override
	public Acc getAcceptance() {
		if(acc == null) {
			acc = new AccBuchi(mFinalStates);
		}
		return acc;
	}

	@Override
	public void makeComplete() {
		IStateWa deadState = addState();
		for(final IStateWa state : mStates) {
            for (int letter = 0; letter < getAlphabetSize(); letter ++) {
            	IntSet succs = state.getSuccessors(letter);
            	if(succs.cardinality() == 0) {
            		state.addSuccessor(letter, deadState.getId());
            	}
            }
        }
	}

}
