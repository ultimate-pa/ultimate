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

package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.complement;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.Options;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.automata.IBuchiWa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.automata.StateWa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.IntSet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.UtilIntSet;

public class StateWaNCSB extends StateWa implements IStateWaComplement {


	private final NCSB mNCSB;
	
	private final IBuchiWa mOperand;
	private final BuchiWaComplement mComplement;
	
	public StateWaNCSB(BuchiWaComplement complement, int id, NCSB ncsb) {
		super(id);
		this.mComplement = complement;
		this.mOperand = complement.getOperand();
		this.mNCSB = ncsb;
	}
	
	public NCSB getNCSB() {
		return  mNCSB;
	}

	@Override
	public IBuchiWa getOperand() {
		return this.mOperand;
	}

	@Override
	public IBuchiWa getComplement() {
		return mComplement;
	}	
	
	private IntSet mVisitedLetters = UtilIntSet.newIntSet();
	@Override
	public IntSet getSuccessors(int letter) {
		if(mVisitedLetters.get(letter)) {
			return super.getSuccessors(letter);
		}
		mVisitedLetters.set(letter);
		// B
		SuccessorResult succResult = collectSuccessors(mNCSB.getBSet(), letter, true);
		if(!succResult.hasSuccessor) return UtilIntSet.newIntSet();
		IntSet BSuccs = succResult.mSuccs;
		IntSet minusFSuccs = succResult.mMinusFSuccs;
		IntSet interFSuccs = succResult.mInterFSuccs;

		// C\B
		IntSet cMinusB = mNCSB.copyCSet();
		cMinusB.andNot(mNCSB.getBSet());
		succResult = collectSuccessors(cMinusB, letter, !Options.lazyS);
		if(!succResult.hasSuccessor) return UtilIntSet.newIntSet();
		IntSet CSuccs = succResult.mSuccs;
		CSuccs.or(BSuccs);
		minusFSuccs.or(succResult.mMinusFSuccs);
		interFSuccs.or(succResult.mInterFSuccs);
		
		// N
		succResult = collectSuccessors(mNCSB.getNSet(), letter, false);
		if(!succResult.hasSuccessor) return UtilIntSet.newIntSet();
		IntSet NSuccs = succResult.mSuccs;

		// S
		succResult = collectSuccessors(mNCSB.getSSet(), letter, false);
		if(!succResult.hasSuccessor) return UtilIntSet.newIntSet();
		IntSet SSuccs = succResult.mSuccs;
		
		return computeSuccessors(new NCSB(NSuccs, CSuccs, SSuccs, BSuccs), minusFSuccs, interFSuccs, letter);
	}
	

	public boolean equals(Object obj) {
		if(this == obj) return true;
		if(!(obj instanceof StateWaNCSB)) {
			return false;
		}
		StateWaNCSB other = (StateWaNCSB)obj;
		return  mNCSB.equals(other.mNCSB);
	}
	
	
	public String toString() {
		return mNCSB.toString();
	}
	

	@Override
	public int hashCode() {
		return mNCSB.hashCode();
	}
	// -------------------------------------------------

	/**
	 * If q in C\F or (B\F), then tr(q, a) should not be not empty
	 * */
	private boolean noTransitionAssertion_MinusF(int state, IntSet succs) {
		return !mOperand.isFinal(state) && succs.isEmpty();
	}
	
	private SuccessorResult collectSuccessors(IntSet states, int letter, boolean testTrans) {
		SuccessorResult result = new SuccessorResult();
		for(final int state : states.iterable()) {
			IntSet succs = mOperand.getSuccessors(state, letter);
			if (testTrans && noTransitionAssertion_MinusF(state, succs)) {
				result.hasSuccessor = false;
				return result;
			}
			result.mSuccs.or(succs);
			if(testTrans) {
				if(mOperand.isFinal(state)) {
					result.mInterFSuccs.or(succs);
				}else {
					result.mMinusFSuccs.or(succs);
				}
			}
		}
		return result;
	}
	
	private IntSet computeSuccessors(NCSB succNCSB, IntSet minusFSuccs
			, IntSet interFSuccs, int letter) {
		// check d(S) and d(C)
		if(succNCSB.getSSet().overlap(mOperand.getFinalStates())
		|| minusFSuccs.overlap(succNCSB.getSSet())) {
			return UtilIntSet.newIntSet();
		}
		SuccessorGenerator generator = new SuccessorGenerator(mNCSB.getBSet().isEmpty()
															, succNCSB
															, minusFSuccs
															, interFSuccs
															, mOperand.getFinalStates());
		IntSet succs = UtilIntSet.newIntSet();
		while(generator.hasNext()) {
		    NCSB ncsb = generator.next();
		    if(ncsb == null) continue;
			StateWaNCSB succ = mComplement.addState(ncsb);
			super.addSuccessor(letter, succ.getId());
			succs.set(succ.getId());
		}

		return succs;
	}

}
