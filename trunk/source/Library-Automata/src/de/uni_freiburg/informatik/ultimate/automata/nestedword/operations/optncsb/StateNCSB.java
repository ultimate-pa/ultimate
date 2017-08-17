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

import java.util.BitSet;
import java.util.HashSet;
import java.util.Set;


/**
 * @author Yong Li (liyong@ios.ac.cn)
 * */

public class StateNCSB extends StateGeneral implements IStateComplement {

	private BitSet mNSet;
	private BitSet mCSet;
	private BitSet mSSet;
	private BitSet mBSet;
	
	private final IBuchi mOperand;
	private final BuchiComplementSDBA mComplement;
	
	public StateNCSB(int id, BuchiComplementSDBA complement) {
		super(id);
		// TODO Auto-generated constructor stub
		this.mComplement = complement;
		this.mOperand = complement.getOperand();
		this.mNSet = new BitSet();
		this.mCSet = new BitSet();
		this.mSSet = new BitSet();
		this.mBSet = new BitSet();
	}
	
	public void setSets(BitSet N, BitSet C, BitSet S, BitSet B) {
		this.mNSet = (BitSet) N.clone();
		this.mCSet = (BitSet) C.clone();
		this.mSSet = (BitSet) S.clone();
		this.mBSet = (BitSet) B.clone();
	}
	
	public BitSet getNSet() {
		return (BitSet) mNSet.clone();
	}
	
	public BitSet getCSet() {
		return (BitSet) mCSet.clone();
	}
	
	public BitSet getSSet() {
		return (BitSet) mSSet.clone();
	}
	
	public BitSet getBSet() {
		return (BitSet) mBSet.clone();
	}

	@Override
	public IBuchi getOperand() {
		return this.mOperand;
	}

	@Override
	public IBuchi getComplement() {
		return mComplement;
	}
	
	// support on-the-fly exploration
	private BitSet visitedLetters = new BitSet();
	
	
	/**
	 *  implementation of NCSB complementation algorithm which is adapted from GOAL
	 */
	@Override
	public BitSet getSuccessors(int letter) {
		
		Set<StateNCSB> succs = new HashSet<>();
		
		if(visitedLetters.get(letter)) {
			return super.getSuccessors(letter);
		}
		
		visitedLetters.set(letter);
		
		BitSet currNSet = (BitSet) mNSet.clone();
		BitSet currCSet = (BitSet) mCSet.clone();
		BitSet currSSet = (BitSet) mSSet.clone();
		BitSet currBSet = (BitSet) mBSet.clone();
		/*
		 * If q in C\F, then tr(q, a) is not empty
		 */
		BitSet F = mOperand.getFinalStates();
		BitSet cMinusF = (BitSet) currCSet.clone();
		cMinusF.andNot(F); 
		for (int s = cMinusF.nextSetBit(0); s >= 0; s = cMinusF.nextSetBit(s + 1)) {
			if (mOperand.getSuccessors(s, letter).isEmpty()) {
				return new BitSet();
			}
		}
		// should have successors
		
		/* -------------- compute successors -----------------*/
		BitSet NSuccs = mOperand.getSuccessors(currNSet, letter);
		BitSet CSuccs = mOperand.getSuccessors(currCSet, letter);
		BitSet SSuccs = mOperand.getSuccessors(currSSet, letter);
		BitSet BSuccs = mOperand.getSuccessors(currBSet, letter);
		/* ------------------------------------------------*/
		
		// N successors
		BitSet Np = (BitSet) NSuccs.clone();
				
		Np.andNot(F);            // remove final states
		Np.andNot(CSuccs);       // remove successors of C, the final states of NSuccs are in CSuccs 
		Np.andNot(SSuccs);       // remove successors of S
		
		// C successors
		BitSet Cp = (BitSet) CSuccs.clone();
		BitSet nInterF = (BitSet) NSuccs.clone();
		nInterF.and(F);
		Cp.or(nInterF);
		
		// S successors
		BitSet Sp = (BitSet) SSuccs.clone();
		
		// B successors
		BitSet Bp = (BitSet) BSuccs.clone();
		
		
		/* -------------- compute C' of C -----------------*/
		// firstly compute successors of C\F which must be in C'
		BitSet CMinusFSuccs = mOperand.getSuccessors(cMinusF, letter);
		
		// secondly compute successors of C/\ F which may have final states
		BitSet cInterF = (BitSet) currCSet.clone(); 
		cInterF.and(F);  // get all accepting states in C
		BitSet CInterFSuccs = mOperand.getSuccessors(cInterF, letter);  // get successors of accepting states
		CInterFSuccs.andNot(F);                            // remove accepting state here
		CInterFSuccs.andNot(CMinusFSuccs);         // remove must-in C states
		
		// note that we should remove all final states which may go to S'

		/* ----------- make nondeterministic choices ------------------- */
		// the successors of C /\ F should go to C and S with nondeterministic choices
		
//		System.out.println(CInterFSuccs);
		PowerSet ps = new PowerSet(CInterFSuccs); 
												
		while (ps.hasNext()) {
			BitSet Sextra = ps.next(); // extra states to be added into S'
            BitSet tmp = (BitSet) Sextra.clone();
            tmp.and(CMinusFSuccs);
			if(!tmp.isEmpty()) continue;
			
			BitSet NPrime = Np;
			BitSet CPrime = (BitSet) Cp.clone();
			CPrime.andNot(Sextra);
			BitSet SPrime = (BitSet) Sp.clone();
			SPrime.or(Sextra);
			BitSet BPrime = null;
			if(currBSet.isEmpty()) {
				BPrime = (BitSet) CPrime.clone();
			}else {
				BPrime = (BitSet) Bp.clone();
				BPrime.andNot(Sextra);
			}

			if (hasNoOverlap(SPrime, F) && hasNoOverlap(CPrime, SPrime)) {
				StateNCSB succ = mComplement.addState(NPrime, CPrime, SPrime, BPrime);
				this.addSuccessor(letter, succ.getId());
				succs.add(succ);
			}
		}

		return super.getSuccessors(letter);
	}
	
	private boolean hasNoOverlap(BitSet set1, BitSet set2) {
		BitSet tmp = (BitSet) set1.clone();
		tmp.and(set2);
		return tmp.isEmpty();
	}
	
//	@Override
	public BitSet getSuccessors2(int letter) {
		
		Set<StateNCSB> succs = new HashSet<>();
		
		if(visitedLetters.get(letter)) {
			return super.getSuccessors(letter);
		}
		
		visitedLetters.set(letter);
		
		BitSet currNSet = (BitSet) mNSet.clone();
		BitSet currCSet = (BitSet) mCSet.clone();
		BitSet currSSet = (BitSet) mSSet.clone();
		BitSet currBSet = (BitSet) mBSet.clone();
		/*
		 * If q in C\F, then tr(q, a) is not empty
		 */
		boolean wrong = false;
		BitSet F = mOperand.getFinalStates();
		BitSet cMinusF = (BitSet) currCSet.clone();
		cMinusF.andNot(F); 
		for (int s = cMinusF.nextSetBit(0); s >= 0; s = cMinusF.nextSetBit(s + 1)) {
			if (mOperand.getSuccessors(s, letter).isEmpty()) {
				wrong = true;
				break;
			}
		}// should have successors
		
		// if guess is wrong, then empty
		if (wrong) return new BitSet();
		
		/* -------------- compute B' of B -----------------*/
		BitSet BSuccs = mOperand.getSuccessors(currBSet, letter);
		/* ------------------------------------------------*/
		
		/* -------------- compute S' of S -----------------*/
		BitSet SSuccs = mOperand.getSuccessors(currSSet, letter);

		/* ------------------------------------------------*/
		
		/* -------------- compute C' of C -----------------*/
		// firstly compute successors of C\F which must be in C'
		BitSet CMinusFSuccs = mOperand.getSuccessors(cMinusF, letter);
		
		// secondly compute successors of C/\ F which may have final states
		BitSet cIntersectF = UtilBitSet.intersect(currCSet, F);             // get all accepting states in C
		BitSet CInterFSuccs = mOperand.getSuccessors(cIntersectF, letter);  // get successors of accepting states
		
		// now we get all successors of C
		BitSet CSuccs = new BitSet();
		CSuccs.or(CMinusFSuccs);                        // add successors of C\F
		CSuccs.or(CInterFSuccs);                        // add successors of C/\F
		
		// note that we should remove all final states which may go to S'
		CInterFSuccs.andNot(F);                            // remove accepting state here
		
		/* ------------------------------------------------*/

		/* -------------- compute N' of N -----------------*/
		BitSet NSuccs = mOperand.getSuccessors(currNSet, letter); // add successors of N
		BitSet tmp = (BitSet) NSuccs.clone();
		tmp.andNot(F);
		CSuccs.or(tmp); // add final successors in C
		
		NSuccs.andNot(F);            // remove final states
		NSuccs.andNot(CSuccs);       // remove successors of C, the final states of NSuccs are in CSuccs 
		NSuccs.andNot(SSuccs);       // remove successors of S
		/* ------------------------------------------------*/

		/* ----------- make nondeterministic choices ------------------- */
		// the successors of C /\ F should go to C and S with nondeterministic choices
		CInterFSuccs.andNot(CMinusFSuccs);         // remove must-in C states
//		System.out.println(CInterFSuccs);
		PowerSet ps = new PowerSet(CInterFSuccs); 
												
		while (ps.hasNext()) {
			BitSet Sextra = ps.next(); // extra states to be added into S'

			BitSet NPrime = NSuccs;
			BitSet CPrime = (BitSet) CSuccs.clone();
			CPrime.andNot(Sextra);
			BitSet SPrime = (BitSet) SSuccs.clone();
			SPrime.or(Sextra);
			
			BitSet BPrime = null;
			if(currBSet.isEmpty() ) {
				BPrime = (BitSet) CPrime.clone();
			}else {
				BPrime = (BitSet) BSuccs.clone();
				BPrime.andNot(Sextra);
			}

			if (hasNoOverlap(SPrime, F) && hasNoOverlap(CPrime, SPrime)) {
				StateNCSB succ = mComplement.addState(NPrime, CPrime, SPrime, BPrime);
				this.addSuccessor(letter, succ.getId());
				succs.add(succ);
			}
		}

		return super.getSuccessors(letter);
	}
	
	
	public boolean equals(Object otherState) {
		if(!(otherState instanceof StateNCSB)) {
			return false;
		}
		StateNCSB state = (StateNCSB)otherState;
		return  toString().equals(state.toString());
	}
	
	// check whether one state is covered by the other state (language-wise)
	public boolean coveredBy(StateNCSB other) {
		if(! UtilBitSet.subsetOf(other.mNSet, mNSet)) {
			return false;
		}
		
		if(! UtilBitSet.subsetOf(other.mCSet, mCSet)) {
			return false;
		}
		
		if(! UtilBitSet.subsetOf(other.mSSet, mSSet)) {
			return false;
		}

		return true;
	}
	
	
	public String toString() {
		return "(" + mNSet.toString() + "," + mCSet.toString() + ","
				+ mSSet.toString() + "," + mBSet.toString() + ")";
	}
	
	@Override
	public int hashCode() {
		return toString().hashCode();
	}


}
