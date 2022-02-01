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
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.IntSet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.PowerSet;


/**
 * @author Yong Li
 * */
class SuccessorGenerator2 {
	
	private boolean mIsCurrBEmpty;
	private final NCSB mSuccNCSB;
	
	private IntSet mMinusFSuccs;
	private IntSet mInterFSuccs;
	
	private IntSet mF;       // so far all final states
	
	private IntSet mNPrime;  // d(N)\F\B'\S'
	private IntSet mVPrime;  // d(C) \/ (d(N) /\ F)
	private IntSet mSPrime;  // d(S)
	private IntSet mBPrime;  // d(B)
	
//	private IntSet mNInterFSuccs;
	
	private PowerSet mPs;
	
	private boolean hasSuccessors = true;
	
		
	public SuccessorGenerator2(boolean isCurrBEmpty, NCSB succ, IntSet minusFSuccs, IntSet interFSuccs, IntSet f) {
		this.mIsCurrBEmpty = isCurrBEmpty;
		this.mSuccNCSB = succ;
		
		this.mMinusFSuccs = minusFSuccs;
		this.mInterFSuccs = interFSuccs;
		this.mF = f;
		
		// initialization
		// N'
		mNPrime =  this.mSuccNCSB.copyNSet();
		mNPrime.andNot(mF);                    // remove final states
		mNPrime.andNot(mSuccNCSB.getCSet());   // remove successors of C, the final states of NSuccs are in CSuccs 
		mNPrime.andNot(mSuccNCSB.getSSet());   // remove successors of S
		
		// V' = d(C) \/ (d(N)/\F)
		mVPrime =  mSuccNCSB.copyCSet();
		IntSet nInterFSuccs =  mSuccNCSB.copyNSet();
		nInterFSuccs.and(mF);           // (d(N) /\ F)
		mVPrime.or(nInterFSuccs);       // d(C) \/ (d(N) /\ F)
		
		// S successors
		mSPrime =  mSuccNCSB.copySSet();
		
		// B successors
		mBPrime =  mSuccNCSB.copyBSet();
		
		if(Options.lazyS && mIsCurrBEmpty) {
			mInterFSuccs = mSuccNCSB.copyCSet(); // set to d(C)
		}
		
		// Original NCSB, distribute states in mInterFSuccs to S'
		mInterFSuccs.andNot(mMinusFSuccs);     // remove must-in C (B) states
//		mInterFSuccs.andNot(mSPrime);          // remove must in S states
		mInterFSuccs.andNot(mF);               // remove final states 

		mPs = new PowerSet(mInterFSuccs);
		
		// d(C\F) /\ d(S) or d(B/\F) should be empty
		hasSuccessors = !mMinusFSuccs.overlap(mSPrime);
	}
	
	public boolean hasNext() {
		return hasSuccessors && mPs.hasNext();
	}
	
	public NCSB next() {
		IntSet Sextra = mPs.next(); // extra states to be added into S'
		
		// this is implementation for NCSB 
		IntSet NP = mNPrime;
		IntSet CP =  null;
		IntSet SP =  mSPrime.clone();
		IntSet BP = null;
		
		if(Options.lazyS) {
			if(mIsCurrBEmpty) {
				// as usual S and C
				CP = mVPrime.clone();
				CP.andNot(Sextra); // C' get extra
				if(!Options.lazyB) {
					BP = CP;   // B' = C'
				}else {
					// following is d(C) /\ C'
					BP = mSuccNCSB.copyCSet(); 
					BP.andNot(Sextra);   // B'= d(C) /\ C'	
				}
				SP.or(Sextra); // S'=d(S)\/(V'\C')
			}else {
				// B is not empty
				SP.or(Sextra); // d(S) \/ M'
				BP = mBPrime.clone();
				BP.andNot(Sextra); // B'=d(B)\M'
				CP = mVPrime.clone();
				CP.andNot(SP); // C'= V'\S'
			}
			
			if(SP.overlap(mF) || BP.overlap(SP)) {
				return null;
			}

		}else {
			// original NCSB
			CP = mVPrime.clone();
			CP.andNot(Sextra);
			SP.or(Sextra);
			if(mIsCurrBEmpty) {
				BP =  CP;
			}else {
				BP =  mBPrime.clone();
				BP.andNot(Sextra);
			}
			
			if(SP.overlap(mF) || CP.overlap(SP)) {
				return null;
			}
		}

		return new NCSB(NP, CP, SP, BP);
	}
	
	
	

}
