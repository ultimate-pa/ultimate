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

public class SuccessorGenerator {
	
	private boolean mIsCurrBEmpty;
	private final NCSB mSuccNCSB;
	
	private IntSet mMinusFSuccs;
	private IntSet mInterFSuccs;
	
	private IntSet mF;       // so far all final states
	
	private IntSet mNPrime;  // d(N)\F\B'\S'
	private IntSet mVPrime;  // d(C) \/ (d(N) /\ F)
	private IntSet mMustIn;  // must in states in C or B
	private IntSet mSPrime;  // d(S)
	private IntSet mBPrime;  // d(B)
	
	private PowerSet mPs;	
		
	public SuccessorGenerator(boolean isBEmpty, NCSB succ, IntSet minusFSuccs, IntSet interFSuccs, IntSet f) {
		this.mIsCurrBEmpty = isBEmpty;
		this.mSuccNCSB = succ;
				
		this.mMinusFSuccs = minusFSuccs;
		this.mInterFSuccs = interFSuccs;
		this.mF = f;
		
		// initialization
		initialize();
	}
	
	private void initialize() {
		
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
		mSPrime =  mSuccNCSB.getSSet();
		
		// B successors
		mBPrime =  mSuccNCSB.getBSet();
		
		// compute must in (C/B) states
		// in order not to mess up the code with the description 
		// some lines may repeat in different situation
		if(Options.lazyS) {
			// lazy NCSB initialization
			if(mIsCurrBEmpty) {
				mInterFSuccs = mSuccNCSB.copyCSet(); // set to d(C)
				// must in states computation
				mMustIn = mSuccNCSB.copyCSet();
				mMustIn.and(mF);                  // d(C) /\ F
				mMustIn.or(nInterFSuccs);         // C_under = d(C\/N) /\F
			}else {
				mMustIn = mInterFSuccs.clone(); // d(B/\F)
				mMustIn.and(mF);                // d(B/\F) /\F
				mMustIn.or(mMinusFSuccs);       // B_under = d(B\F) \/ (d(B/\F) /\F)
			}
		}else {
			// original NCSB
			mMustIn = mInterFSuccs.clone(); // d(C/\F)
			mMustIn.and(mF);                // d(C/\F) /\F
			mMustIn.or(mMinusFSuccs);       // d(C\F) \/ (d(C/\F) /\F)
			mMustIn.or(nInterFSuccs);       // C_under = d(C\F) \/ (d(C/\F) /\F) \/ (d(N)\/ F)
		}
		
		// compute nondeterministic states from mInterFSuccs
		mInterFSuccs.andNot(mMinusFSuccs);     // remove must-in C (B) states
		mInterFSuccs.andNot(mSPrime);          // remove must in S states
		mInterFSuccs.andNot(mF);               // remove final states 

		mPs = new PowerSet(mInterFSuccs);
		
	}
	
	public boolean hasNext() {
		return mPs.hasNext();
	}
	
	public NCSB next() {
		IntSet toS = mPs.next(); // extra states to be added into S'
		IntSet left = mInterFSuccs.clone();
		left.andNot(toS);
		// this is implementation for NCSB 
		IntSet NP = mNPrime;
		IntSet CP =  null;
		IntSet SP =  mSPrime.clone();
		IntSet BP = null;
		
		if(Options.lazyS) {
			SP.or(toS); // S'=d(S)\/M'
			if(mIsCurrBEmpty) {
				// as usual S and C
				CP = mMustIn.clone();
				CP.or(left); // C' get extra
				if(!Options.lazyB) {
					BP = CP;
				}else {
					// following is d(C) /\ C'
					BP = mSuccNCSB.copyCSet(); 
					BP.and(CP);   // B'= d(C) /\ C'
				}
			}else {
				// B is not empty
				BP = mMustIn.clone();
				BP.or(left); // B'=d(B)\M'
				CP = mVPrime.clone();
				CP.andNot(SP); // C'= V'\S'
			}
			
			assert !SP.overlap(mF) && !BP.overlap(SP) : "S:" + SP.toString() + " B:" + BP.toString();

		}else {
			// original NCSB
			CP = mMustIn.clone();
			CP.or(left);
			SP.or(toS);
			if(mIsCurrBEmpty) {
				if(!Options.lazyB) {
					BP = CP;
				}else {
					BP = mSuccNCSB.copyCSet();
					BP.and(CP);
				}
			}else {
				BP =  mBPrime.clone();
				BP.and(CP);
			}
			
			assert !SP.overlap(mF) && !CP.overlap(SP) : "S:" + SP.toString() + " C:" + CP.toString();
		}

		return new NCSB(NP, CP, SP, BP);
	}
	
	
	

}
