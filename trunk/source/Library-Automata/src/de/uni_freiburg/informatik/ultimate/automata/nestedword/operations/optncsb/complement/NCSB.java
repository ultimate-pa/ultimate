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
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.util.UtilIntSet;

/**
 * NCSB tuple 
 * TODO: in order to make it unmodifiable
 * */
public class NCSB {
	
	private IntSet mNSet;
	private IntSet mCSet;
	private IntSet mSSet;
	private IntSet mBSet;
	
	public NCSB(IntSet N, IntSet C, IntSet S, IntSet B) {
		this.mNSet = N;
		this.mCSet = C;
		this.mSSet = S;
		this.mBSet = B;
	}
	
	public NCSB() {
		this.mNSet = UtilIntSet.newIntSet();
		this.mCSet = UtilIntSet.newIntSet();
		this.mSSet = UtilIntSet.newIntSet();
		this.mBSet = UtilIntSet.newIntSet();
	}
	
	// be aware that we use the same object
	//CLONE object to make modification
	public IntSet getNSet() {
		return  mNSet;
	}
	
	public IntSet getCSet() {
		return  mCSet;
	}
	
	public IntSet getSSet() {
		return  mSSet;
	}
	
	public IntSet getBSet() {
		return  mBSet;
	}
	
	// Safe operations for (N, C, S, B)
	public IntSet copyNSet() {
		return  mNSet.clone();
	}
	
	public IntSet copyCSet() {
		return  mCSet.clone();
	}
	
	public IntSet copySSet() {
		return  mSSet.clone();
	}
	
	public IntSet copyBSet() {
		return  mBSet.clone();
	}
	
	@Override
	public boolean equals(Object obj) {
		if(this == obj) return true;
		if(!(obj instanceof NCSB)) {
			return false;
		}
		NCSB ncsb = (NCSB)obj;
		return  contentEqual(ncsb);
	}
	
	private boolean contentEqual(NCSB ncsb) {
		if(! mNSet.equals(ncsb.mNSet)
		|| ! mCSet.equals(ncsb.mCSet)
		|| ! mSSet.equals(ncsb.mSSet)
		|| ! mBSet.equals(ncsb.mBSet)) {
			return false;
		}
		return true;
	}
	

	public boolean coveredBy(NCSB other) {
		if(Options.lazyS && ! other.mBSet.subsetOf(mBSet)) {
			return false;
		}
		if(! other.mNSet.subsetOf(mNSet)
		|| ! other.mCSet.subsetOf(mCSet)
		|| ! other.mSSet.subsetOf(mSSet)) {
			return false;
		}

		return true;
	}
	
	// this.N >= other.N & this.C >= other.C & this.S >= other.S & this.B >= other.B
	public boolean strictlyCoveredBy(NCSB other) {
		if(! other.mNSet.subsetOf(mNSet)
		|| ! other.mCSet.subsetOf(mCSet)
		|| ! other.mSSet.subsetOf(mSSet)
		|| ! other.mBSet.subsetOf(mBSet)) {
			return false;
		}

		return true;
	}
	
	private IntSet mAllSets = null; 
	
	private void initializeAllSets() {
	    mAllSets = copyNSet();
	    mAllSets.or(mCSet);
	    mAllSets.or(mSSet);
	}
	
	public boolean subsetOf(NCSB other) {
	    if(mAllSets == null) {
	        initializeAllSets();
	    }
	    if(other.mAllSets == null) {
	        other.initializeAllSets();
	    }
        return mAllSets.subsetOf(other.mAllSets);
	}
	
	@Override
	public NCSB clone() {
		return new NCSB(mNSet.clone(), mCSet.clone(), mSSet.clone(), mBSet.clone());
	}
	
	@Override
	public String toString() {
		return "(" + mNSet.toString() + "," 
		           + mCSet.toString() + ","
		           + mSSet.toString() + ","
		           + mBSet.toString() + ")";
	}
	
    private int hashCode;
    private boolean hasCode = false;
	
	@Override
	public int hashCode() {
		if(hasCode) return hashCode;
		else {
			hasCode = true;
			hashCode = 1;
			final int prime = 31;
			hashCode= prime * hashCode + hashValue(mNSet);
			hashCode= prime * hashCode + hashValue(mCSet);
			hashCode= prime * hashCode + hashValue(mSSet);
			hashCode= prime * hashCode + hashValue(mBSet);
			return hashCode;
		}
	}
	
	private int hashValue(IntSet set) {
		final int prime = 31;
        int result = 1;
        for(final int n : set.iterable()) {
        	result = prime * result + n;
        }
        return result;
	}
	

}
