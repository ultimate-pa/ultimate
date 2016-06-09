/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure;

import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.SimpleList;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.SimpleListable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.CuckooHashSet;

public class CCTermPairHash extends CuckooHashSet<CCTermPairHash.Info> {
	
	public final static class Info {
		CCEquality mDiseq;
		final SimpleList<CCEquality.Entry>  mEqlits;
		final Entry mLhsEntry, mRhsEntry;

		class Entry extends SimpleListable<Entry> {
			CCTerm mOther;
			
			Entry(CCTerm other) {
				mOther = other;
			}
			
			Info getInfo() {
				return Info.this;
			}
			
			Entry getOtherEntry() {
				return mLhsEntry == this 
					? mRhsEntry : mLhsEntry; 
			}

			@Override
			public String toString() {
				return Info.this.toString();
			}
		}
		
		public Info(CCTerm l, CCTerm r) {
			mLhsEntry = new Entry(r);
			mRhsEntry = new Entry(l);
			l.mPairInfos.append(mLhsEntry);
			r.mPairInfos.append(mRhsEntry);
			mEqlits = new SimpleList<CCEquality.Entry>();
		}
		
		@Override
		public int hashCode() {
			return pairHash(mRhsEntry.mOther, mLhsEntry.mOther);
		}
		
		public final boolean equals(CCTerm lhs, CCTerm rhs) {
			return (mRhsEntry.mOther == lhs && mLhsEntry.mOther == rhs)
					|| (mRhsEntry.mOther == rhs && mLhsEntry.mOther == lhs);
		}
		
		@Override
		public String toString() {
			return "Info[" + mRhsEntry.mOther + "," + mLhsEntry.mOther + "]";
		}
		
//		public void addExtensionalityDiseq(ConvertFormula converter) {
//			if (arrayextadded == 0) {
//				arrayextadded = 1;
//				converter.addExtensionalityDiseqClause(
//						lhsEntry.other.flatTerm, rhsEntry.other.flatTerm);
//			}
//		}

		public boolean isEmpty() {
			return mEqlits.isEmpty();
		}
	}
	
	private Info getInfoStash(CCTerm lhs, CCTerm rhs) {
		StashList<Info> stash = mStashList;
		while (stash != null) {
			if (stash.getEntry().equals(lhs,rhs)) {
				return stash.getEntry();
			}
			stash = stash.getNext();
		}
		return null;
	}
	
	public Info getInfo(CCTerm lhs, CCTerm rhs) {
		final int hash = hash(pairHash(lhs, rhs));
		final int hash1 = hash1(hash);
		Info bucket = (Info) mBuckets[hash1]; 
  		if (bucket != null && bucket.equals(lhs, rhs)) {
			return bucket;
		}
		bucket = (Info) mBuckets[hash2(hash) ^ hash1]; 
  		if (bucket != null && bucket.equals(lhs, rhs)) {
			return bucket;
		}
		return mStashList == null ? null : getInfoStash(lhs, rhs);
	}

	private static int pairHash(CCTerm lhs, CCTerm rhs) {
		return hashJenkins(lhs.hashCode()) + hashJenkins(rhs.hashCode());
	}

	public void removePairInfo(Info info) {
		// First remove this pair from the pairInfos-lists in the components
		info.mLhsEntry.removeFromList();
		info.mRhsEntry.removeFromList();
		remove(info);
	}
}
