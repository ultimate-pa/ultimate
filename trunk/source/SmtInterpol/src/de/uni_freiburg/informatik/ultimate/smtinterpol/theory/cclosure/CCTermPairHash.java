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
		CCEquality diseq;
		SimpleList<CCEquality.Entry>  eqlits;
		Entry lhsEntry, rhsEntry;
		int arrayextadded;

		class Entry extends SimpleListable<Entry> {
			CCTerm other;
			
			Entry (CCTerm other) {
				this.other = other;
			}
			
			Info getInfo() {
				return Info.this;
			}
			
			Entry getOtherEntry() {
				return Info.this.lhsEntry == this 
					? Info.this.rhsEntry : Info.this.lhsEntry; 
			}

			public String toString() {
				return Info.this.toString();
			}
		}
		
		public Info(CCTerm l, CCTerm r) {
			lhsEntry = new Entry(r);
			rhsEntry = new Entry(l);
			l.pairInfos.append(lhsEntry);
			r.pairInfos.append(rhsEntry);
			eqlits = new SimpleList<CCEquality.Entry>();
			arrayextadded = 0;
		}
		
		public int hashCode() {
			return pairHash(rhsEntry.other, lhsEntry.other);
		}
		
		public final boolean equals(CCTerm lhs, CCTerm rhs) {
			return (this.rhsEntry.other == lhs && this.lhsEntry.other == rhs)
					|| (this.rhsEntry.other == rhs && this.lhsEntry.other == lhs);
		}
		
		public String toString() {
			return "Info["+rhsEntry.other+","+lhsEntry.other+"]";
		}
		
//		public void addExtensionalityDiseq(ConvertFormula converter) {
//			if (arrayextadded == 0) {
//				arrayextadded = 1;
//				converter.addExtensionalityDiseqClause(
//						lhsEntry.other.flatTerm, rhsEntry.other.flatTerm);
//			}
//		}

		// TODO: Array and Quantifier support
		public boolean isEmpty() {
			return eqlits.isEmpty();
		}
	}
	
	private Info getInfoStash(CCTerm lhs, CCTerm rhs) {
		StashList<Info> stash = this.stashList;
		while (stash != null) {
			if (stash.getEntry().equals(lhs,rhs))
				return stash.getEntry();
			stash = stash.getNext();
		}
		return null;
	}
	
	public Info getInfo(CCTerm lhs, CCTerm rhs) {
		int hash = hash(pairHash(lhs, rhs));
		int hash1 = hash1(hash);
		Info bucket = (Info) buckets[hash1]; 
  		if (bucket != null && bucket.equals(lhs, rhs))
			return bucket;
		bucket = (Info) buckets[hash2(hash) ^ hash1]; 
  		if (bucket != null && bucket.equals(lhs, rhs))
			return bucket;
		return stashList != null ? getInfoStash(lhs, rhs) : null;
	}

	private static int pairHash(CCTerm lhs, CCTerm rhs) {
		return hashJenkins(lhs.hashCode()) + hashJenkins(rhs.hashCode());
	}

	public void removePairInfo(Info info) {
		// First remove this pair from the pairInfos-lists in the components
		info.lhsEntry.removeFromList();
		info.rhsEntry.removeFromList();
		remove(info);
	}
}
