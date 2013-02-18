package local.stalin.smt.theory.cclosure;

import local.stalin.smt.dpll.SimpleList;
import local.stalin.smt.dpll.SimpleListable;
import local.stalin.smt.theory.cclosure.CuckooHashSet;

public class CCTermPairHash extends CuckooHashSet<CCTermPairHash.Info> {
	
	static final class EqualityEntry extends SimpleListable<EqualityEntry> {
		EqualityAtom data;
		public EqualityEntry(EqualityAtom data) {
			this.data = data;
		}
		public EqualityAtom getData() {
			return data;
		}
		
		public String toString() {
			return data.toString();
		}
	}
	
	public final static class Info {
		CCTerm lhs, rhs;
		EqualityAtom diseq;
		SimpleList<EqualityEntry>  eqlits;

		class Entry extends SimpleListable<Entry> {
			Entry otherEntry;
			
			Info getInfo() {
				return Info.this;
			}

			public String toString() {
				return Info.this.toString();
			}
		}
		
		public Info(CCTerm l, CCTerm r) {
			lhs = l;
			rhs = r;
			Entry l1 = new Entry();
			Entry r1 = new Entry();
			l1.otherEntry = r1;
			r1.otherEntry = l1;
			l.pairInfos.append(l1);
			r.pairInfos.append(r1);
			eqlits = new SimpleList<EqualityEntry>();
		}
		
		public int hashCode() {
			return pairHash(lhs, rhs);
		}
		
		public final boolean equals(CCTerm lhs, CCTerm rhs) {
			return (this.lhs == lhs && this.rhs == rhs)
					|| (this.lhs == rhs && this.rhs == lhs);
		}
		
		public final boolean equals(Info info) {
			return equals(info.lhs, info.rhs);
		}
		
		public boolean equals(Object info) {
			return info instanceof Info && equals((Info) info);
		}

		public String toString() {
			return "Info["+lhs+","+rhs+"]";
		}
	}
	
	private Info getInfoStash(CCTerm lhs, CCTerm rhs) {
		StashList<Info> stash = this.stashList;
		while (stash != null) {
			if (stash.entry.equals(lhs,rhs))
				return stash.entry;
			stash = stash.next;
		}
		return null;
	}
	
	public Info getInfo(CCTerm lhs, CCTerm rhs) {
		int hash = pairHash(lhs, rhs);
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
		return hashSbox(lhs.hashCode()) ^ hashSbox(rhs.hashCode());
	}
}
