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

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.SimpleList;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.SimpleListable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.CuckooHashSet;

public class CCTermPairHash extends CuckooHashSet<CCTermPairHash.Info> {

	public final static class Info {
		CCEquality mDiseq;
		/**
		 * The offset of this pair info: it relates the two endpoints {@code A = mRhsEntry.mOther} and
		 * {@code B = mLhsEntry.mOther} by {@code value(A) == value(B) + mOffset}. Several infos with the same endpoints
		 * but different offsets may coexist (e.g. for the equalities {@code a == b} and {@code a == b + 5}); they are
		 * distinguished by this offset both in the pair hash key and in the targeted lookups. For plain (offset-free)
		 * congruence closure this is always {@link Rational#ZERO}. Final, as it is part of the hash key.
		 */
		final Rational mOffset;
		final SimpleList<CCEquality.Entry>  mEqlits;
		final Entry mLhsEntry, mRhsEntry;
		final SimpleList<CompareTrigger> mCompareTriggers; // E-Matching

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

			/**
			 * The offset of the info as seen from the owner of this entry towards {@link #mOther}, i.e.
			 * {@code value(owner) - value(mOther)}. This is {@code +mOffset} for the lhs entry (owner {@code A}) and
			 * {@code -mOffset} for the rhs entry (owner {@code B}).
			 */
			Rational getOffsetToOther() {
				return mLhsEntry == this ? mOffset : mOffset.negate();
			}

			@Override
			public String toString() {
				return Info.this.toString();
			}
		}

		public Info(CCTerm l, CCTerm r) {
			this(l, r, Rational.ZERO);
		}

		public Info(CCTerm l, CCTerm r, Rational offset) {
			mLhsEntry = new Entry(r);
			mRhsEntry = new Entry(l);
			mOffset = offset;
			l.mPairInfos.append(mLhsEntry);
			r.mPairInfos.append(mRhsEntry);
			mEqlits = new SimpleList<CCEquality.Entry>();
			mCompareTriggers = new SimpleList<>();
		}

		@Override
		public int hashCode() {
			return pairHash(mRhsEntry.mOther, mLhsEntry.mOther)
					^ offsetHash(mRhsEntry.mOther, mLhsEntry.mOther, mOffset);
		}

		public final boolean equals(CCTerm lhs, CCTerm rhs, Rational offset) {
			// A = mRhsEntry.mOther, B = mLhsEntry.mOther, mOffset = value(A) - value(B).
			if (mRhsEntry.mOther == lhs && mLhsEntry.mOther == rhs) {
				return mOffset.equals(offset);
			}
			if (mRhsEntry.mOther == rhs && mLhsEntry.mOther == lhs) {
				return mOffset.equals(offset.negate());
			}
			return false;
		}

		@Override
		public String toString() {
			if (mOffset.equals(Rational.ZERO)) {
				return "Info[" + mLhsEntry.mOther + "," + mRhsEntry.mOther + "]";
			}
			return "Info[" + mRhsEntry.mOther + "," + mLhsEntry.mOther + "+" + mOffset + "]";
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

	private Info getInfoStash(CCTerm lhs, CCTerm rhs, Rational offset) {
		if (mStash != null && mStash.equals(lhs, rhs, offset)) {
			return mStash;
		}
		return null;
	}

	/**
	 * Look up the offset-zero pair info between the two terms. Equivalent to {@link #getInfo(CCTerm, CCTerm, Rational)}
	 * with a zero offset; used by all call sites that only deal with plain (offset-free) equalities.
	 */
	public Info getInfo(CCTerm lhs, CCTerm rhs) {
		return getInfo(lhs, rhs, Rational.ZERO);
	}

	/**
	 * Look up the pair info for the relationship {@code value(lhs) == value(rhs) + offset}. Infos with the same
	 * endpoints but different offsets are distinct entries, so the offset is part of the lookup key.
	 */
	public Info getInfo(CCTerm lhs, CCTerm rhs, Rational offset) {
		final int hash = hashJenkins(pairHash(lhs, rhs) ^ offsetHash(lhs, rhs, offset));
		final int hash1 = hash1(hash);
		Info bucket = (Info) mBuckets[hash1];
		if (bucket != null && bucket.equals(lhs, rhs, offset)) {
			return bucket;
		}
		bucket = (Info) mBuckets[hash2(hash) ^ hash1];
		if (bucket != null && bucket.equals(lhs, rhs, offset)) {
			return bucket;
		}
		return getInfoStash(lhs, rhs, offset);
	}

	private static int pairHash(CCTerm lhs, CCTerm rhs) {
		return hashJenkins(lhs.hashCode()) + hashJenkins(rhs.hashCode());
	}

	/**
	 * A hash contribution for the offset of an info between {@code a} and {@code b} with {@code offset == value(a) -
	 * value(b)}. The offset is expressed in a canonical endpoint orientation (the term with the smaller
	 * {@link CCTerm#hashCode()} first) before hashing, so that the relationship {@code (a, b, off)} and its mirror
	 * {@code (b, a, -off)} hash identically, while {@code (a, b, off)} and {@code (a, b, -off)} (i.e. {@code a = b + off}
	 * versus {@code a = b - off}) get different hashes — important because cuckoo hashing degrades badly on structured
	 * collisions. We use {@code hashCode()} rather than identity hashes to keep the solver deterministic.
	 *
	 * <p>If the two endpoints have equal hash codes (about a one in four billion chance) the orientation is ambiguous,
	 * so we fall back to the negation-invariant {@code offset.abs()} hash. That keeps the mirror consistent (at the
	 * cost of {@code off}/{@code -off} colliding only in that rare case).
	 */
	static int offsetHash(CCTerm a, CCTerm b, Rational offset) {
		final int ha = a.hashCode();
		final int hb = b.hashCode();
		if (ha == hb) {
			return offset.abs().hashCode();
		}
		final Rational canonical = ha < hb ? offset : offset.negate();
		return canonical.hashCode();
	}

	public void removePairInfo(Info info) {
		// First remove this pair from the pairInfos-lists in the components
		info.mLhsEntry.removeFromList();
		info.mRhsEntry.removeFromList();
		remove(info);
	}
}
