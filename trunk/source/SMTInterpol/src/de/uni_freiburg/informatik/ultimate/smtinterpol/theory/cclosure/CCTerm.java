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
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.SimpleList;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.SimpleListable;


/**
 * Objects of this class represent smtlib terms. This class contains the functionality for computing congruence closure
 * and deferring new equality/disequality atoms.
 *
 * The congruent terms are kept in a tree like structure: Every term except for the root of the tree points to a single
 * neighbour (equalEdge) to which it is congruent. The congruence is either due to an explicit equality atom between
 * these two neighbours or because the neighbours are function application with congruent parameters. If two nodes need
 * to be merged that are inside the tree, we make one of them the root of its tree by inverting the equalEdges. Then it
 * gets a new equalEdge to the other tree.
 *
 * There is another field rep pointing to the representative of the congruence class. It may be different to the root of
 * the equalEdge tree. The representative keeps track of the members of the class (members), the pair infos with the
 * equality atoms starting from this class and the disequality that separates it from another class (pairInfos), and the
 * signature back-refs of all terms in the class, i.e. the signatures in which a class member occurs as an argument
 * (signatureBackRefs).
 *
 * Each equalEdge corresponds to a merging event of two equivalence classes. We need to remember the representative of
 * the source equivalence class to allow undoing the merge operation. This is stored in the oldRep field of the object
 * that contains the equalEdge. If equalEdge is inverted, the oldRep field is moved accordingly. The old representative
 * also stores a reasonLiteral (which is null if the edge was introduced by congruence), and the list of merges that
 * were introduced after this merge by congruence closure (ccMerges).
 *
 * @author hoenicke
 */
public abstract class CCTerm extends SimpleListable<CCTerm> implements CCParameter {

	/**
	 * The destination of the outgoing equality edge. Every term has at most one
	 * equality edge, which was introduced by some merge operation. The edges may be
	 * inverted to allow introducing new equality edges. The equality edges always
	 * form a spanning tree for the members of the current equivalence class. They
	 * correspond either to congruences or equality literals.
	 */
	CCTerm mEqualEdge;
	/**
	 * The representative of the congruence class.  The representative
	 * is the one that contains the members, ccpar and eqlits information.
	 */
	CCTerm mRepStar;
	/**
	 * The offset of this term relative to its representative: the value of this term equals the value of
	 * {@link #mRepStar} plus this offset. This realises the affine (offset) equality classes: a member {@code t}
	 * satisfies {@code t == t.mRepStar + t.mOffsetToRep}. A representative has offset {@link Rational#ZERO} relative to
	 * itself. As long as no offset equality is ever created this is always {@link Rational#ZERO} and the structure
	 * degenerates to plain congruence closure.
	 */
	Rational mOffsetToRep = Rational.ZERO;
	/**
	 * Points to the next merged representative in the congruence class.
	 * This representative can have another representative of its own, if
	 * it is merged later with another class.
	 * This field equals this, iff the term is the representative of its class.
	 */
	CCTerm mRep;
	/**
	 * The representative of the source congruence class before the merge
	 * that introduced this.equalEdge.  Note that due to inverting the edge
	 * the old representative may be the representative of the destination
	 * of the equality edge.
	 */
	CCTerm mOldRep;
	/**
	 * oldRep.reasonLiteral contains the reason why equalEdge was introduced.
	 */
	CCEquality mReasonLiteral;
	/**
	 * the time stamp (or rather stack depth) when the merge of this node with
	 * its representative rep took place.
	 */
	int mMergeTime = Integer.MAX_VALUE;
	SimpleList<CCTerm> mMembers;
	int mNumMembers;
	SimpleList<CCTermPairHash.Info.Entry> mPairInfos;
	/**
	 * The list of signature backrefs for all terms in the congruence class.  The representative has all backrefs,
	 * the other terms point to the sublists that correspond to their children.
	 */
	SimpleList<SignatureBackRef> mSignatureBackRefs;
	/**
	 * A CCTerm in the current equivalence class that is shared with other theories, i.e. linear arithmetic. This is
	 * used to propagate equalities between shared terms when two equivalence classes are merged that both have a shared
	 * term. Only one shared term needs to be remembered as it is assumed that the other theories have some kind of
	 * transitive closure reasoning for equality.
	 */
	CCTerm mSharedTerm;
	/**
	 * The SMTLib representation of the term. This is the term for which this CCTerm was produced. It is null for
	 * partial function applications, which have no corresponding SMTLib representation.
	 */
	Term mFlatTerm;

	int mHashCode;

	final int mAge;

	static class TermPairMergeInfo {
		CCTermPairHash.Info.Entry mInfo;
		TermPairMergeInfo mNext;
		public TermPairMergeInfo(final CCTermPairHash.Info.Entry i, final TermPairMergeInfo n) {
			mInfo = i;
			mNext = n;
		}
	}
	static class CongruenceInfo {
		CCAppTerm mAppTerm1;
		CCAppTerm mAppTerm2;
		boolean mMerged;
		CongruenceInfo mNext;

		public CongruenceInfo(final CCAppTerm app1, final CCAppTerm app2, final CongruenceInfo next) {
			mAppTerm1 = app1;
			mAppTerm2 = app2;
			mNext = next;
		}
	}

	protected CCTerm(final int hash, final int age) {
		mRep = mRepStar = this;
		mMembers = new SimpleList<>();
		mPairInfos = new SimpleList<>();
		mSignatureBackRefs = new SimpleList<>();
		mMembers.append(this);
		mNumMembers = 1;
		assert invariant();
		mHashCode = hash;
		mAge = age;
	}

	boolean pairHashValid(final CClosure engine) {
		if (Config.EXPENSIVE_ASSERTS) {
			for (final CCTermPairHash.Info.Entry pentry : mPairInfos) {
				final CCTermPairHash.Info info = pentry.getInfo();
				assert pentry.getOtherEntry().mOther == this;
				if (this == mRep) {
					assert engine.mPairHash.getInfo(this, pentry.mOther) == info;
				}
			}
		}
		return true;
	}

	final boolean invariant() {
		if (Config.EXPENSIVE_ASSERTS) {
			boolean found = false;
			for (final CCTerm m : mRepStar.mMembers) {
				if (m == this) {
					found = true;
				}
			}
			assert found;
			assert mPairInfos.wellformed();
			if (this == mRepStar) {
				assert mMembers.wellformed();
			}
			for (final CCTermPairHash.Info.Entry pentry : mPairInfos) {
				assert pentry.getOtherEntry().mOther == this;
				final CCTerm other = pentry.mOther;
				assert other.mMergeTime >= mMergeTime;
				if (this == mRepStar || pentry.mOther == mRep) {
					assert pentry.getInfo().mEqlits.wellformed();
				} else {
					assert pentry.getInfo().mEqlits.wellformedPart();
				}
			}
			if (this == mRepStar) {
				assert mOffsetToRep.equals(Rational.ZERO) : "representative must have zero offset";
				for (final CCTerm m : mMembers) {
					assert m.mRepStar == this;
				}
			}
			assert (mEqualEdge == null) == (mOldRep == null);
			if (mEqualEdge != null) {
				assert mRepStar == mEqualEdge.mRepStar;
			}
		}
		return true;
	}

	@Override
	public final CCTerm getRepresentative() {
		return mRepStar;
	}

	/**
	 * @return the offset of this term relative to its representative, i.e. {@code value(this) == value(rep) + offset}.
	 */
	@Override
	public final Rational getOffsetToRep() {
		return mOffsetToRep;
	}

	/** A bare CCTerm is a {@link CCParameter} for its own value, with structural offset zero. */
	@Override
	public final CCTerm getCCTerm() {
		return this;
	}

	@Override
	public final Rational getOffset() {
		return Rational.ZERO;
	}

	public final boolean isRepresentative() {
		return mRep == this;
	}

	/**
	 * This is called when the flat term behind this ccterm is shared with another theory like linear arithmetic. We
	 * remember that this ccterm is shared and propagate this into all the representatives if there are already some.
	 * This may also propagate equalities if there is already a shared term in the congruence class.
	 *
	 * @param engine
	 */
	public void share(final CClosure engine) {
		assert mSharedTerm != this;
		engine.getLogger().debug("CC-Share %s", this);

		/*
		 * Find the old shared term, that would have been first merged with us, if this would have been shared earlier.
		 * Also determine, if we or oldShared would have gone to the representative. And in term we compute the common
		 * ancestor of oldShared and us.
		 */
		final CCTerm oldShared;
		final boolean weWin;
		CCTerm term = this;
		if (mSharedTerm != null) {
			oldShared = mSharedTerm;
			weWin = true;
		} else {
			/*
			 * The descendants of this didn't have a shared term so far. We search for the first shared term in the
			 * other part of the congruence class
			 */
			term.mSharedTerm = this;
			while (term.mRep.mSharedTerm == null) {
				term = term.mRep;
				/* so far, we are the only shared term in the congruence class */
				term.mSharedTerm = this;
			}
			if (term != term.mRep) {
				/* we found another shared term. Check which merge happened earlier */
				final CCTerm rep = term.mRep;
				assert rep.mSharedTerm != null;
				oldShared = rep.mSharedTerm;
				if (oldShared == rep) {
					weWin = false;
				} else {
					CCTerm otherTerm = oldShared;
					while (otherTerm.mRep != rep) {
						otherTerm = otherTerm.mRep;
					}
					assert otherTerm.mRep == rep && term.mRep == rep;
					assert otherTerm != term;
					/* the sharedTerm that was merged first, wins */
					weWin = term.mMergeTime < otherTerm.mMergeTime;
				}
				term = rep;
			} else {
				/* no other shared term found */
				oldShared = null;
				weWin = true;
			}
		}
		// propagate the equality with oldShared.
		if (oldShared != null) {
			/* update the remaining shared terms, if we win. */
			if (weWin) {
				/* we need to update exactly those, where oldShared was stored to */
				while (term.mSharedTerm == oldShared) {
					term.mSharedTerm = this;
					term = term.mRep;
				}
			}
			propagateSharedEquality(engine, oldShared);
		}
	}

	public void unshare() {
		assert mSharedTerm == this;
		assert isRepresentative();
		mSharedTerm = null;
	}

	/**
	 * Propagate a shared equality between this term and otherSharedTerm.
	 *
	 * @param engine
	 * @param otherSharedTerm
	 */
	private void propagateSharedEquality(final CClosure engine, final CCTerm otherSharedTerm) {
		assert mRepStar == otherSharedTerm.mRepStar;
		/* create equality formula.  This should never give TRUE or FALSE,
		 * as sterm is a newly shared term, which must be linear independent
		 * of all previously created terms.
		 */
		// value(this) - value(otherSharedTerm); both are in the same class, so the difference of their offsets.
		final Rational offset = mOffsetToRep.sub(otherSharedTerm.mOffsetToRep);
		final CCEquality cceq = engine.createEquality(this, otherSharedTerm, offset, true);
		assert cceq != null;
		if (engine.getLogger().isDebugEnabled()) {
			engine.getLogger().debug("PL: %s", cceq);
		}
		if (cceq.getDecideStatus() == null) {
			/* Creating the CCEquality should already propagate it, if it is true */
			assert engine.mPendingLits.contains(cceq);
		} else if (cceq.getLASharedData().getDecideStatus() == null) {
			assert cceq.getDecideStatus() == cceq;
			/*
			 * Creating an LAEquality doesn't automatically propagate it, though, if the CCEquality is already decided
			 */
			engine.addPending(cceq.getLASharedData());
			engine.mRecheckOnBacktrackLits.add(cceq);
		}
	}

	/**
	 * Clear the equal edge by inverting the edges.
	 */
	public void invertEqualEdges(final CClosure engine) {
		if (mEqualEdge == null) {
			return;
		}

		long time;
		if (Config.PROFILE_TIME) {
			time = System.nanoTime();
		}
		CCTerm last = null;
		CCTerm lastRep = null;
		CCTerm next = this;
		while (next != null) {
			final CCTerm t = next;
			next = next.mEqualEdge;
			t.mEqualEdge = last;
			final CCTerm nextRep = t.mOldRep;
			t.mOldRep = lastRep;
			last = t;
			lastRep = nextRep;
		}
		if (Config.PROFILE_TIME) {
			engine.addInvertEdgeTime(System.nanoTime() - time);
		}
	}

	/**
	 * Compute the value difference {@code value(from) - value(to)} implied by a merge reason. For an offset equality the
	 * reason states {@code reason.getLhs() == reason.getRhs() + reason.getOffset()}; {@code from} and {@code to} are the
	 * two terms being merged and must be exactly the two sides of the reason (in either order). A {@code null} reason is
	 * a congruence merge, where the two function applications have equal value, hence a difference of zero.
	 */
	private static Rational reasonDiff(final CCEquality reason, final CCTerm from, final CCTerm to) {
		if (reason == null) {
			return Rational.ZERO;
		}
		if (from == reason.getLhs() && to == reason.getRhs()) {
			return reason.getOffset();
		}
		if (from == reason.getRhs() && to == reason.getLhs()) {
			return reason.getOffset().negate();
		}
		throw new AssertionError("merge reason does not match the merged terms");
	}

	public Clause merge(final CClosure engine, final CCTerm lhs, final CCEquality reason) {
		assert reason != null
				|| (this instanceof CCAppTerm && lhs instanceof CCAppTerm);

		/* Check the representatives of this */
		final CCTerm src = lhs.mRepStar;
		final CCTerm dest = mRepStar;
		assert src.invariant();
		assert src.pairHashValid(engine);
		assert dest.invariant();
		assert dest.pairHashValid(engine);
		if (src == dest) {
			/*
			 * Terms are already merged. With offset equalities this is only consistent if the offset implied by the
			 * reason matches the offset that the two terms already have within their common class. A mismatch (e.g.
			 * asserting x = x + 1) is a conflict.
			 */
			final Rational existingDiff = lhs.mOffsetToRep.sub(mOffsetToRep);
			if (!existingDiff.equals(reasonDiff(reason, lhs, this))) {
				// The two terms are congruent (reason == null ⇒ implied value difference 0) but already in the same
				// class at a non-zero offset existingDiff (e.g. f(x) and f(y) forced equal while the class already has
				// f(x) = f(y) + k). This is an offset conflict: build the anti-cycle from the argument equalities (which
				// justify the congruence) plus the existing path (which establishes the conflicting offset).
				assert reason == null : "non-congruence merge of terms already in the same class";
				return engine.computeCongruenceAntiCycle((CCAppTerm) this, (CCAppTerm) lhs);
			}
			return null;
		}

		engine.incMergeCount();
		Clause res;
		if (src.mNumMembers > dest.mNumMembers) {
			res = lhs.mergeInternal(engine, this, reason);
		} else {
			res = mergeInternal(engine, lhs, reason);
		}
		assert invariant();
		assert lhs.invariant();
		assert mRepStar.pairHashValid(engine);
		return res;
	}

	private Clause mergeInternal(final CClosure engine, final CCTerm lhs, final CCEquality reason) {
		/* Check the representatives of this */
		final CCTerm src = lhs.mRepStar;
		final CCTerm dest = mRepStar;

		/*
		 * The offset that src (the old representative of the merged class) gets relative to dest: value(src) ==
		 * value(dest) + delta. It is derived from the reason and the offsets the two merged terms already have relative
		 * to their respective representatives.
		 */
		final Rational delta = reasonDiff(reason, lhs, this).sub(lhs.mOffsetToRep).add(mOffsetToRep);

		// Detect a conflict (a disequality forbidding the merge, or a shared-term clash) before mutating anything and
		// return it immediately. The conflict explainers build each half within its own class and never walk the merge
		// bridge, so they do not need the equal edge — returning here (rather than merging, then undoing the edge on a
		// conflict) keeps the union-find and MBTC from ever seeing the half-merged conflicting state. A disequality
		// conflicts only if it forbids exactly the offset delta at which the two classes are being merged.
		final CCTermPairHash.Info diseqInfo = engine.mPairHash.getInfo(src, dest, delta);
		if (diseqInfo != null && diseqInfo.mDiseq != null) {
			final CCEquality diseq = diseqInfo.mDiseq;
			// A disequality forbids this merge. Its two sides straddle the freshly added (not-yet-united) bridge, so
			// orient them into the source/destination class and build the two halves separately (computeCycle would
			// walk a single path across the bridge and mix offset frames). mRepStar is still the pre-merge rep here.
			final CCTerm srcEnd = diseq.getLhs().mRepStar == src ? diseq.getLhs() : diseq.getRhs();
			final CCTerm destEnd = diseq.getLhs().mRepStar == src ? diseq.getRhs() : diseq.getLhs();
			return engine.computeMergeDiseqCycle(srcEnd, destEnd, lhs, this, reason,
					reasonDiff(reason, lhs, this), diseq);
		}
		if (src.mSharedTerm != null) {
			if (dest.mSharedTerm == null) {
				dest.mSharedTerm = src.mSharedTerm;
			} else {
				final boolean createInLA = dest.mSharedTerm.mFlatTerm.getSort().isNumericSort();
				// value(src.mSharedTerm) - value(dest.mSharedTerm) after the merge: the merge offset delta plus the two
				// shared terms' offsets to their (current) representatives.
				final Rational sharedOffset =
						delta.add(src.mSharedTerm.mOffsetToRep).sub(dest.mSharedTerm.mOffsetToRep);
				final CCEquality cceq =
						engine.createEquality(src.mSharedTerm, dest.mSharedTerm, sharedOffset, createInLA);
				/* If cceq cannot be created this is a conflict like merging x+1 and x */
				if (cceq == null) {
					return engine.computeSharedConflictCycle(src.mSharedTerm, dest.mSharedTerm, lhs, this, reason,
							reasonDiff(reason, lhs, this));
				}
				/*
				 * No need to remember the created equality. It was inserted and will be found later and propagated
				 * automatically.
				 */
			}
		}

		/* Invert equivalence edges */
		lhs.invertEqualEdges(engine);
		/* Now create a new equaledge to dest. */
		lhs.mEqualEdge = this;
		lhs.mOldRep = src;
		src.mReasonLiteral = reason;

		long time;

		src.mMergeTime = engine.getMergeDepth();
		engine.recordMerge(lhs);
		engine.getLogger().debug("M %s %s (offset %s)", this, lhs, reasonDiff(reason, this, lhs));

		if (Config.PROFILE_TIME) {
			time = System.nanoTime();
		}
		/*
		 * Rehash the signatures with delta (computed above): the effective offset of every src-class argument increases
		 * by delta. Since src is a representative its own offset was ZERO, so after the shift below src.mOffsetToRep ==
		 * delta. Rehashing happens before the offsets are actually updated below.
		 */
		engine.rehashSignatures(src, dest, delta, src.mSignatureBackRefs);
		/* Update rep fields and shift offsets of the merged members into dest's frame */
		src.mRep = dest;
		for (final CCTerm t : src.mMembers) {
			t.mRepStar = dest;
			t.mOffsetToRep = t.mOffsetToRep.add(delta);
		}
		if (Config.PROFILE_TIME) {
			engine.addSetRepTime(System.nanoTime() - time);
		}
		dest.mMembers.joinList(src.mMembers);
		dest.mNumMembers += src.mNumMembers;

		if (Config.PROFILE_TIME) {
			time = System.nanoTime();
		}
		for (final CCTermPairHash.Info.Entry pentry : src.mPairInfos) {
			final CCTermPairHash.Info info = pentry.getInfo();
			assert pentry.getOtherEntry().mOther == src;
			final CCTerm other = pentry.mOther;
			assert other.mRepStar == other;
			// offset of this info as seen from src: value(src) - value(other)
			final Rational offFromSrc = pentry.getOffsetToOther();
			if (other == dest) {
				if (offFromSrc.equals(delta)) {
					// The equalities in this info hold at exactly the merge offset, so they are now implied true.
					assert (info.mDiseq == null);
					for (final CCEquality.Entry eq : info.mEqlits) {
						engine.addPending(eq.getCCEquality());
					}
					// E-Matching
					for (final CompareTrigger trigger : info.mCompareTriggers) {
						trigger.activate();
					}
				} else {
					// These equalities claim an offset different from the merge offset, so they are now implied
					// false. We propagate the disequality eagerly here with the merge as its reason; the explanation
					// (CClosure.computeAntiCycle, same-class branch) reconstructs it from the path between the two
					// terms, so no separating disequality atom is involved and mDiseqReason stays null. An equality
					// here cannot already be true, as that would mean src and dest are already in the same class.
					for (final CCEquality.Entry eq : info.mEqlits) {
						final CCEquality cceq = eq.getCCEquality();
						assert cceq.getDecideStatus() != cceq;
						if (cceq.getDecideStatus() == null) {
							// this is caused by an offset conflict, not by a set disequality
							cceq.mDiseqReason = null;
							engine.addPending(cceq.negate());
						}
					}
				}
			} else {
				// Re-key the info from src to dest: value(dest) - value(other) = (value(src) - value(other)) - delta.
				final Rational destOffset = offFromSrc.sub(delta);
				CCTermPairHash.Info destInfo = engine.mPairHash.getInfo(dest, other, destOffset);
				if (destInfo == null) {
					destInfo = new CCTermPairHash.Info(dest, other, destOffset);
					engine.mPairHash.add(destInfo);
				}
				//System.err.println("M "+src+" "+other+" "+dest);
				/* Merge Infos */
				if (destInfo.mDiseq == null && info.mDiseq != null) {
					destInfo.mDiseq = info.mDiseq;
					for (final CCEquality.Entry eq : destInfo.mEqlits) {
						assert eq.getCCEquality().getDecideStatus() != eq.getCCEquality();
						if (eq.getCCEquality().getDecideStatus() == null) {
							eq.getCCEquality().setDiseqReason(info.mDiseq);
							engine.addPending(eq.getCCEquality().negate());
						}
					}
				} else if (destInfo.mDiseq != null && info.mDiseq == null) {
					for (final CCEquality.Entry eq : info.mEqlits) {
						assert eq.getCCEquality().getDecideStatus() != eq.getCCEquality();
						if (eq.getCCEquality().getDecideStatus() == null) {
							eq.getCCEquality().setDiseqReason(destInfo.mDiseq);
							engine.addPending(eq.getCCEquality().negate());
						}
					}
				}
				destInfo.mEqlits.joinList(info.mEqlits);
				destInfo.mCompareTriggers.joinList(info.mCompareTriggers);
			}
			pentry.getOtherEntry().unlink();
			assert other.mPairInfos.wellformed();
			engine.removePairHash(info);
		}
		if (Config.PROFILE_TIME) {
			engine.addEqTime(System.nanoTime() - time);
		}

		if (Config.PROFILE_TIME) {
			time = System.nanoTime();
		}
		/* Compute congruence closure */
		engine.getLogger().debug("Merge Backrefs: %s", src.mSignatureBackRefs);
		dest.mSignatureBackRefs.joinList(src.mSignatureBackRefs);

		if (Config.PROFILE_TIME) {
			engine.addCcTime(System.nanoTime() - time);
		}

		assert invariant();
		assert lhs.invariant();
		assert src.invariant();
		assert dest.invariant();

		return null;
	}

	public void undoMerge(final CClosure engine, final CCTerm lhs) {
		engine.getLogger().debug("U %s %s (offset %s)", lhs, this, mOldRep == null ? null : mOldRep.mOffsetToRep);
		long time;
		CCTerm src, dest;

		assert invariant();
		assert lhs.invariant();
		assert mRepStar.pairHashValid(engine);
		assert mEqualEdge == lhs;
		assert mRepStar == lhs.mRepStar;

		src = mOldRep;
		mEqualEdge = null;
		mOldRep = null;
		dest = mRepStar;
		assert src.mRep == dest;

		/*
		 * The delta that was added to every src-class member at merge time is src's current offset relative to dest
		 * (src was a representative with offset ZERO before the merge). Undoing reverses both the representative change
		 * (dest -> src) and the offset shift (by -delta). Rehash before the offsets below are restored.
		 */
		final Rational delta = src.mOffsetToRep;
		dest.mSignatureBackRefs.unjoinList(src.mSignatureBackRefs);
		engine.getLogger().debug("Unmerge Backrefs: %s", src.mSignatureBackRefs);
		engine.rehashSignatures(dest, src, delta.negate(), src.mSignatureBackRefs);

		src.mReasonLiteral = null;
		for (final CCTermPairHash.Info.Entry pentry : src.mPairInfos.reverse()) {
			final CCTermPairHash.Info info = pentry.getInfo();
			assert pentry.getOtherEntry().mOther == src;
			engine.mPairHash.add(pentry.getInfo());
			assert pentry.mOther.mPairInfos.wellformed();
			pentry.mOther.mPairInfos.append(pentry.getOtherEntry());
			assert pentry.mOther.mPairInfos.wellformed();
			final CCTerm other = pentry.mOther;
			assert other.mRepStar == other;
			if (other != dest) {
				// Mirror the merge re-keying: the merged info lived at value(dest) - value(other) = offFromSrc - delta.
				final Rational destOffset = pentry.getOffsetToOther().sub(delta);
				final CCTermPairHash.Info destInfo = engine.mPairHash.getInfo(dest, other, destOffset);
				if (destInfo == null) {
					continue;
				}
				destInfo.mCompareTriggers.unjoinList(info.mCompareTriggers);
				assert destInfo.mEqlits.wellformed();
				destInfo.mEqlits.unjoinList(info.mEqlits);
				assert info.mEqlits.wellformed() && destInfo.mEqlits.wellformed();
				if (destInfo.mDiseq == info.mDiseq) {
					destInfo.mDiseq = null;
				}
				/* Check if we can remove destInfo since it is empty now */
				if (destInfo.mDiseq == null && destInfo.mEqlits.isEmpty() && destInfo.mCompareTriggers.isEmpty()) {
					destInfo.mLhsEntry.unlink();
					destInfo.mRhsEntry.unlink();
					engine.removePairHash(destInfo);
				}
			}
		}

		dest.mNumMembers -= src.mNumMembers;
		if (Config.PROFILE_TIME) {
			time = System.nanoTime();
		}
		/*
		 * Undo the offset shift applied at merge (delta computed above). Subtracting it restores each member's offset
		 * relative to src and resets src.mOffsetToRep to ZERO.
		 */
		dest.mMembers.unjoinList(src.mMembers);
		for (final CCTerm t : src.mMembers) {
			t.mRepStar = src;
			t.mOffsetToRep = t.mOffsetToRep.sub(delta);
		}
		src.mRep = src;

		assert src.mMergeTime == engine.getMergeDepth();
		src.mMergeTime = Integer.MAX_VALUE;
		if (Config.PROFILE_TIME) {
			engine.addSetRepTime(System.nanoTime() - time);
		}

		if (dest.mSharedTerm == src.mSharedTerm) {
			dest.mSharedTerm = null;
		}

		assert invariant();
		assert lhs.invariant();
		assert src.invariant();
		assert dest.invariant();
		assert src.pairHashValid(engine);
		assert dest.pairHashValid(engine);
	}

	public CCTerm getSharedTerm() {
		return mSharedTerm;
	}

	@Override
	public int hashCode() {
		return mHashCode;
	}

	@Override
	public Term getFlatTerm() {
		return mFlatTerm;
	}

	public int getNumMembers() {
		return mNumMembers;
	}

	public int getAge() {
		return mAge;
	}
}
