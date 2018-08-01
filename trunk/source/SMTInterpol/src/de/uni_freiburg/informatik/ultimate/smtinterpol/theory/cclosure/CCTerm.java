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

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.EqualityProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SharedTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.SimpleList;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.SimpleListable;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;


/**
 * Objects of this class represent smtlib terms.  This class contains
 * the functionality for computing congruence closure and deferring new
 * equality/disequality atoms.
 * 
 * The congruent terms are kept in a tree like structure:  Every term 
 * except for the root of the tree points to a single neighbour (equalEdge)
 * to which it is congruent.  The congruence is either due to an explicit 
 * equality atom between these two neighbours or because the neighbours 
 * are function application with congruent parameters.  If two nodes need
 * to be merged that are inside the tree, we make one of them the root
 * of its tree by inverting the equalEdges.  Then it gets a new equalEdge to
 * the other tree.
 * 
 * There is another field rep pointing to the representative of the congruence
 * class.  It may be different to the root of the equalEdge tree.  The 
 * representative keeps track of the members of the class (member), the
 * equality atoms starting from this class (eqlits), the classes that are 
 * guaranteed to be disjoint (diseq), and the function application terms whose
 * parameter is in this class (ccpar1/ccpar2).
 * 
 * Each equalEdge corresponds to merging to equivalence classes.  We need to
 * remember the representative of the source equivalence class to allow undoing
 * the merge operation.  This is stored in the oldRep field of the object 
 * that contains the equalEdge.  If equalEdge is inverted, the oldRep field
 * is moved accordingly.  The old representative also stores a
 * reasonLiteral (which is null if the edge was introduced by congruence), 
 * and the list of merges that were introduced after this merge by 
 * congruence closure (ccMerges).
 * 
 * @author hoenicke
 */
public abstract class CCTerm extends SimpleListable<CCTerm> {
	
	/**
	 * The destination of the outgoing equality edge.  Every term has at
	 * most one equality edge, which was introduced by some merge operation.
	 * The edges may be inverted to allow introducing new equality edges.
	 */
	CCTerm mEqualEdge;
	/**
	 * The representative of the congruence class.  The representative 
	 * is the one that contains the members, ccpar and eqlits information.
	 */
	CCTerm mRepStar;
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
	CCParentInfo mCCPars;
	SimpleList<CCTerm> mMembers;
	int mNumMembers;
	SimpleList<CCTermPairHash.Info.Entry> mPairInfos;
	SharedTerm mSharedTerm;
	SharedTerm mFlatTerm;
	
	int mHashCode;
	
	int mModelVal;
	
	static class TermPairMergeInfo {
		CCTermPairHash.Info.Entry mInfo;
		TermPairMergeInfo mNext;
		public TermPairMergeInfo(CCTermPairHash.Info.Entry i, TermPairMergeInfo n) {
			mInfo = i;
			mNext = n;
		}
	}
	static class CongruenceInfo {
		CCAppTerm mAppTerm1;
		CCAppTerm mAppTerm2;
		boolean mMerged;
		CongruenceInfo mNext;

		public CongruenceInfo(CCAppTerm app1, CCAppTerm app2, CongruenceInfo next) {
			mAppTerm1 = app1;
			mAppTerm2 = app2;
			mNext = next;
		}
	}
	
	boolean mIsFunc;
	int mParentPosition;

	protected CCTerm(boolean isFunc, int parentPos, SharedTerm term, int hash) {
		mIsFunc = isFunc;
		mCCPars = null;
		if (isFunc) {
			mParentPosition = parentPos;
		}
		mCCPars = new CCParentInfo();
		mRep = mRepStar = this;
		mMembers = new SimpleList<CCTerm>();
		mPairInfos = new SimpleList<CCTermPairHash.Info.Entry>();
		mMembers.append(this);
		mNumMembers = 1;
		assert invariant();
		mFlatTerm = term;
		mHashCode = hash;
	}
	
	boolean pairHashValid(CClosure engine) {
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
    			assert(mCCPars != null);
    			for (CCParentInfo parInfo = mCCPars.mNext; 
    			     parInfo != null; parInfo = parInfo.mNext) {
    				assert parInfo.mCCParents.wellformed();
    				assert parInfo.mNext == null 
    						|| parInfo.mFuncSymbNr < parInfo.mNext.mFuncSymbNr;
    			}
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

	public final CCTerm getRepresentative() {
		return mRepStar;
	}

	public final boolean isRepresentative() {
		return mRep == this;
	}

	public void share(CClosure engine, SharedTerm sterm) {
		if (mSharedTerm != null) {
			if (mSharedTerm == sterm) {
				return;
			}
			propagateSharedEquality(engine, sterm);
		}
		CCTerm term = this;
		final SharedTerm oldTerm = mSharedTerm;
		mSharedTerm = sterm;
		while (term.mRep != term) {
			term = term.mRep;
			if (term.mSharedTerm == oldTerm) {
				term.mSharedTerm = sterm;
			} else {
				term.propagateSharedEquality(engine, sterm);
				break;
			}
		}
	}
	
	public void unshare(SharedTerm sterm) {
		assert mSharedTerm == sterm;
		assert isRepresentative();
		mSharedTerm = null;
	}
	
	private void propagateSharedEquality(CClosure engine, SharedTerm sterm) {
		/* create equality formula.  This should never give TRUE or FALSE,
		 * as sterm is a newly shared term, which must be linear independent
		 * of all previously created terms. 
		 */
		final EqualityProxy eqForm = mSharedTerm.createEquality(sterm);
		assert (eqForm != EqualityProxy.getTrueProxy());
		assert (eqForm != EqualityProxy.getFalseProxy());
		final CCEquality cceq = eqForm.createCCEquality(mSharedTerm, sterm);
		if (engine.mEngine.getLogger().isDebugEnabled()) {
			engine.mEngine.getLogger().debug("PL: " + cceq);
		}
		engine.addPending(cceq);
	}

	/**
	 * Clear the equal edge by inverting the edges.
	 */
	public void invertEqualEdges(CClosure engine) {
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
	
	public Clause merge(CClosure engine, CCTerm lhs, CCEquality reason) {
		assert reason != null 
				|| (this instanceof CCAppTerm && lhs instanceof CCAppTerm);
		assert engine.mMergeDepth == engine.mMerges.size();

		/* Check the representatives of this */
		final CCTerm src = lhs.mRepStar;
		final CCTerm dest = mRepStar;
		assert src.invariant();
		assert src.pairHashValid(engine);
		assert dest.invariant();
		assert dest.pairHashValid(engine);
		if (src == dest) {
			/* Terms are already merged. */
			return null;
		}

		//Logger.getRootLogger().debug("M"+lhs+"=="+this);
		engine.incMergeCount();
		Clause res;
		if (src.mNumMembers > dest.mNumMembers) {
			res = lhs.mergeInternal(engine, this, reason);
			if (res == null && reason == null) {
				((CCAppTerm)this).markParentInfos();
			}
		} else {
			res = mergeInternal(engine, lhs, reason);
			if (res == null && reason == null) {
				((CCAppTerm)lhs).markParentInfos();
			}
		}
		assert engine.mMergeDepth == engine.mMerges.size();
		assert invariant();
		assert lhs.invariant();
		assert mRepStar.pairHashValid(engine);
		return res;
	}
	
	private Clause mergeInternal(CClosure engine, CCTerm lhs, CCEquality reason) {
		/* Check the representatives of this */
		final CCTerm src = lhs.mRepStar;
		final CCTerm dest = mRepStar;
		
		// Need to prevent MBTC when we get a conflict. Hence a two-way pass
		CCEquality diseq = null;
		final CCTermPairHash.Info diseqInfo = engine.mPairHash.getInfo(src, dest);
		if (diseqInfo != null) {
			diseq = diseqInfo.mDiseq;
		}
		boolean sharedTermConflict = false;
		if (diseq == null && src.mSharedTerm != null) {
			if (dest.mSharedTerm == null) {
				dest.mSharedTerm = src.mSharedTerm;
			} else {
				final EqualityProxy form = 
					src.mSharedTerm.createEquality(dest.mSharedTerm);
				if (form == EqualityProxy.getFalseProxy()) {
					sharedTermConflict = true;
				}
				else {
					form.createCCEquality(src.mSharedTerm, dest.mSharedTerm);
				// no need to remember the created equality. It was inserted
				// and will be found later automatically.
				}
			}
		}
		
		/* Invert equivalence edges */
		lhs.invertEqualEdges(engine);
		/* Now create a new equaledge to dest. */
		lhs.mEqualEdge = this;
		lhs.mOldRep = src;
		src.mReasonLiteral = reason;
		
		/* Check for conflict */
		if (sharedTermConflict || diseq != null) {
			final Clause conflict = sharedTermConflict 
				? engine.computeCycle(src.mSharedTerm.getCCTerm(), 
									  dest.mSharedTerm.getCCTerm())
				: engine.computeCycle(diseq);
			lhs.mEqualEdge = null;
			lhs.mOldRep = null;
			src.mReasonLiteral = null;
			return conflict;
		}

		long time;

		assert(engine.mMergeDepth == engine.mMerges.size());
		src.mMergeTime = ++engine.mMergeDepth;
		engine.mMerges.push(lhs);
		engine.mEngine.getLogger().debug(new DebugMessage("M {0} {1}", this, lhs));
		assert(engine.mMerges.size() == engine.mMergeDepth);

		if (Config.PROFILE_TIME) {
			time = System.nanoTime();
		}
		/* Update rep fields */
		src.mRep = dest;
		for (final CCTerm t : src.mMembers) {
			t.mRepStar = dest;
		}
		if (Config.PROFILE_TIME) {
			engine.addSetRepTime(System.nanoTime() - time);
		}
		dest.mMembers.joinList(src.mMembers);
		dest.mNumMembers += src.mNumMembers;
		
		if (Config.PROFILE_TIME) {
			time = System.nanoTime();
		}
//		System.err.println("Merge "+this+"+"+lhs+" -> "+src+" "+dest);
		for (final CCTermPairHash.Info.Entry pentry : src.mPairInfos) {
			final CCTermPairHash.Info info = pentry.getInfo();
			assert pentry.getOtherEntry().mOther == src;
			final CCTerm other = pentry.mOther;
			assert other.mRepStar == other;
			if (other == dest) {
				assert (info.mDiseq == null);
				for (final CCEquality.Entry eq : info.mEqlits) {
					engine.addPending(eq.getCCEquality());
				}
			} else {
				CCTermPairHash.Info destInfo = engine.mPairHash.getInfo(dest, other);
				if (destInfo == null) {
					destInfo = new CCTermPairHash.Info(dest, other);
					engine.mPairHash.add(destInfo);
				}
				//System.err.println("M "+src+" "+other+" "+dest);
				/* Merge Infos */
				if (destInfo.mDiseq == null && info.mDiseq != null) {
					destInfo.mDiseq = info.mDiseq;
					for (final CCEquality.Entry eq : destInfo.mEqlits) {
						assert eq.getCCEquality().getDecideStatus() != eq.getCCEquality();
						if (eq.getCCEquality().getDecideStatus() == null) {
							eq.getCCEquality().mDiseqReason = info.mDiseq;
							engine.addPending(eq.getCCEquality().negate());
						}
					}
				} else if (destInfo.mDiseq != null && info.mDiseq == null) {
					for (final CCEquality.Entry eq : info.mEqlits) {
						assert eq.getCCEquality().getDecideStatus() != eq.getCCEquality();
						if (eq.getCCEquality().getDecideStatus() == null) {
							eq.getCCEquality().mDiseqReason = destInfo.mDiseq;
							engine.addPending(eq.getCCEquality().negate());
						}
					}
				}
				destInfo.mEqlits.joinList(info.mEqlits);
			}
			pentry.getOtherEntry().unlink();
			assert other.mPairInfos.wellformed();
			engine.mPairHash.remove(info);
		}
		if (Config.PROFILE_TIME) {
			engine.addEqTime(System.nanoTime() - time);
		}

		if (Config.PROFILE_TIME) {
			time = System.nanoTime();
		}
		/* Compute congruence closure */
		if (mIsFunc) {
			final CCParentInfo srcParentInfo = src.mCCPars.mNext; 
			final CCParentInfo destParentInfo = dest.mCCPars.mNext;
//			assert (srcParentInfo == null || srcParentInfo.m_Next == null);
//			assert (destParentInfo == null || destParentInfo.m_Next == null);
			if (srcParentInfo != null) {
				assert(srcParentInfo.mFuncSymbNr == destParentInfo.mFuncSymbNr);
			tloop:
				for (final CCAppTerm.Parent t1 : srcParentInfo.mCCParents) {
					if (t1.isMarked()) {
						continue;
					}
					final CCAppTerm t = t1.getData();
					for (final CCAppTerm.Parent u1 : destParentInfo.mCCParents) {
						if (u1.isMarked()) {
							continue;
						}
						engine.incCcCount();
						if (t.mArg.mRepStar == u1.getData().mArg.mRepStar) {
							engine.addPendingCongruence(t, u1.getData());
							continue tloop;
						}
					}
				}
				destParentInfo.mCCParents.joinList(srcParentInfo.mCCParents);
			}
		} else {
			CCParentInfo srcParentInfo = src.mCCPars.mNext; 
			CCParentInfo destParentInfo = dest.mCCPars.mNext;
			while (srcParentInfo != null && destParentInfo != null) {
				if (srcParentInfo.mFuncSymbNr < destParentInfo.mFuncSymbNr) {
					srcParentInfo = srcParentInfo.mNext;
				} else if (srcParentInfo.mFuncSymbNr > destParentInfo.mFuncSymbNr) {
					destParentInfo = destParentInfo.mNext;
				} else {
					assert(srcParentInfo.mFuncSymbNr == destParentInfo.mFuncSymbNr);
				tloop:
					for (final CCAppTerm.Parent t1 : srcParentInfo.mCCParents) {
						if (t1.isMarked()) {
							continue;
						}
						final CCAppTerm t = t1.getData();
						for (final CCAppTerm.Parent u1 : destParentInfo.mCCParents) {
							if (u1.isMarked()) {
								continue;
							}
							engine.incCcCount();
							if (t.mFunc.mRepStar == u1.getData().mFunc.mRepStar) {
								engine.addPendingCongruence(t, u1.getData());
								continue tloop;
							}
						}
					}
					srcParentInfo = srcParentInfo.mNext;
					destParentInfo = destParentInfo.mNext;
				}
			}
			dest.mCCPars.mergeParentInfo(src.mCCPars);
		}

		if (Config.PROFILE_TIME) {
			engine.addCcTime(System.nanoTime() - time);
		}
		
		assert invariant();
		assert lhs.invariant();
		assert src.invariant();
		assert dest.invariant();

		return null;
	}

	public void undoMerge(CClosure engine, CCTerm lhs) {
		engine.mEngine.getLogger().debug(new DebugMessage("U {0} {1}", lhs, this));
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
		dest.mCCPars.unmergeParentInfo(src.mCCPars);
		// Congruence merge
		if (src.mReasonLiteral == null) {
			((CCAppTerm)this).unmarkParentInfos();
		}
		
		//System.err.println("Unmerge "+this+"+"+lhs+" -> "+src+" "+dest);
		//Logger.getRootLogger().debug("U"+lhs+"=="+this);
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
				//System.err.println("UM "+src+" "+other+" "+dest);
				final CCTermPairHash.Info destInfo = engine.mPairHash.getInfo(dest, other);
				if (destInfo == null) {
					continue;
				}
				assert destInfo.mEqlits.wellformed();
				destInfo.mEqlits.unjoinList(info.mEqlits);
				assert info.mEqlits.wellformed() && destInfo.mEqlits.wellformed();
				if (destInfo.mDiseq == info.mDiseq) {
					destInfo.mDiseq = null;
				}
				/* Check if we can remove destInfo since it is empty now */
				if (destInfo.mDiseq == null && destInfo.mEqlits.isEmpty()) {
					destInfo.mLhsEntry.unlink();
					destInfo.mRhsEntry.unlink();
					engine.mPairHash.remove(destInfo);
				}
			}
		}
		
		dest.mNumMembers -= src.mNumMembers;
		if (Config.PROFILE_TIME) {
			time = System.nanoTime();
		}
		dest.mMembers.unjoinList(src.mMembers);
		for (final CCTerm t : src.mMembers) {
			t.mRepStar = src;
		}
		src.mRep = src;
		
		assert src.mMergeTime == engine.mMergeDepth;
		engine.mMergeDepth--;
		assert(engine.mMergeDepth == engine.mMerges.size());
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
	
	public SharedTerm getSharedTerm() {
		return mSharedTerm;
	}
	
	@Override
	public int hashCode() {
		return mHashCode;
	}

	public SharedTerm getFlatTerm() {
		return mFlatTerm;
	}
	
	public Term toSMTTerm(Theory t) {
		return new CCTermConverter(t).convert(this);
	}
}
