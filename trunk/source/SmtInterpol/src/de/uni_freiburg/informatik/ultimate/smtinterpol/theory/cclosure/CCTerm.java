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
	public static long invertEdgeTime, eqTime, ccTime, setRepTime;
	public static long ccCount, mergeCount;
	
	/**
	 * The destination of the outgoing equality edge.  Every term has at
	 * most one equality edge, which was introduced by some merge operation.
	 * The edges may be inverted to allow introducing new equality edges.
	 */
	CCTerm equalEdge;
	/**
	 * The representative of the congruence class.  The representative 
	 * is the one that contains the members, ccpar and eqlits information.
	 */
	CCTerm repStar;
	/**
	 * Points to the next merged representative in the congruence class. 
	 * This representative can have another representative of its own, if 
	 * it is merged later with another class.
	 * This field equals this, iff the term is the representative of its class.
	 */
	CCTerm rep;
	/**
	 * The representative of the source congruence class before the merge
	 * that introduced this.equalEdge.  Note that due to inverting the edge
	 * the old representative may be the representative of the destination
	 * of the equality edge.
	 */
	CCTerm oldRep;
	/**
	 * oldRep.reasonLiteral contains the reason why equalEdge was introduced.
	 */
	CCEquality reasonLiteral;
	/**
	 * the time stamp (or rather stack depth) when the merge of this node with
	 * its representative rep took place.
	 */
	int mergeTime = Integer.MAX_VALUE;
	CCParentInfo ccpars;
	SimpleList<CCTerm> members;
	int numMembers;
	SimpleList<CCTermPairHash.Info.Entry> pairInfos;
	SharedTerm sharedTerm;
	SharedTerm flatTerm;
	
	int hashCode;
	
	static class TermPairMergeInfo {
		CCTermPairHash.Info.Entry info;
		TermPairMergeInfo next;
		public TermPairMergeInfo(CCTermPairHash.Info.Entry i, TermPairMergeInfo n) {
			info = i;
			next = n;
		}
	}
	static class CongruenceInfo {
		CCAppTerm appTerm1;
		CCAppTerm appTerm2;
		boolean merged;
		CongruenceInfo next;

		public CongruenceInfo(CCAppTerm app1, CCAppTerm app2, CongruenceInfo next) {
			this.appTerm1 = app1;
			this.appTerm2 = app2;
			this.next = next;
		}
	}
	
	boolean isFunc;
	int parentPosition;

	protected CCTerm(boolean isFunc, int parentPos, SharedTerm term, int hash) {
		this.isFunc = isFunc;
		this.ccpars = null;
		if (isFunc) {
			parentPosition = parentPos;
		}
		ccpars = new CCParentInfo();
		rep = repStar = this;
		members = new SimpleList<CCTerm>();
		pairInfos = new SimpleList<CCTermPairHash.Info.Entry>();
		members.append(this);
		numMembers = 1;
		assert invariant();
		flatTerm = term;
		hashCode = hash;
	}
	
	/**
	 * Constructor for CCTerms that are not part of the E-graph, but only used temporarily for
	 * interpolation generation.
	 */
	public CCTerm() {
	}

	boolean pairHashValid(CClosure engine) {
		if (Config.EXPENSIVE_ASSERTS){
			for (CCTermPairHash.Info.Entry pentry : pairInfos) {
				CCTermPairHash.Info info = pentry.getInfo();
				assert pentry.getOtherEntry().other == this;
				if (this == rep) {
					assert engine.pairHash.getInfo(this, pentry.other) == info;
				}
			}
		}
		return true;
	}

	boolean invariant() {
		if (Config.EXPENSIVE_ASSERTS) {
		boolean found = false;
		for (CCTerm m : repStar.members) {
			if (m == this)
				found = true;
		}
		assert found;
		assert(pairInfos.wellformed());
		if (this == repStar)
			assert(members.wellformed());
		for (CCTermPairHash.Info.Entry pentry : pairInfos) {
			assert pentry.getOtherEntry().other == this;
			CCTerm other = pentry.other;
			assert other.mergeTime >= this.mergeTime;
			if (this == repStar || pentry.other == rep)
				assert(pentry.getInfo().eqlits.wellformed());
			else
				assert(pentry.getInfo().eqlits.wellformedPart());
		}
		if (this == repStar) {
			assert(ccpars != null);
			for (CCParentInfo parInfo = ccpars.m_Next; 
			     parInfo != null; parInfo = parInfo.m_Next) {
				assert(parInfo.m_CCParents.wellformed());
				assert(parInfo.m_Next == null || parInfo.m_FuncSymbNr < parInfo.m_Next.m_FuncSymbNr);
			}
			for (CCTerm m : members)
				assert (m.repStar == this);
		}
		assert ((equalEdge == null) == (oldRep == null));
		if (equalEdge != null) {
			assert (repStar == equalEdge.repStar);
		}
		}
		return true;
	}

	public final CCTerm getRepresentative() {
		return repStar;
	}

	public void share(CClosure engine, SharedTerm sterm) {
		if (this.sharedTerm != null) {
			if (this.sharedTerm == sterm)
				return;
			propagateSharedEquality(engine, sterm);
		}
		CCTerm term = this;
		SharedTerm oldTerm = this.sharedTerm;
		this.sharedTerm = sterm;
		while (term.rep != term) {
			term = term.rep;
			if (term.sharedTerm == oldTerm)
				term.sharedTerm = sterm;
			else {
				term.propagateSharedEquality(engine, sterm);
				break;
			}
		}
	}
	
	public void unshare(SharedTerm sterm) {
		assert this.sharedTerm == sterm;
		assert this.rep == this;
		this.sharedTerm = null;
	}
	
	private void propagateSharedEquality(CClosure engine, SharedTerm sterm) {
		/* create equality formula.  This should never give TRUE or FALSE,
		 * as sterm is a newly shared term, which must be linear independent
		 * of all previously created terms. 
		 */
		EqualityProxy eqForm = sharedTerm.createEquality(sterm);
		assert (eqForm != EqualityProxy.getTrueProxy());
		assert (eqForm != EqualityProxy.getFalseProxy());
		CCEquality cceq = eqForm.createCCEquality(this.sharedTerm, sterm);
		if (engine.engine.getLogger().isDebugEnabled())
			engine.engine.getLogger().debug("PL: "+cceq);
		engine.addPending(cceq);
	}

	/**
	 * Clear the equal edge by inverting the edges.
	 */
	public void invertEqualEdges() {
		if (equalEdge == null)
			return;

		long time;
		if (Config.PROFILE_TIME)
			time = System.nanoTime();
		CCTerm last = null;
		CCTerm lastRep = null;
		CCTerm next = this;
		while (next != null) {
			CCTerm t = next;
			next = next.equalEdge;
			t.equalEdge = last;
			CCTerm nextRep = t.oldRep;
			t.oldRep = lastRep;
			last = t;
			lastRep = nextRep;
		}
		if (Config.PROFILE_TIME)
			invertEdgeTime += System.nanoTime() - time;
	}
	
	public Clause merge(CClosure engine, CCTerm lhs, CCEquality reason) {
		assert(reason != null || (this instanceof CCAppTerm && lhs instanceof CCAppTerm));
		assert(engine.mergeDepth == engine.merges.size());

		/* Check the representatives of this */
		CCTerm src = lhs.repStar;
		CCTerm dest = this.repStar;
		assert (src.invariant());
		assert (src.pairHashValid(engine));
		assert (dest.invariant());
		assert (dest.pairHashValid(engine));
		if (src == dest) {
			/* Terms are already merged. */
			return null;
		}

		//Logger.getRootLogger().debug("M"+lhs+"=="+this);
		mergeCount++;
		Clause res;
		if (src.numMembers > dest.numMembers) {
			res = lhs.mergeInternal(engine, this, reason);
			if (res == null && reason == null)
				((CCAppTerm)this).markParentInfos();
		} else {
			res = this.mergeInternal(engine, lhs, reason);
			if (res == null && reason == null)
				((CCAppTerm)lhs).markParentInfos();
		}
		assert (engine.mergeDepth == engine.merges.size());
		assert invariant();
		assert (lhs.invariant());
		assert (repStar.pairHashValid(engine));
		return res;
	}
	
	private Clause mergeInternal(CClosure engine, CCTerm lhs, CCEquality reason) {
		/* Check the representatives of this */
		CCTerm src = lhs.repStar;
		CCTerm dest = this.repStar;
		
		// Need to prevent MBTC when we get a conflict. Hence a two-way pass
		CCEquality diseq = null;
		{
			CCTermPairHash.Info info = engine.pairHash.getInfo(src, dest);
			if (info != null) {
				diseq = info.diseq;
			}
		}
		boolean sharedTermConflict = false;
		if (diseq == null && src.sharedTerm != null) {
			if (dest.sharedTerm != null) {
				EqualityProxy form = 
					src.sharedTerm.createEquality(dest.sharedTerm);
				if (form == EqualityProxy.getFalseProxy())
					sharedTermConflict = true;
				else
					form.createCCEquality(src.sharedTerm, dest.sharedTerm);
				// no need to remember the created equality. Is was inserted
				// and will be found later automatically.
			} else
				dest.sharedTerm = src.sharedTerm;
		}
		
		/* Invert equivalence edges */
		lhs.invertEqualEdges();
		/* Now create a new equaledge to dest. */
		lhs.equalEdge = this;
		lhs.oldRep = src;
		src.reasonLiteral = reason;
		
		/* Check for conflict */
		if (sharedTermConflict || diseq != null) {
			Clause conflict = sharedTermConflict 
				? engine.computeCycle(src.sharedTerm.getCCTerm(), 
									  dest.sharedTerm.getCCTerm())
				: engine.computeCycle(diseq);
			lhs.equalEdge = null;
			lhs.oldRep = null;
			src.reasonLiteral = null;
			return conflict;
		}

		long time;

		assert(engine.mergeDepth == engine.merges.size());
		src.mergeTime = ++engine.mergeDepth;
		engine.merges.push(lhs);
		engine.engine.getLogger().debug(new DebugMessage("M {0} {1}", this, lhs));
		assert(engine.merges.size() == engine.mergeDepth);

		if (Config.PROFILE_TIME)
			time = System.nanoTime();
		/* Update rep fields */
		src.rep = dest;
		for (CCTerm t : src.members) {
			t.repStar = dest;
		}
		if (Config.PROFILE_TIME)
			setRepTime += System.nanoTime() - time;
		dest.members.joinList(src.members);
		dest.numMembers += src.numMembers;
		
		if (Config.PROFILE_TIME)
			time = System.nanoTime();
//		System.err.println("Merge "+this+"+"+lhs+" -> "+src+" "+dest);
		for (CCTermPairHash.Info.Entry pentry : src.pairInfos) {
			CCTermPairHash.Info info = pentry.getInfo();
			assert pentry.getOtherEntry().other == src;
			CCTerm other = pentry.other;
			assert other.repStar == other;
			if (other == dest) {
				assert (info.diseq == null);
				for (CCEquality.Entry eq : info.eqlits) {
					engine.addPending(eq.getCCEquality());
				}
			} else {
				CCTermPairHash.Info destInfo = engine.pairHash.getInfo(dest, other);
				if (destInfo == null) {
					destInfo = new CCTermPairHash.Info(dest, other);
					engine.pairHash.add(destInfo);
				}
				destInfo.arrayextadded += info.arrayextadded;
				//System.err.println("M "+src+" "+other+" "+dest);
				/* Merge Infos */
				if (destInfo.diseq == null && info.diseq != null) {
					destInfo.diseq = info.diseq;
					for (CCEquality.Entry eq : destInfo.eqlits) {
						assert (eq.getCCEquality().getDecideStatus() != eq.getCCEquality());
						if (eq.getCCEquality().getDecideStatus() == null) {
							eq.getCCEquality().m_diseqReason = info.diseq;
							engine.addPending(eq.getCCEquality().negate());
						}
					}
				} else if (destInfo.diseq != null && info.diseq == null) {
					for (CCEquality.Entry eq : info.eqlits) {
						assert (eq.getCCEquality().getDecideStatus() != eq.getCCEquality());
						if (eq.getCCEquality().getDecideStatus() == null) {
							eq.getCCEquality().m_diseqReason = destInfo.diseq;
							engine.addPending(eq.getCCEquality().negate());
						}
					}
				}
				destInfo.eqlits.joinList(info.eqlits);
			}
			pentry.getOtherEntry().unlink();
			assert other.pairInfos.wellformed();
			engine.pairHash.remove(info);
		}
		if (Config.PROFILE_TIME)
			eqTime += System.nanoTime() - time;

		if (Config.PROFILE_TIME)
			time = System.nanoTime();
		/* Compute congruence closure */
		// XXX Get candidates for reverse triggers registered on src and dest
		if (isFunc) {
			CCParentInfo srcParentInfo = src.ccpars.m_Next; 
			CCParentInfo destParentInfo = dest.ccpars.m_Next;
//			assert (srcParentInfo == null || srcParentInfo.m_Next == null);
//			assert (destParentInfo == null || destParentInfo.m_Next == null);
			if (srcParentInfo != null) {
				assert(srcParentInfo.m_FuncSymbNr == destParentInfo.m_FuncSymbNr);
				tloop: for (CCAppTerm.Parent t1 : srcParentInfo.m_CCParents) {
					if (t1.isMarked()) continue;
					CCAppTerm t = t1.getData();
					for (CCAppTerm.Parent u1 : destParentInfo.m_CCParents) {
						if (u1.isMarked()) continue;
						ccCount++;
						if (t.arg.repStar == u1.getData().arg.repStar) {
							engine.addPendingCongruence(t, u1.getData());
							continue tloop;
						}
					}
				}
				destParentInfo.m_CCParents.joinList(srcParentInfo.m_CCParents);
			}
		} else {
			CCParentInfo srcParentInfo = src.ccpars.m_Next; 
			CCParentInfo destParentInfo = dest.ccpars.m_Next;
			while (srcParentInfo != null && destParentInfo != null) {
				if (srcParentInfo.m_FuncSymbNr < destParentInfo.m_FuncSymbNr)
					srcParentInfo = srcParentInfo.m_Next;
				else if (srcParentInfo.m_FuncSymbNr > destParentInfo.m_FuncSymbNr)
					destParentInfo = destParentInfo.m_Next;
				else {
					assert(srcParentInfo.m_FuncSymbNr == destParentInfo.m_FuncSymbNr);
					tloop: for (CCAppTerm.Parent t1 : srcParentInfo.m_CCParents) {
						if (t1.isMarked()) continue;
						CCAppTerm t = t1.getData();
						for (CCAppTerm.Parent u1 : destParentInfo.m_CCParents) {
							if (u1.isMarked()) continue;
							ccCount++;
							if (t.func.repStar == u1.getData().func.repStar) {
								engine.addPendingCongruence(t, u1.getData());
								continue tloop;
							}
						}
					}
					srcParentInfo = srcParentInfo.m_Next;
					destParentInfo = destParentInfo.m_Next;
				}
			}
			dest.ccpars.mergeParentInfo(src.ccpars);
		}

		if (Config.PROFILE_TIME)
			ccTime += System.nanoTime() - time;
		
		assert invariant();
		assert lhs.invariant();
		assert src.invariant();
		assert dest.invariant();

		return null;
	}

	public void undoMerge(CClosure engine, CCTerm lhs) {
		engine.engine.getLogger().debug(new DebugMessage("U {0} {1}", lhs, this));
		long time;
		CCTerm src, dest;

		assert invariant();
		assert lhs.invariant();
		assert(repStar.pairHashValid(engine));
		assert this.equalEdge == lhs;
		assert repStar == lhs.repStar;
		
		src = oldRep;
		equalEdge = null;
		oldRep = null;
		dest = repStar;
		dest.ccpars.unmergeParentInfo(src.ccpars);
		// Congruence merge
		if (src.reasonLiteral == null) {
			((CCAppTerm)this).unmarkParentInfos();
			// TODO Is this line needed? I don't think so...
//			((CCAppTerm)lhs).unmarkParentInfos();
		}
		
		//System.err.println("Unmerge "+this+"+"+lhs+" -> "+src+" "+dest);
		//Logger.getRootLogger().debug("U"+lhs+"=="+this);
		src.reasonLiteral = null;
		for (CCTermPairHash.Info.Entry pentry : src.pairInfos.reverse()) {
			CCTermPairHash.Info info = pentry.getInfo();
			assert pentry.getOtherEntry().other == src;
			engine.pairHash.add(pentry.getInfo());
			assert pentry.other.pairInfos.wellformed();
			pentry.other.pairInfos.append(pentry.getOtherEntry());
			assert pentry.other.pairInfos.wellformed();
			CCTerm other = pentry.other;
			assert other.repStar == other;
			if (other != dest) {
				//System.err.println("UM "+src+" "+other+" "+dest);
				CCTermPairHash.Info destInfo = engine.pairHash.getInfo(dest, other);
				// FIXME: Is this correct?
				if (destInfo == null)
					continue;
				destInfo.arrayextadded -= info.arrayextadded;
				assert(destInfo.eqlits.wellformed());
				destInfo.eqlits.unjoinList(info.eqlits);
				assert(info.eqlits.wellformed() && destInfo.eqlits.wellformed());
				if (destInfo.diseq == info.diseq)
					destInfo.diseq = null;
				/* Check if we can remove destInfo since it is empty now */
				if (destInfo.diseq == null && destInfo.eqlits.isEmpty()) {
					destInfo.lhsEntry.unlink();
					destInfo.rhsEntry.unlink();
					engine.pairHash.remove(destInfo);
				}
			}
		}
		
		dest.numMembers -= src.numMembers;
		if (Config.PROFILE_TIME)
			time = System.nanoTime();
		dest.members.unjoinList(src.members);
		for (CCTerm t : src.members)
			t.repStar = src;
		src.rep = src;
		
		assert src.mergeTime == engine.mergeDepth;
		engine.mergeDepth--;
		assert(engine.mergeDepth == engine.merges.size());
		src.mergeTime = Integer.MAX_VALUE;
		if (Config.PROFILE_TIME)
			setRepTime += System.nanoTime() - time;

		if (dest.sharedTerm == src.sharedTerm)
			dest.sharedTerm = null;
		
		assert invariant();
		assert lhs.invariant();
		assert src.invariant();
		assert dest.invariant();
		assert(src.pairHashValid(engine));
		assert(dest.pairHashValid(engine));
	}
	
	public SharedTerm getSharedTerm() {
		return sharedTerm;
	}
	
	public int hashCode() {
		return hashCode;
	}

	public SharedTerm getFlatTerm() {
		return flatTerm;
	}
	
	public abstract Term toSMTTerm(Theory t, boolean useAuxVars);
	public Term toSMTTerm(Theory t) {
		return toSMTTerm(t, false);
	}
}
