package local.stalin.smt.theory.cclosure;

import local.stalin.smt.dpll.Clause;
import local.stalin.smt.dpll.SimpleList;
import local.stalin.smt.dpll.SimpleListable;
import local.stalin.smt.theory.cclosure.CCAppTerm.Parent;

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
	private static final boolean profileTime = true;
	
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
	EqualityAtom reasonLiteral;
	CCParentInfo ccpars;
	SimpleList<CCTerm> members;
	int numMembers;
	SimpleList<CCTermPairHash.Info.Entry> pairInfos;
	/**
	 * oldRep.ccMerges contains the merges that were introduced by congruence
	 * closure.  Needed for undoing merges.
	 */
	CongruenceInfo ccMerges;
	TermPairMergeInfo pairMergeInfo;
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

	private boolean invariant() {
		boolean found = false;
		for (CCTerm m : rep.members) {
			if (m == this)
				found = true;
		}
		assert found;
		if (this == rep) {
			assert(members.wellformed());
			assert(pairInfos.wellformed());
			assert(ccpars != null);
			for (CCParentInfo parInfo = ccpars.mNext; 
			     parInfo != null; parInfo = parInfo.mNext) {
				assert(parInfo.mCCParents.wellformed());
				assert(parInfo.mNext == null || parInfo.mFuncSymbNr < parInfo.mNext.mFuncSymbNr);
			}
			for (CCTerm m : members)
				assert (m.rep == this);
			assert(ccMerges == null);
		}
		assert ((equalEdge == null) == (oldRep == null));
		if (equalEdge != null) {
			assert (rep == equalEdge.rep);
		}
		return true;
	}

	protected CCTerm(boolean isFunc, int parentPos) {
		this.isFunc = isFunc;
		this.ccpars = null;
		if (isFunc) {
			parentPosition = parentPos;
		}
		ccpars = new CCParentInfo();
		rep = this;
		members = new SimpleList<CCTerm>();
		pairInfos = new SimpleList<CCTermPairHash.Info.Entry>();
		ccMerges = null;
		members.append(this);
		numMembers = 1;
		assert invariant();
	}
	
	/**
	 * Constructor for CCTerms that are not part of the E-graph, but only used temporarily for
	 * interpolation generation.
	 */
	public CCTerm() {
	}

	public final CCTerm getRepresentative() {
		return rep;
	}

	public void addParentInfo(int funcSymbNr, Parent parent) {
		ccpars.addParentInfo(funcSymbNr, parent);
	}
	
	/**
	 * Clear the equal edge by inverting the edges.
	 */
	public void invertEqualEdges() {
		if (equalEdge == null)
			return;

		long time;
		if (profileTime)
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
		if (profileTime)
			invertEdgeTime += System.nanoTime() - time;
	}
	
	public Clause merge(CClosure engine, CCTerm lhs, EqualityAtom reason) {
		/* Check the representatives of this */
		CCTerm src = lhs.rep;
		CCTerm dest = this.rep;
		assert(src.invariant());
		assert(dest.invariant());
		if (src == dest) {
			/* Terms are already merged. */
			return null;
		}

		//Logger.getRootLogger().debug("M"+lhs+"=="+this);
		mergeCount++;
		if (src.numMembers > dest.numMembers) {
			return lhs.mergeInternal(engine, this, reason);
		} else {
			return this.mergeInternal(engine, lhs, reason);
		}
	}
		
	private Clause mergeInternal(CClosure engine, CCTerm lhs, EqualityAtom reason) {
		/* Check the representatives of this */
		CCTerm src = lhs.rep;
		CCTerm dest = this.rep;

		/* Invert equivalence edges */
		lhs.invertEqualEdges();
		/* Now create a new equaledge to dest. */
		lhs.equalEdge = this;
		lhs.oldRep = src;
		src.reasonLiteral = reason;
		
		/* Check for conflict */
		{
			CCTermPairHash.Info info = engine.pairHash.getInfo(src, dest);
			if (info != null && info.diseq != null) {
				Clause conflict = engine.computeCycle(info.diseq);
				lhs.equalEdge = null;
				lhs.oldRep = null;
				src.reasonLiteral = null;
				return conflict;
			}
		}

		long time;

		if (profileTime)
			time = System.nanoTime();
		/* Update realRep fields */
		for (CCTerm t : src.members) {
			t.rep = dest;
		}		
		if (profileTime)
			setRepTime += System.nanoTime() - time;
		dest.members.joinList(src.members);
		dest.numMembers += src.numMembers;

		if (profileTime)
			time = System.nanoTime();
		//System.err.println("Merge "+this+"+"+lhs+" -> "+src+" "+dest);
		for (CCTermPairHash.Info.Entry pentries : src.pairInfos) {
			CCTermPairHash.Info info = pentries.getInfo();
			assert info.lhs == src || info.rhs == src;
			CCTerm other = info.lhs == src ? info.rhs : info.lhs;
			assert other.rep == other;
			if (other == dest) {
				assert (info.diseq == null);
				for (CCTermPairHash.EqualityEntry eql : info.eqlits) {
					EqualityAtom eq = eql.getData();
					if (eq.getDecideStatus() == null)
						engine.addPending(eq);
				}
				pentries.otherEntry.unlink();
				pentries.unlink();
				engine.pairHash.remove(info);
				src.pairMergeInfo = new TermPairMergeInfo(pentries, src.pairMergeInfo);
			} else {
				CCTermPairHash.Info destInfo = engine.pairHash.getInfo(dest, other);
				if (destInfo != null) {
					//System.err.println("M "+src+" "+other+" "+dest);
					/* Merge Infos */
					if (destInfo.diseq == null && info.diseq != null) {
						destInfo.diseq = info.diseq;
						for (CCTermPairHash.EqualityEntry eql : destInfo.eqlits) {
							EqualityAtom eq = eql.getData();
							engine.addPending(eq.negate());
						}
					} else if (destInfo.diseq != null && info.diseq == null) {
						for (CCTermPairHash.EqualityEntry eql : info.eqlits) {
							EqualityAtom eq = eql.getData();
							engine.addPending(eq.negate());
						}
					}
					destInfo.eqlits.joinList(info.eqlits);
					pentries.otherEntry.unlink();
					pentries.unlink();
					engine.pairHash.remove(info);
					src.pairMergeInfo = new TermPairMergeInfo(pentries, src.pairMergeInfo);
				} else {
					//System.err.println("C "+src+" "+other+"->"+dest);
					engine.pairHash.remove(info);
					if (info.lhs == src)
						info.lhs = dest;
					else
						info.rhs = dest;
					engine.pairHash.add(info);
				}
			}
		}
		dest.pairInfos.joinList(src.pairInfos);
		if (profileTime)
			eqTime += System.nanoTime() - time;

		if (profileTime)
			time = System.nanoTime();
		/* Compute congruence closure */
		/*DiseqReason diseqReason;*/
		if (isFunc) {
			CCParentInfo srcParentInfo = src.ccpars.mNext; 
			CCParentInfo destParentInfo = dest.ccpars.mNext;
			assert (srcParentInfo == null || srcParentInfo.mNext == null);
			assert (destParentInfo == null || destParentInfo.mNext == null);
			if (srcParentInfo != null) {
				assert(srcParentInfo.mFuncSymbNr == destParentInfo.mFuncSymbNr);
				tloop: for (CCAppTerm.Parent t1 : srcParentInfo.mCCParents) {
					CCAppTerm t = t1.getData();
					for (CCAppTerm.Parent u1 : destParentInfo.mCCParents) {
						ccCount++;
						if (t.arg.rep == u1.getData().arg.rep) {
							src.ccMerges = new CongruenceInfo(t, u1.getData(), src.ccMerges);
							t.unlinkParentInfos();
							continue tloop;
						}
					}
				}
				destParentInfo.mCCParents.joinList(srcParentInfo.mCCParents);
			}
		} else {
			CCParentInfo srcParentInfo = src.ccpars.mNext; 
			CCParentInfo destParentInfo = dest.ccpars.mNext;
			while (srcParentInfo != null && destParentInfo != null) {
				if (srcParentInfo.mFuncSymbNr < destParentInfo.mFuncSymbNr)
					srcParentInfo = srcParentInfo.mNext;
				else if (srcParentInfo.mFuncSymbNr > destParentInfo.mFuncSymbNr)
					destParentInfo = destParentInfo.mNext;
				else {	
					assert(srcParentInfo.mFuncSymbNr == destParentInfo.mFuncSymbNr);
					tloop: for (CCAppTerm.Parent t1 : srcParentInfo.mCCParents) {
						CCAppTerm t = t1.getData();
						for (CCAppTerm.Parent u1 : destParentInfo.mCCParents) {
							ccCount++;
							if (t.func.rep == u1.getData().func.rep) {
								src.ccMerges = new CongruenceInfo(t, u1.getData(), src.ccMerges);
								t.unlinkParentInfos();
								continue tloop;
							}
						}
					}
					srcParentInfo = srcParentInfo.mNext;
					destParentInfo = destParentInfo.mNext;
				}
			}
			dest.ccpars.mergeParentInfo(src.ccpars);
		}

		if (profileTime)
			ccTime += System.nanoTime() - time;
		
		assert invariant();
		assert lhs.invariant();
		assert src.invariant();
		assert dest.invariant();

		/* Merge congruence closure list (need to reverse it first) */
		CongruenceInfo last = null;
		CongruenceInfo entry = src.ccMerges;
		while (entry != null) {
			CongruenceInfo next = entry.next;
			entry.next = last;
			last = entry;
			entry = next;
		}
		/* Now merge and revert it again */
		Clause conflict = null;
		entry = last;
		last = null;
		while (entry != null) {
			CongruenceInfo next = entry.next;
			entry.next = last;
			if (conflict == null) {
				CCTerm first = entry.appTerm1;
				CCTerm second = entry.appTerm2;
				if (first.rep != second.rep) {
					entry.merged = true;
					conflict = second.merge(engine, first, null);
				}
			}
			last = entry;
			entry = next;
		}
		assert last == src.ccMerges;
		return conflict;
	}

	public void undoMerge(CClosure engine, CCTerm lhs) {
		long time;
		CCTerm src, dest;

		assert invariant();
		assert lhs.invariant();
		assert this.equalEdge == lhs;
		assert rep == lhs.rep;
		
		
		src = oldRep;
		equalEdge = null;
		oldRep = null;

		for (CongruenceInfo entry = src.ccMerges; entry != null; entry = entry.next) {
			if (entry.merged) {
				CCTerm t1 = entry.appTerm1;
				CCTerm t2 = entry.appTerm2;
				if (t1.equalEdge == t2)
					t1.undoMerge(engine, t2);
				else if (t2.equalEdge == t1)
					t2.undoMerge(engine, t1);
			}
		}
		/* Important: Set dest only after recursive undoMerge occured */
		dest = rep;

		dest.ccpars.unmergeParentInfo(src.ccpars);
		for (CongruenceInfo entry = src.ccMerges; entry != null; entry = entry.next)
			entry.appTerm1.relinkParentInfos();
		src.ccMerges = null;
		
		//System.err.println("Unmerge "+this+"+"+lhs+" -> "+src+" "+dest);
		//Logger.getRootLogger().debug("U"+lhs+"=="+this);
		src.reasonLiteral = null;
		dest.pairInfos.unjoinList(src.pairInfos);
		for (CCTermPairHash.Info.Entry e : src.pairInfos) {
			CCTermPairHash.Info info = e.getInfo();
			assert info.lhs == dest || info.rhs == dest;
			CCTerm other = info.lhs == dest ? info.rhs : info.lhs;
			assert other.rep == other;
			//System.err.println("UC "+src+" "+other+"<-"+dest);
			engine.pairHash.remove(info);
			if (info.lhs == dest)
				info.lhs = src;
			else
				info.rhs = src;
			engine.pairHash.add(info);
		}
		TermPairMergeInfo mergeInfo = src.pairMergeInfo;
		src.pairMergeInfo = null;
		while (mergeInfo != null) {
			CCTermPairHash.Info.Entry pentry = mergeInfo.info;
			CCTermPairHash.Info info = pentry.getInfo();
			assert info.lhs == src || info.rhs == src;
			engine.pairHash.add(pentry.getInfo());
			pentry.relink();
			pentry.otherEntry.relink();
			CCTerm other = info.lhs == src ? info.rhs : info.lhs;
			assert other.rep == other;
			if (other != dest) {
				//System.err.println("UM "+src+" "+other+" "+dest);
				CCTermPairHash.Info destInfo = engine.pairHash.getInfo(dest, other);
				assert(destInfo.eqlits.wellformed());
				destInfo.eqlits.unjoinList(info.eqlits);
				assert(info.eqlits.wellformed() && destInfo.eqlits.wellformed());
				if (destInfo.diseq == info.diseq)
					destInfo.diseq = null;
			}
			mergeInfo = mergeInfo.next;
		}
		
		dest.numMembers -= src.numMembers;
		if (profileTime)
			time = System.nanoTime();
		dest.members.unjoinList(src.members);
		for (CCTerm t : src.members)
			t.rep = src;
		if (profileTime)
			setRepTime += System.nanoTime() - time;
		assert invariant();
		assert lhs.invariant();
		assert src.invariant();
		assert dest.invariant();
	}

	/**
	 * Returns the number of the first formula that contains all
	 * symbols from this term.  This is used for interpolation.
	 * @return the first formula.
	 */
	public abstract int getFirstFormula();
	/**
	 * Returns the number of the last formula that contains all
	 * symbols from this term.  This is used for interpolation.
	 * @return the last formula.
	 */
	public abstract int getLastFormula();
	/**
	 * Call this on a term, if it occurs in a formula.  This updates
	 * first and last formula counter.  Used for interpolation.
	 */
	public abstract void occursIn(int formulaNr);
}
