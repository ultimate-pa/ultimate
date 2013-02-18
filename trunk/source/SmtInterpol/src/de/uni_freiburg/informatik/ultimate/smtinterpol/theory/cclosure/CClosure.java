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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SharedTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ITheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.SimpleList;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.Model;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.SharedTermEvaluator;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.LeafNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTermPairHash.Info.Entry;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LAEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.ArrayQueue;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.ListSet;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;
import de.uni_freiburg.informatik.ultimate.util.ScopedHashMap;

public class CClosure implements ITheory {
	private final class CCAppTermPair {
		CCAppTerm first,second;
		public CCAppTermPair(CCAppTerm first,CCAppTerm second) {
			this.first = first;
			this.second = second;
		}
		public int hashCode() {
			// Needs to be symmetric
			return first.hashCode() + second.hashCode();
		}
		public boolean equals(Object o) {
			if (o instanceof CCAppTermPair) {
				CCAppTermPair p = (CCAppTermPair)o;
				return (first == p.first && second == p.second) || 
					(first == p.second && second == p.first);
			}
			return false;
		}
		public String toString() {
			return first + " " + second;
		}
	}
	DPLLEngine engine;
	ArrayList<CCTerm> allTerms = new ArrayList<CCTerm>();
	CCTermPairHash pairHash = new CCTermPairHash();
	ArrayQueue<Literal> pendingLits = new ArrayQueue<Literal>();
	ScopedHashMap<Object, CCTerm> symbolicTerms = new ScopedHashMap<Object, CCTerm>();
	int numFunctionPositions;
	int mergeDepth;
	ArrayDeque<CCTerm> merges = new ArrayDeque<CCTerm>();
	ArrayDeque<CCAppTermPair> pendingCongruences =
		new ArrayDeque<CCAppTermPair>();
	// E-Matching Support
//	boolean ematchingActive = false;
	TriggerExecutionContext root;
	TriggerExecutionContext.ReactivationContext lastRC;
	TriggerExecutionContext doneYields = null;
	
	// Array Support
	ListSet<CCTerm> m_foreignarrays = new ListSet<CCTerm>();
	Clausifier clausifier;
	int curinsts = 0;

	public CClosure(DPLLEngine engine, Clausifier clausifier) {
		this.engine = engine;
		this.clausifier = clausifier;
		root = new TriggerExecutionContext();
		lastRC = root.new ReactivationContext();
	}
	
	public CCTerm createAnonTerm(SharedTerm flat) {
		CCTerm term = new CCBaseTerm(false, numFunctionPositions, flat, flat);
		allTerms.add(term);
		return term;
	}


	public CCTerm createAppTerm(boolean isFunc, CCTerm func, CCTerm arg) {
		assert(func.isFunc);
		CCParentInfo info = arg.repStar.ccpars.getExistingParentInfo(func.parentPosition);
		if (info != null) {
			SimpleList<CCAppTerm.Parent> prevParents = info.m_CCParents;
			assert(prevParents.wellformed());
			for (CCAppTerm.Parent termpar : prevParents) {
				CCAppTerm term = termpar.getData();
				if (term.func == func && term.arg == arg) {
					return term;
				}
			}
		}
		CCAppTerm term = new CCAppTerm(isFunc, 
				isFunc ? func.parentPosition + 1 : 0, func, arg, null, this);
		CCAppTerm congruentTerm = term.addParentInfo(this);
		if (congruentTerm != null) {
			// Here, we do not have the resulting term in the equivalence class
			// Mark pending congruence
			addPendingCongruence(term, congruentTerm);
		}
		return term;
	}
	
	private CCTerm convertFuncTerm(FunctionSymbol sym, CCTerm[] args, int numArgs) {
		if (numArgs == 0) {
			CCTerm term = symbolicTerms.get(sym);
			if (term == null) {
				term = new CCBaseTerm(args.length > 0, numFunctionPositions, sym, null);
				numFunctionPositions += args.length;
				symbolicTerms.put(sym, term);
			}
			return term;
		} else {
			CCTerm pred = convertFuncTerm(sym, args, numArgs-1);
			return createAppTerm(numArgs < args.length, pred, args[numArgs-1]);
		}
	}
	
	/**
	 * Function to retrieve the CCTerm representing a function symbol. This
	 * function should be used by the pattern compiler to retrieve the correct
	 * number of the function symbol.
	 * @param sym Function symbol.
	 * @return CCTerm representing this function symbol in the egraph.
	 */
	public CCTerm getFuncTerm(FunctionSymbol sym) {
		CCTerm term = symbolicTerms.get(sym);
		if (term == null) {
			term = new CCBaseTerm(sym.getParameterCount() > 0,
					numFunctionPositions,sym,null);
			numFunctionPositions += sym.getParameterCount();
			symbolicTerms.put(sym,term);
		}
		return term;
	}
	
	public void insertEqualityEntry(CCTerm t1, CCTerm t2, 
								    CCEquality.Entry eqentry) {
		if (t1.mergeTime > t2.mergeTime) {
			CCTerm tmp = t1;
			t1 = t2;
			t2 = tmp;
		}
			
		if (t1.rep == t1) {
			assert t2.rep == t2;
			CCTermPairHash.Info info = pairHash.getInfo(t1, t2);
			if (info == null) {
				info = new CCTermPairHash.Info(t1, t2);
				pairHash.add(info);
			}
			info.eqlits.prependIntoJoined(eqentry, true);
		} else {
			boolean isLast = t1.rep == t2;
			boolean found = false;
			for (CCTermPairHash.Info.Entry pentry : t1.pairInfos) {
				CCTermPairHash.Info info = pentry.getInfo();
				// info might have blocked compare triggers but no eqlits
//				assert (!info.eqlits.isEmpty());
				if (pentry.other == t2) {
					info.eqlits.prependIntoJoined(eqentry, isLast);
					found = true;
					break;
				}
			}
			if  (!found) {
				CCTermPairHash.Info info = new CCTermPairHash.Info(t1, t2);
				info.rhsEntry.unlink();
				info.eqlits.prependIntoJoined(eqentry, isLast);
			}
			if (!isLast)
				insertEqualityEntry(t1.rep, t2, eqentry);
		}
	}
	
	public CCEquality createCCEquality(int stackLevel, CCTerm t1, CCTerm t2) {
		assert (t1 != t2);
		CCEquality eq = null;
		assert (t1.invariant());
		assert (t2.invariant());
		
		eq = new CCEquality(stackLevel, t1, t2);
		insertEqualityEntry(t1, t2, eq.getEntry());
		engine.addAtom(eq);
		
		assert(t1.invariant());
		assert(t2.invariant());
		assert(t1.pairHashValid(this));
		assert(t2.pairHashValid(this));
		
		if (t1.repStar == t2.repStar) {
			if (engine.getLogger().isDebugEnabled())
				engine.getLogger().debug("CC-Prop: " + eq + " repStar: " + t1.repStar);
			pendingLits.add(eq);
		} else {
			CCEquality diseq = pairHash.getInfo(t1.repStar, t2.repStar).diseq; 
			if (diseq != null) {
				if (engine.getLogger().isDebugEnabled())
					engine.getLogger().debug("CC-Prop: " + eq.negate() + " diseq: " + diseq);
				eq.m_diseqReason = diseq;
				pendingLits.add(eq.negate());
			}
		}
		return eq;
	}
	public boolean knowsConstant(FunctionSymbol sym) {
		return symbolicTerms.containsKey(sym);
	}
	public CCTerm createFuncTerm(
			FunctionSymbol sym, CCTerm[] subterms, SharedTerm fapp) {
		CCTerm term = convertFuncTerm(sym, subterms, subterms.length);
		if (term.flatTerm == null) {
			allTerms.add(term);
		}
		term.flatTerm = fapp;
		return term;
	}
	
	public void addTerm(CCTerm term, SharedTerm shared) {
		term.flatTerm = shared;
		allTerms.add(term);
	}
			
	@Override
	public void backtrackLiteral(Literal literal) {
		if (!(literal.getAtom() instanceof CCEquality))
			return;
		CCEquality eq = (CCEquality) literal.getAtom();
		if (eq.stackDepth != -1) {
			backtrackStack(eq.stackDepth);
			eq.stackDepth = -1;
			if (literal != eq)
				undoSep(eq);
		}
	}

	@Override
	public Clause computeConflictClause() {
		Clause res = checkpoint();
		// Only do array instantiations if we do not have a conflict so far
		if (res == null) {
			res = checkpoint();
		}
		assert(pendingCongruences.isEmpty());
//		assert(root.next == root);
		return res;
	}
	
	boolean processTriggers(int maxnum) {
//		System.err.println("Processing triggers for " + maxnum + " insts");
		curinsts = 0;
		// Do all trigger instructions
		while (root.next != root && curinsts < maxnum) {
			// Remove from front of the list list
			TriggerExecutionContext tec = root.next;
			root.next = tec.next;
			root.next.prev = root;
			// Re-execute
			tec.reexecute(this);
			// Clear in list status
			tec.next = tec.prev = null;
		}
		return root.next != root;
	}

	public Literal getPropagatedLiteral() {
		Literal lit = pendingLits.poll();
		assert (lit == null || checkPending(lit));
		return lit;
	}
	
	@Override
	public Clause getUnitClause(Literal lit) {
		if (lit.getAtom() instanceof LAEquality) {
			LAEquality laeq = (LAEquality) lit.getAtom();
			for (CCEquality eq : laeq.getDependentEqualities()) {
				if (eq.getStackPosition() >= 0 
					&& eq.getStackPosition() < laeq.getStackPosition()) {
					return new Clause(new Literal[] { eq.getDecideStatus().negate(), lit },
							new LeafNode(LeafNode.EQ, null));
				}
			}
			throw new AssertionError("Cannot find explanation for "+laeq);
		} else if (lit instanceof CCEquality) {
			CCEquality eq = (CCEquality) lit;
			return computeCycle(eq);
		} else {
			/* ComputeAntiCycle */
			CCEquality eq = (CCEquality) lit.negate();
			return computeAntiCycle(eq);
		}
	}

	@Override
	public Clause setLiteral(Literal literal) {
		if (!(literal.getAtom() instanceof CCEquality))
			return null;
		CCEquality eq = (CCEquality) literal.getAtom();
		LAEquality laeq = eq.getLASharedData(); 
		if (laeq != null) {
			assert ((List<CCEquality>)laeq.getDependentEqualities()).contains(eq);
			if (laeq.getDecideStatus() != null
				&& laeq.getDecideStatus().getSign() != literal.getSign()) {
				return new Clause(new Literal[] { laeq.getDecideStatus().negate(), literal.negate() },
						new LeafNode(LeafNode.EQ, null));
			}
			pendingLits.add(literal == eq ? laeq : laeq.negate());
		}
		if (literal == eq) {
			if (eq.getLhs().repStar != eq.getRhs().repStar) {
				eq.stackDepth = merges.size();
				Clause conflict = eq.getLhs().merge(this, eq.getRhs(), eq);
				if (conflict != null)
					return conflict;
			}
		} else {
			CCTerm left = eq.getLhs().repStar;
			CCTerm right = eq.getRhs().repStar;
			
			/* Check for conflict */
			if (left == right) {
				Clause conflict = computeCycle(eq);
				if (conflict != null)
					return conflict;
			}
			/* TODO get array extensionality working! */
			/*if (eq.isArray()) {
				// This is ext-diseq
				Info info = pairHash.getInfo(left, right);
				info.addExtensionalityDiseq(converter);
			}*/
			separate(left, right, eq);
			eq.stackDepth = merges.size();
		}
		return null;
	}

	private CCTermPairHash.Info lastInfo;
	private void separate(CCTerm lhs, CCTerm rhs, CCEquality atom) {
		if (lastInfo == null || !lastInfo.equals(lhs, rhs)) {
			lastInfo = pairHash.getInfo(lhs, rhs);
			assert lastInfo != null;
		}
		if (lastInfo.diseq != null)
			return;

		lastInfo.diseq = atom;
		/* Propagate inequalities */
		for (CCEquality.Entry eqentry : lastInfo.eqlits) {
			CCEquality eq = eqentry.getCCEquality();
			if (eq.getDecideStatus() == null) {
				eq.m_diseqReason = atom;
				addPending(eq.negate());
			}
		}
		/* reverse congruence closure
		for (CCTerm t1 : members) {
			if (t1 instanceof CCAppTerm) {
				CCAppTerm app1 = (CCAppTerm) t1;
				for (CCTerm t2 : members) {
					if (t2 instanceof CCAppTerm) {
						CCAppTerm app2 = (CCAppTerm) t2;
						if (app1.func.rep == app2.func.rep
							&& !app1.arg.rep.inDiseq(app2.arg.rep.diseq)) {
							separate(app1.arg.rep, app2.arg.rep, atom);
						} else if (app1.arg.rep == app2.arg.rep
								   && !app1.func.rep.inDiseq(app2.func.rep.diseq)) {
							separate(app1.func.rep, app2.func.rep, atom);
						}
					}
				}
			}
		} */
	}
	
	private void undoSep(CCEquality atom) {
		atom.m_diseqReason = null;
		CCTermPairHash.Info destInfo = pairHash.getInfo(atom.getLhs().repStar, atom.getRhs().repStar);
		if (destInfo != null && destInfo.diseq != null) {
			destInfo = pairHash.getInfo(atom.getLhs().repStar, atom.getRhs().repStar);
		    if (destInfo.diseq == atom)
		    	destInfo.diseq = null;
		}
	}	

	public Clause computeCycle(CCEquality eq) {
		CongruencePath congPath = 
			new CongruencePath(this);
		Clause res = congPath.computeCycle(eq, engine.isProofGenerationEnabled());
		assert(res.getSize() != 2 || res.getLiteral(0).negate() != res.getLiteral(1));
		return res;
	}
	public Clause computeCycle(CCTerm lconstant,CCTerm rconstant) {
		CongruencePath congPath = 
			new CongruencePath(this);
		return congPath.computeCycle(lconstant,rconstant, engine.isProofGenerationEnabled());
	}
		
	public Clause computeAntiCycle(CCEquality eq) {
		CCTerm left = eq.getLhs();
		CCTerm right = eq.getRhs();
		CCEquality diseq = eq.m_diseqReason;
		assert left.repStar != right.repStar;
		assert diseq.getLhs().repStar == left.repStar
			|| diseq.getLhs().repStar == right.repStar;
		assert diseq.getRhs().repStar == left.repStar
			|| diseq.getRhs().repStar == right.repStar;

		left.invertEqualEdges();
		left.equalEdge = right;
		left.oldRep = left.repStar;
		assert left.oldRep.reasonLiteral == null;
		left.oldRep.reasonLiteral = eq;
		Clause c = computeCycle(diseq);
		assert left.equalEdge == right && left.oldRep == left.repStar;
		left.oldRep.reasonLiteral = null;
		left.oldRep = null;
		left.equalEdge = null;
		return c;
	}
	
	public void addPending(Literal eq) {
		assert(checkPending(eq));
		pendingLits.add(eq);
	}

	private boolean checkPending(Literal literal) {
		if (literal.negate() instanceof CCEquality) {
			CCEquality eq = (CCEquality) literal.negate();
			CCTerm left = eq.getLhs();
			CCTerm right = eq.getRhs();
			CCEquality diseq = eq.m_diseqReason;
			assert left.repStar != right.repStar;
			assert diseq.getLhs().repStar == left.repStar
				|| diseq.getLhs().repStar == right.repStar;
			assert diseq.getRhs().repStar == left.repStar
				|| diseq.getRhs().repStar == right.repStar;
			return true;
		}
		if (literal instanceof CCEquality) {
			CCEquality eq = (CCEquality)literal;
			return (eq.getLhs().repStar == eq.getRhs().repStar);
		}
		if (literal.getAtom() instanceof LAEquality) {
			LAEquality laeq = (LAEquality) literal.getAtom();
			for (CCEquality eq : laeq.getDependentEqualities()) {
				if (eq.getDecideStatus() != null
						&& eq.getDecideStatus().getSign() == literal.getSign())
					return true;
			}
		}
		return false;
	}

	public Clause checkpoint() {
		// TODO Move some functionality from setLiteral here.
		while (!pendingCongruences.isEmpty()/* || root.next != root*/) {
			Clause res = buildCongruence(true);
			if (res == null) {
				// First add array extensionality axioms (might lead to new pending insns)
//				ListSet<CCTerm>.ListSetIterator it1 = m_foreignarrays.listIterator();
//				while (it1.hasNext()) {
//					CCTerm array1 = it1.next();
//					ListSet<CCTerm>.ListSetIterator it2 = 
//						m_foreignarrays.successors(it1);
//					while (it2.hasNext()) {
//						CCTerm array2 = it2.next();
//						// Arrays are currently congruent
//						if (array1.repStar == array2.repStar) continue;
//						Info info = pairHash.getInfo(array1.repStar, array2.repStar);
//						if (info == null) {
//							info = new CCTermPairHash.Info(array1.repStar,array2.repStar);
//							pairHash.add(info);
//						}
//						info.addExtensionalityDiseq(converter);
//					}
//				}
//				// Do all trigger instructions
//				while (root.next != root) {
//					// Remove from front of the list list
//					TriggerExecutionContext tec = root.next;
//					root.next = tec.next;
//					root.next.prev = root;
//					// Re-execute
//					tec.reexecute(this);
//					// Clear in list status
//					tec.next = tec.prev = null;
//				}
			} else
				return res;
		}
		return null;
	}
	
	public Term convertTermToSMT(CCTerm t) {
		return t.toSMTTerm(engine.getSMTTheory());
	}

	public Term convertEqualityToSMT(CCTerm t1, CCTerm t2) {
		return engine.getSMTTheory().equals(convertTermToSMT(t1), 
				convertTermToSMT(t2));
	}
	

	public void dumpModel(Logger logger) {
//		assert(checkCongruence());
		logger.info("Equivalence Classes:");
		for (CCTerm t : allTerms) {
			if (t == t.repStar) {
				StringBuilder sb = new StringBuilder();
				String comma = "";
				for (CCTerm t2 : t.members) {
					sb.append(comma).append(t2);
					comma = "=";
				}
				logger.info(sb.toString());
			}
		}
	}

	@SuppressWarnings("unused")
	private boolean checkCongruence() {
		boolean skip;
		for (CCTerm t1 : allTerms) {
			skip = true;
			for (CCTerm t2 : allTerms) {
				if (skip) {
					if (t1 == t2)
						skip = false;
					continue;
				}
				if (t1 instanceof CCAppTerm && t2 instanceof CCAppTerm) {
					CCAppTerm a1 = (CCAppTerm)t1;
					CCAppTerm a2 = (CCAppTerm)t2;
					if (a1.func.repStar == a2.func.repStar &&
							a1.arg.repStar == a2.arg.repStar &&
							a1.repStar != a2.repStar) {
						System.err.println("Should be congruent: " + t1 + " and " + t2);
						return false;
					}
				}
			}
		}
		return true;
	}
	
	public void printStatistics(Logger logger) {
		logger.info("CCTimes: iE "+CCTerm.invertEdgeTime+" eq "+CCTerm.eqTime +
				" cc "+CCTerm.ccTime + " setRep "+CCTerm.setRepTime);
		logger.info("Merges: "+CCTerm.mergeCount+ ", cc:"+CCTerm.ccCount);
	}

	@Override
	public Literal getSuggestion() {
		// CClosure does not need to suggest anything so far!
		return null;
	}

	@Override
	public void decreasedDecideLevel(int currentDecideLevel) {}

	@Override
	public void increasedDecideLevel(int currentDecideLevel) {}

	@Override
	public Clause backtrackComplete() {
		pendingLits.clear();
		return buildCongruence(true);
	}

	@Override
	public void restart(int iteration) {}

	@Override
	public Clause startCheck() { return null; }
	
	@Override
	public void endCheck() {}
	
	void addPendingCongruence(CCAppTerm first,CCAppTerm second) {
		assert(first.leftParInfo.inList() && second.leftParInfo.inList());
		assert(first.rightParInfo.inList() && second.rightParInfo.inList());
		pendingCongruences.add(new CCAppTermPair(first,second));
	}
	
	void prependPendingCongruence(CCAppTerm first,CCAppTerm second) {
		assert(first.leftParInfo.inList() && second.leftParInfo.inList());
		assert(first.rightParInfo.inList() && second.rightParInfo.inList());
		pendingCongruences.addFirst(new CCAppTermPair(first,second));
	}
	
	private Clause buildCongruence(boolean checked) {
		CCAppTermPair cong;
		while ((cong = pendingCongruences.poll()) != null) {
			engine.getLogger().debug(new DebugMessage("PC {0}", cong));
			Clause res = null;
			// TODO Uncomment checked here
			if (/*!checked ||*/ 
					(cong.first.arg.repStar == cong.second.arg.repStar && 
						cong.first.func.repStar == cong.second.func.repStar)) {
				res = cong.first.merge(this,cong.second,null);
			} else
				assert checked : "Unchecked buildCongruence with non-holding congruence!";
			if (res != null) {
				return res;
			}
		}
		return null;
	}	

	private void backtrackStack(int todepth) {
		while (merges.size() > todepth) {
			CCTerm top = merges.pop();
			top.repStar.invertEqualEdges();
			boolean isCongruence = top.oldRep.reasonLiteral == null;
			CCTerm lhs = top;
			CCTerm rhs = top.equalEdge;
			top.undoMerge(this, top.equalEdge);
			if (isCongruence) {
				assert (rhs instanceof CCAppTerm);
				prependPendingCongruence((CCAppTerm)lhs, (CCAppTerm)rhs);
			}
		}
	}
	public void appendRC(TriggerExecutionContext.ReactivationContext rc) {
		rc.prevRC = lastRC;
		lastRC = rc;
	}
	
	void addPendingInsn(TriggerExecutionContext tec) {
		if (tec.next == null) {
			root.prev.next = tec;
			tec.prev = root.prev;
			root.prev = tec;
			tec.next = root;
		}
	}
	
	public void addForeignArray(CCTerm foreign) {
		m_foreignarrays.add(foreign);
	}
	
	public int getStackDepth() {
		return merges.size();
	}
	
	public TriggerExecutionContext getRoot() {
		return root;
	}

	public void yieldDone(TriggerExecutionContext tec) {
		if (doneYields == null) {
			doneYields = tec;
			tec.next = tec.prev = tec;
		} else {
			tec.next = doneYields;
			tec.prev = doneYields.prev;
			doneYields.prev.next = tec;
			doneYields.prev = tec;
		}
	}

	public void instantiation() {
		++curinsts;
	}

	@Override
	public void removeAtom(DPLLAtom atom) {
		if (atom instanceof CCEquality) {
			CCEquality cceq = (CCEquality) atom;
			removeCCEquality(cceq.getLhs(), cceq.getRhs(), cceq);
		}
	}
	private void removeCCEquality(CCTerm t1, CCTerm t2, CCEquality eq) {
		// TODO Need test for this!!!
		if (t1.mergeTime > t2.mergeTime) {
			CCTerm tmp = t1;
			t1 = t2;
			t2 = tmp;
		}
			
		if (t1.rep == t1) {
			assert t2.rep == t2;
			CCTermPairHash.Info info = pairHash.getInfo(t1, t2);
			if (info == null) {
				// We never created a pair hash for this...
				return;
			}
			info.eqlits.prepareRemove(eq.getEntry());
			eq.getEntry().removeFromList();
			if (info.isEmpty()) {
				pairHash.removePairInfo(info);
			}
		} else {
			boolean isLast = t1.rep == t2;
			boolean found = false;
			for (CCTermPairHash.Info.Entry pentry : t1.pairInfos) {
				CCTermPairHash.Info info = pentry.getInfo();
				if (pentry.other == t2) {
					info.eqlits.prepareRemove(eq.getEntry());
					found = true;
					break;
				}
			}
			assert(found);
			if (!isLast)
				removeCCEquality(t1.rep, t2, eq);
			else
				eq.getEntry().removeFromList();
		}
		if (eq.getLASharedData() != null)
			eq.getLASharedData().removeDependentAtom(eq);
	}

	private void removeTerm(CCTerm t) {
		assert (t.repStar == t);
		assert (pendingCongruences.isEmpty());
		for (Entry e : t.pairInfos)
			pairHash.removePairInfo(e.getInfo());
		if (t.sharedTerm != null)
			t.sharedTerm = null;
	}
	
	@Override
	public void pop(Object object, int targetlevel) {
		StackData sd = (StackData) object;
		for (int i = allTerms.size() - 1; i >= sd.allTermsSize; --i) {
			CCTerm t = allTerms.get(i);
			removeTerm(t);
			allTerms.remove(i);
		}
		numFunctionPositions = sd.numFuncPositions;
		m_foreignarrays.endScope();
		symbolicTerms.endScope();
	}

	@Override
	public Object push() {
		m_foreignarrays.beginScope();
		symbolicTerms.beginScope();
		return new StackData(this);
	}

	@Override
	public Object[] getStatistics() {
		return new Object[]{
				":CC", new Object[][]{
						{"Merges", CCTerm.mergeCount},
						{"Closure", CCTerm.ccCount},
						{"Times", new Object[][]{
								{"Invert", CCTerm.invertEdgeTime},
								{"Eq", CCTerm.eqTime},
								{"Closure", CCTerm.ccTime},
								{"SetRep", CCTerm.setRepTime}}
						}
				}};
	}

	@Override
	public void fillInModel(Model model, Theory t, SharedTermEvaluator ste) {
		CCTerm trueNode = null, falseNode = null;
		if (!allTerms.isEmpty()) {
			CCTerm t0 = allTerms.get(0);
			SharedTerm shared0 = t0.getFlatTerm();
			if (shared0.getTerm() == t.TRUE) {
				trueNode = t0;
				falseNode = allTerms.get(1);
			} else if (shared0.getTerm() == t.FALSE) {
				falseNode = t0;
				trueNode = allTerms.get(1);
			}
		}
		new ModelBuilder(allTerms, model, t, ste, trueNode, falseNode);
	}
	
}
