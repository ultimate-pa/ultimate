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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.LeafNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.SymmetricPair;


public class CongruencePath {

	final CClosure mClosure;
	
	public static class SubPath {
		ArrayList<CCTerm> mTermsOnPath;
		ArrayList<CCEquality> mLitsOnPath;
		
		public SubPath(CCTerm start) {
			mTermsOnPath = new ArrayList<CCTerm>();
			mLitsOnPath = new ArrayList<CCEquality>();
			mTermsOnPath.add(start);
		}

		public void storeInto(CCTerm[][] paths, CCEquality[][] lits, int i) {
			assert mTermsOnPath.size() == mLitsOnPath.size() + 1;
			paths[i] = mTermsOnPath.toArray(new CCTerm[mTermsOnPath.size()]);
			lits[i] = mLitsOnPath.toArray(new CCEquality[mLitsOnPath.size()]);			
		}

		public void addEntry(CCTerm term, CCEquality reason) {
			mTermsOnPath.add(term);
			mLitsOnPath.add(reason);
		}

		public void addReverse(SubPath second) {
			assert second.mTermsOnPath.size() == second.mLitsOnPath.size() + 1;
			assert second.mTermsOnPath.get(second.mTermsOnPath.size() - 1)
				== mTermsOnPath.get(mTermsOnPath.size() - 1);
			for (int i = second.mLitsOnPath.size() - 1; i >= 0; i--) {
				mTermsOnPath.add(second.mTermsOnPath.get(i));
				mLitsOnPath.add(second.mLitsOnPath.get(i));
			}
		}
	}

	final HashMap<SymmetricPair<CCTerm>,SubPath> mVisited;
	SubPath mMainPath;
	final Set<Literal> mAllLiterals;

	public CongruencePath(CClosure closure) {
		this.mClosure = closure;
		mVisited = new HashMap<SymmetricPair<CCTerm>, SubPath>();
		mAllLiterals = new HashSet<Literal>();
	}
	
	private CCAnnotation createAnnotation(CCEquality diseq) {
		CCTerm[][] paths = new CCTerm[mVisited.size()][];
		CCEquality[][] lits  = new CCEquality[mVisited.size()][];
		int i = 0;
		mMainPath.storeInto(paths, lits, i++);
		for (SubPath subPath : mVisited.values()) {
			if (subPath != mMainPath)
				subPath.storeInto(paths, lits, i++);
		}
		return new CCAnnotation(diseq, paths, lits);
	}
	
	private int computeDepth(CCTerm t) {
		int depth = 0;
		while (t.mEqualEdge != null) {
			t = t.mEqualEdge;
			depth++;
		}
		return depth;
	}
	
	/**
	 * Compute the conflict set and interpolation information for the 
	 * congruence path from start to end.  The terms must be congruent AppTerms, 
	 * i.e. their func and arg values are congruent. 
	 * 
	 * The interpolation info should contain the path preceding the congruence, 
	 * its tailNr should correspond to the last formula number of the equality edge
	 * pointing to start in the circle.  The parameter tailNr should correspond to
	 * the equality edge pointing to end in the circle.
	 * 
	 * @param mVisited a set of equality pairs that were already visited.  This is
	 * used to prevent double work.
	 * @param set  the set of literals in the conflict clause.
	 * @param info the interpolation info containing head/tail interfaces, and collecting
	 * the equality chains. 
	 * @param tailNr the last formula number of equality edge connecting end in the
	 *  congruence graph circle.
	 * @param start one of the function application terms.
	 * @param end the other function application term.
	 */
	private void computeCCPath(CCAppTerm start, CCAppTerm end) {
		while (true) {
			/* Compute path and interpolation info for func and arg */
			computePath(start.mArg, end.mArg);

			/* We do not have explicit edges between partial function
			 * applications.  Hence start.func and end.func must be equal 
			 * or congruent.
			 */
			if (start.mFunc == end.mFunc)
				break;
			
			start = (CCAppTerm) start.mFunc;
			end = (CCAppTerm) end.mFunc;
		}
	}
	
	/**
	 * Compute the conflict set and interpolation information for the 
	 * congruence path from term t to end.  The terms must be directly connected by the 
	 * equalEdge graph, i.e. end is reachable from t by repeatedly following the 
	 * equalEdge field.  The last equalEdge must be induced by a equality literal not a 
	 * congruence edge.
	 * 
	 * The interpolation info should be empty, its head/max/lastNr should correspond 
	 * to the last formula number of the edge preceding t in the circle.
	 * 
	 * @param mVisited a set of equality pairs that were already visited.  This is
	 * used to prevent double work.
	 * @param set  the set of literals in the conflict clause.
	 * @param info the interpolation info containing head/tail interfaces, and collecting
	 * the equality chains. 
	 * @param t the first term in the path.
	 * @param end the last term in the path.
	 */
	private SubPath computePathTo(CCTerm t, CCTerm end) {
		SubPath path = new SubPath(t);
		CCTerm startCongruence = t;
		while (t != end) {
			if (t.mOldRep.mReasonLiteral != null) {
				if (startCongruence != t) {
					/* We have a congruence:  The terms startCongruence and t are congruent.
					 * Compute the paths for the func and arg parts and merge into the 
					 * interpolation info.
					 */
					computeCCPath((CCAppTerm) startCongruence, (CCAppTerm) t);
					path.addEntry(t, null);
				}
				/* Add the equality literal to conflict set */
				path.addEntry(t.mEqualEdge, t.mOldRep.mReasonLiteral);
				mAllLiterals.add(t.mOldRep.mReasonLiteral);
				startCongruence = t.mEqualEdge;
			}
			t = t.mEqualEdge;
		}
		assert (startCongruence == t);
		return path;
	}
	
	/**
	 * Compute the conflict set and interpolation information for the 
	 * congruence path from term left to right.  The interpolation info should be
	 * empty and its head/max/tailNr should be equal to the (last) formula number of
	 * the equality that precedes left in the conflict circle.  The parameter tailNr
	 * should give the (last) formula number of the next equality after right.
	 * On return info.tailNr is equal to tailNr.
	 * 
	 * @param mVisited a set of equality pairs that were already visited.  This is
	 * used to prevent double work. 
	 * @param set  the set of literals in the conflict clause.
	 * @param info the interpolation info containing head/tail interfaces, and collecting
	 * the equality chains. 
	 * @param tailNr this gives the (last) formula number of the equality after right.
	 * @param left the left end of the congruence chain that should be evaluated.
	 * @param right the right end of the congruence chain that should be evaluated.
	 */
	public SubPath computePath(CCTerm left, CCTerm right) {
		/* check for and ignore trivial paths */
		if (left == right)
			return null;
		
		SymmetricPair<CCTerm> key = new SymmetricPair<CCTerm>(left, right);
		if (mVisited.containsKey(key))
			return mVisited.get(key);

		int leftDepth = computeDepth(left);
		int rightDepth = computeDepth(right);
		CCTerm ll = left;
		CCTerm rr = right;
		CCTerm llWithReason = ll, rrWithReason = rr;
		while (leftDepth > rightDepth) {
			if (ll.mOldRep.mReasonLiteral != null)
				llWithReason = ll.mEqualEdge;
			ll = ll.mEqualEdge;
			leftDepth--;
		}
		while (rightDepth > leftDepth) {
			if (rr.mOldRep.mReasonLiteral != null)
				rrWithReason = rr.mEqualEdge;
			rr = rr.mEqualEdge;
			rightDepth--;
		}
		while (ll != rr) {
			if (ll.mOldRep.mReasonLiteral != null)
				llWithReason = ll.mEqualEdge;
			if (rr.mOldRep.mReasonLiteral != null)
				rrWithReason = rr.mEqualEdge;
			ll = ll.mEqualEdge;
			rr = rr.mEqualEdge;
		}
		assert (ll != null);
		SubPath path = computePathTo(left, llWithReason);
		if (llWithReason != rrWithReason) {
			computeCCPath((CCAppTerm)llWithReason, (CCAppTerm)rrWithReason);
			path.addEntry(rrWithReason, null);
		}
		path.addReverse(computePathTo(right, rrWithReason));
		mVisited.put(key, path);
		return path;
	}
	
	public Clause computeCycle(CCEquality eq, boolean produceProofs) {
		mMainPath = computePath(eq.getLhs(), eq.getRhs());
		Literal[] cycle = new Literal[mAllLiterals.size() + 1];
		int i = 0;
		cycle[i++] = eq;
		for (Literal l: mAllLiterals)
			cycle[i++] = l.negate();
		Clause c = new Clause(cycle);
		if (produceProofs)
			c.setProof(new LeafNode(LeafNode.THEORY_CC, createAnnotation(eq)));
		return c;
	}
	
	public Clause computeCycle(CCTerm lconstant, CCTerm rconstant, boolean produceProofs) {
		mClosure.mEngine.getLogger().debug("computeCycle for Constants");
		mMainPath = computePath(lconstant, rconstant);
		Literal[] cycle = new Literal[mAllLiterals.size()];
		int i = 0;
		for (Literal l: mAllLiterals)
			cycle[i++] = l.negate();
		Clause c = new Clause(cycle);
		if (produceProofs)
			c.setProof(new LeafNode(
					LeafNode.THEORY_CC, createAnnotation(null)));
		return c;
	}
	
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("CongruencePath[");
		sb.append(mAllLiterals.toString());
		sb.append(']');
		return sb.toString();
	}

}
