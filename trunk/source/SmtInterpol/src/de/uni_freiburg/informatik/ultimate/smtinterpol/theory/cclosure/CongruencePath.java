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

	CClosure closure;
	
	public static class SubPath {
		ArrayList<CCTerm> termsOnPath;
		ArrayList<CCEquality> litsOnPath;
		
		public SubPath(CCTerm start) {
			termsOnPath = new ArrayList<CCTerm>();
			litsOnPath = new ArrayList<CCEquality>();
			termsOnPath.add(start);
		}

		public void storeInto(CCTerm[][] paths, CCEquality[][] lits, int i) {
			assert termsOnPath.size() == litsOnPath.size()+1;
			paths[i] = termsOnPath.toArray(new CCTerm[termsOnPath.size()]);
			lits[i] = litsOnPath.toArray(new CCEquality[litsOnPath.size()]);			
		}

		public void addEntry(CCTerm term, CCEquality reason) {
			termsOnPath.add(term);
			litsOnPath.add(reason);
		}

		public void addReverse(SubPath second) {
			assert second.termsOnPath.size() == second.litsOnPath.size()+1;
			assert second.termsOnPath.get(second.termsOnPath.size()-1)
				== termsOnPath.get(termsOnPath.size()-1);
			for (int i = second.litsOnPath.size()-1; i >= 0; i--) {
				termsOnPath.add(second.termsOnPath.get(i));
				litsOnPath.add(second.litsOnPath.get(i));
			}
		}
	}

	HashMap<SymmetricPair<CCTerm>,SubPath> visited;
	SubPath mainPath;
	Set<Literal> allLiterals;

	public CongruencePath(CClosure closure) {
		this.closure = closure;
		visited = new HashMap<SymmetricPair<CCTerm>, SubPath>();
		allLiterals = new HashSet<Literal>();
	}
	
	private CCAnnotation createAnnotation(CCEquality diseq) {
		CCTerm[][] paths = new CCTerm[visited.size()][];
		CCEquality[][] lits  = new CCEquality[visited.size()][];
		int i = 0;
		mainPath.storeInto(paths, lits, i++);
		for (SubPath subPath : visited.values()) {
			if (subPath != mainPath)
				subPath.storeInto(paths, lits, i++);
		}
		return new CCAnnotation(diseq, paths, lits);
	}
	
	private int computeDepth(CCTerm t) {
		int depth = 0;
		while (t.equalEdge != null) {
			t = t.equalEdge;
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
	 * @param visited a set of equality pairs that were already visited.  This is
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
			computePath(start.arg, end.arg);

			/* We do not have explicit edges between partial function
			 * applications.  Hence start.func and end.func must be equal 
			 * or congruent.
			 */
			if (start.func == end.func)
				break;
			
			start = (CCAppTerm) start.func;
			end = (CCAppTerm) end.func;
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
	 * @param visited a set of equality pairs that were already visited.  This is
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
			if (t.oldRep.reasonLiteral != null) {
				if (startCongruence != t) {
					/* We have a congruence:  The terms startCongruence and t are congruent.
					 * Compute the paths for the func and arg parts and merge into the 
					 * interpolation info.
					 */
					computeCCPath((CCAppTerm) startCongruence, (CCAppTerm) t);
					path.addEntry(t, null);
				}
				/* Add the equality literal to conflict set */
				path.addEntry(t.equalEdge, t.oldRep.reasonLiteral);
				allLiterals.add(t.oldRep.reasonLiteral);
				startCongruence = t.equalEdge;
			}
			t = t.equalEdge;
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
	 * @param visited a set of equality pairs that were already visited.  This is
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
		if (visited.containsKey(key))
			return visited.get(key);

		int leftDepth = computeDepth(left);
		int rightDepth = computeDepth(right);
		CCTerm ll = left;
		CCTerm rr = right;
		CCTerm llWithReason = ll, rrWithReason = rr;
		while (leftDepth > rightDepth) {
			if (ll.oldRep.reasonLiteral != null)
				llWithReason = ll.equalEdge;
			ll = ll.equalEdge;
			leftDepth--;
		}
		while (rightDepth > leftDepth) {
			if (rr.oldRep.reasonLiteral != null)
				rrWithReason = rr.equalEdge;
			rr = rr.equalEdge;
			rightDepth--;
		}
		while (ll != rr) {
			if (ll.oldRep.reasonLiteral != null)
				llWithReason = ll.equalEdge;
			if (rr.oldRep.reasonLiteral != null)
				rrWithReason = rr.equalEdge;
			ll = ll.equalEdge;
			rr = rr.equalEdge;
		}
		assert (ll != null);
		SubPath path = computePathTo(left, llWithReason);
		if (llWithReason != rrWithReason) {
			computeCCPath((CCAppTerm)llWithReason, (CCAppTerm)rrWithReason);
			path.addEntry(rrWithReason, null);
		}
		path.addReverse(computePathTo(right, rrWithReason));
		visited.put(key, path);
		return path;
	}
	
	public Clause computeCycle(CCEquality eq, boolean produceProofs) {
		mainPath = computePath(eq.getLhs(), eq.getRhs());
		Literal[] cycle = new Literal[allLiterals.size() + 1];
		int i = 0;
		cycle[i++] = eq;
		for (Literal l: allLiterals)
			cycle[i++] = l.negate();
		Clause c = new Clause(cycle);
		if (produceProofs)
			c.setProof(new LeafNode(LeafNode.THEORY_CC, createAnnotation(eq)));
		return c;
	}
	
	public Clause computeCycle(CCTerm lconstant, CCTerm rconstant, boolean produceProofs) {
		closure.engine.getLogger().debug("computeCycle for Constants");
		mainPath = computePath(lconstant, rconstant);
		Literal[] cycle = new Literal[allLiterals.size()];
		int i = 0;
		for (Literal l: allLiterals)
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
		sb.append(allLiterals.toString());
		sb.append("]");
		return sb.toString();
	}

}
