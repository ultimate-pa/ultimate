package local.stalin.smt.theory.cclosure;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;
import java.util.HashMap;
import java.util.Map;
import java.util.LinkedList;
import java.util.List;

import local.stalin.logic.Atom;
import local.stalin.logic.Formula;
import local.stalin.logic.FormulaVariable;
import local.stalin.logic.Term;
import local.stalin.logic.TermVariable;
import local.stalin.smt.dpll.Clause;
import local.stalin.smt.dpll.DPLLAtom;
import local.stalin.smt.dpll.InterpolationInfo;
import local.stalin.smt.dpll.Interpolator;
import local.stalin.smt.dpll.Literal;

public class CongruencePath {

	CClosure closure;
	
	Map<SymmetricPair<CCTerm>, List<InterfaceTerms>> visited;
	Set<Literal> path;
	Set<Formula>[] interpolant;

	/**
	 * This class represents the information needed for interpolation of a chain
	 * of equalities.  The information is stored in arrays, with one entry for each
	 * interpolant.
	 * 
	 * For a chain of equalities t1 = t2 = t3 = ... = tn, we compute the following information:
	 * <dl>
	 * <dt>headNr</dt>
	 * <dd>the lastFormulaNumber of the equality "t1 = t2".</dd>
	 * <dt>maxNr</dt>
	 * <dd>the maximum lastFormulaNumber of all literals t1...tn the chain.</dd>
	 * <dt>tailNr</dt>
	 * <dd>the lastFormulaNumber of the equality "t{n-1} = tn".</dd>
	 * <dt>headIface</dt>
	 * <dd>for cutnr c with headNr <= c < maxnr, this contains the ti that ends the 
	 *     first partial A-chain for this cut.</dd>
	 * <dt>headPre</dt>
	 * <dd>the equalities that are needed from B to prove with A that t1 = headIface.
	 *     If cutnr >= maxnr then this is null.</dd>
	 * <dt>tailIface</dt>
	 * <dd>for cutnr c with tailNr <= c < maxnr, this contains the ti that starts the 
	 *     last partial A-chain for this cut.</dd>
	 * <dt>tailPre</dt>
	 * <dd>the equalities that are needed from B to prove with A that tailIface = tn.
	 *     If cutnr >= maxnr then these are needed to prove with A that t1 = tn.</dd>
	 * </dl> 
	 * 
	 * Note that for cuts c with c >= maxnr, all literals are in A 
	 * (or more exactly not in B), therefore the partial A-chain stretches completely 
	 * over the equality chain.  For cuts c with c < tailNr,
	 * all literals from the literal corresponding to maxnr belong to B, so there is no 
	 * partial A-chain at the end.  Likewise for c < headNr, there is no partial A-chain
	 * at the beginning.
	 * 
	 * @author hoenicke
	 *
	 */
	class InterfaceTerms {
		/**
		 * The last formula number of the first equality in the chain.
		 */
		int headNr;
		/**
		 * The largest formula number such that a literal from this formula appeared in
		 * the chain.
		 */
		int maxNr;
		/**
		 * The last formula number of the last equality in the chain.
		 */
		int tailNr;
		/**
		 * Contains the end of the first chain for formulas from headNr to maxNr-1.
		 */
		CCTerm[] headIface;
		/**
		 * The equalities needed from B to prove with A that headIface equals the 
		 * first term in the chain.
		 */
		Set<Formula>[] headPre;
		
		/**
		 * Contains the start of the last chain for formulas from tailNr to maxNr-1.
		 */
		CCTerm[] tailIface;
		/**
		 * The equalities needed from B to prove with A that tailIface resp the first
		 * term in the chain equals the last term in the chain.
		 */
		Set<Formula>[] tailPre;
		
		@SuppressWarnings("unchecked")
		public InterfaceTerms(int formNr) {
			headIface = new CCTerm[interpolant.length];
			tailIface = new CCTerm[interpolant.length];
			headPre = new Set[interpolant.length];
			tailPre = new Set[interpolant.length];
			headNr = maxNr = tailNr = formNr;
		}
		
		public void setEndOfChain(int formNr, CCTerm t) {
			if (formNr >= maxNr) {
				/* This chain was never opened.  Set firstIface in interpolation info */
				headIface[formNr] = t;
				headPre[formNr] = tailPre[formNr];
				tailPre[formNr] = null;
				maxNr = formNr+1;
			} else {
				/* Close chain from lastIface to this term */
				Formula eq = closure.convertEqualityToSMT(tailIface[formNr], t); 
				interpolant[formNr].add(addPrecondition(tailPre[formNr], eq));
				tailPre[formNr] = null;
			}
		}

		public void mergePreconditions(Set<Formula>[] mergedPre) {
			for (int i = 0; i < mergedPre.length; i++) {
				if (mergedPre[i] != null) {
					if (tailPre[i] == null)
						tailPre[i] = new HashSet<Formula>();
					tailPre[i].addAll(mergedPre[i]);
				}
			}
		}

		/**
		 * Merge an interpolation info for a forward path (this) with an interpolation info of a 
		 * backward path (revInfo).    
		 * The interpolation info for the backward path must have been constructed by calling
		 * the constructor on the interpolation info for the forward path. 
		 * @param t  The term where the two paths meet.
		 * @param revIface The interpolation info of the backward path.
		 */
		public void mergeRevIface(CCTerm t, InterfaceTerms revIface) {
			/* Now go down in both paths to minimum of tailNr and revInfo.tailNr. */
			int formNr = tailNr;
			while (formNr > revIface.tailNr) {
				tailIface[--formNr] = t;
			}
			while (revIface.tailNr > formNr) {
				revIface.tailIface[--revIface.tailNr] = t;
			}
			/* Merge the tailPre of reverse path into this path */
			mergePreconditions(revIface.tailPre);
			
			/* Now the lastNr's are equal; we can merge the reverse info by closing the chains
			 * from info to revInfo.
			 */
			while (formNr < revIface.maxNr) {
				setEndOfChain(formNr, revIface.tailIface[formNr]);
				formNr++;
			}
			while (formNr > revIface.headNr) {
				formNr--;
				tailIface[formNr] = revIface.headIface[formNr];
				tailPre[formNr] = revIface.headPre[formNr];
			}
			tailNr = formNr;
		}
		
		public String toString() {
			StringBuilder sb = new StringBuilder();
			sb.append("InterfaceTerms[");
			if (headNr >= 0) {
				String comma = "";
				sb.append("first[");
				for (int i = headNr; i < maxNr; i++) {
					sb.append(comma).append(headIface[i]);
					comma = ",";
				}
				sb.append("],");
			}
			if (tailNr >= 0) {
				String comma = "";
				sb.append("last[");
				for (int i = tailNr; i < maxNr; i++) {
					sb.append(comma).append(tailIface[i]);
					comma=",";
				}
				sb.append("],");
			}
			sb.append(headNr).append(",").append(tailNr).append("]");
			return sb.toString();
		}
	}

	@SuppressWarnings("unchecked")
	public CongruencePath(CClosure closure, int length) {
		this.closure = closure;
		visited = new HashMap<SymmetricPair<CCTerm>,List<InterfaceTerms>>();
		path = new HashSet<Literal>();
		interpolant = new Set[length];
		for (int i = 0; i < length; i++) {
			interpolant[i] = new HashSet<Formula>();
		}
	}
	
	public Formula addPrecondition(Set<Formula> pre, Formula f) {
		if (pre != null) {
			Formula preform = Atom.TRUE;
			for (Formula preeq : pre)
				preform = closure.engine.andFormula(preform, preeq);
			return closure.engine.implFormula(preform, f);
		}
		return f;
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
	private void computeCCPath(InterfaceTerms info, int tailNr,
			CCAppTerm start, CCAppTerm end) {
		
		int formNr = info.tailNr;

		/* Compute path and interpolation info for func and arg */
		InterfaceTerms funcInfo = computePath(formNr, tailNr, start.func, end.func);
		InterfaceTerms argInfo = computePath(formNr, tailNr, start.arg, end.arg);
		
		assert (funcInfo.headNr == formNr);
		assert (argInfo.headNr == formNr);
		assert (funcInfo.tailNr == tailNr);
		assert (argInfo.tailNr == tailNr);
		
		
		/* Merge the head preconditions from func and arg */
		info.mergePreconditions(funcInfo.headPre);
		info.mergePreconditions(argInfo.headPre);

		/* Now move from formNr to smallest max. */
		while (formNr < funcInfo.maxNr && formNr < argInfo.maxNr) {
			CCTerm func = funcInfo.headIface[formNr];
			CCTerm arg = argInfo.headIface[formNr];
			info.setEndOfChain(formNr, new CCAppTerm(func, arg));
			formNr++;
		}
		/* Now move from largest max to smallest max by adding preconditions */
		while (formNr < funcInfo.maxNr) {
			funcInfo.maxNr--;
			Formula pre =
				closure.convertEqualityToSMT(funcInfo.headIface[funcInfo.maxNr], 
						funcInfo.tailIface[funcInfo.maxNr]);
			if (info.tailPre[funcInfo.maxNr] == null)
				info.tailPre[funcInfo.maxNr] = new HashSet<Formula>();
			info.tailPre[funcInfo.maxNr].add(pre);
		}
		while (formNr < argInfo.maxNr) {
			argInfo.maxNr--;
			Formula pre = 
				closure.convertEqualityToSMT(argInfo.headIface[argInfo.maxNr], 
						argInfo.tailIface[argInfo.maxNr]);
			if (info.tailPre[argInfo.maxNr] == null)
				info.tailPre[argInfo.maxNr] = new HashSet<Formula>();
			info.tailPre[argInfo.maxNr].add(pre);
		}

		/* Now move from smallest max back to tailNr */
		while (formNr > tailNr) {
			formNr--;
			CCTerm func = funcInfo.tailIface[formNr];
			CCTerm arg = argInfo.tailIface[formNr];
			info.tailIface[formNr] = new CCAppTerm(func, arg);
		}
		info.tailNr = formNr;

		/* Merge the tail preconditions from func and arg */
		info.mergePreconditions(funcInfo.tailPre);
		info.mergePreconditions(argInfo.tailPre);
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
	private void computePathTo(InterfaceTerms info, CCTerm t, CCTerm end) {
		CCTerm startCongruence = t;
		int formNr = info.tailNr;
		while (t != end) {
			if (t.oldRep.reasonLiteral != null) {
				EqualityAtom edge = t.oldRep.reasonLiteral; 
				int nextNr = edge.getLastFormulaNr();
				if (edge.isMixed()) {
					if (edge.getRhs() == t)
						nextNr = edge.getFirstFormulaNr();
				}
				if (startCongruence != t) {
					/* We have a congruence:  The terms startCongruence and t are congruent.
					 * Compute the paths for the func and arg parts and merge into the 
					 * interpolation info.
					 */
					info.tailNr = formNr;
					computeCCPath(info, nextNr, 
							(CCAppTerm) startCongruence, (CCAppTerm) t);
					formNr = info.tailNr;
				}
				/* Add the equality literal to conflict set */
				path.add(t.oldRep.reasonLiteral);
				if (formNr == -1)
					formNr = info.headNr = info.maxNr = nextNr;
				if (nextNr < formNr) {
					/* for cuts with firstNr <= cut < formNr:
					 *   A chains start at this node. */
					while (formNr > nextNr) {
						info.tailIface[--formNr] = t;
					}
				} else {
					/* for cuts with formNr <= cut < nextNr:
					 *   A chain end at this node. */
					while (formNr < nextNr) {
						info.setEndOfChain(formNr, t);
						formNr++;
					}
				}
				if (edge.isMixed()) {
					/* Handle mixed literals, by ending/starting the chains with the mixed term variable */
					CCTerm mixedTerm = edge.getMixedInterpolationTerm();
					if (edge.getRhs() == t) {
						/* This term is B, the next is A. */
						nextNr = edge.getLastFormulaNr();
						while (formNr > nextNr) {
							info.tailIface[--formNr] = mixedTerm;
						}
					} else {
						/* This term is A, the next is B. */
						nextNr = edge.getFirstFormulaNr();
						while (formNr < nextNr) {
							info.setEndOfChain(formNr, mixedTerm);
							formNr++;
						}
					}
				}
				startCongruence = t.equalEdge;
			}
			t = t.equalEdge;
		}
		assert (startCongruence == t);
		info.tailNr = formNr;
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
	public InterfaceTerms computePath(int headNr, int tailNr,
			CCTerm left, CCTerm right) {
		
		SymmetricPair<CCTerm> key = new SymmetricPair<CCTerm>(left, right);
		List<InterfaceTerms> cachedInfos = visited.get(key);
		if (cachedInfos == null) {
			cachedInfos = new LinkedList<InterfaceTerms>();
			visited.put(key, cachedInfos);
		}
		for (InterfaceTerms oldInfo : cachedInfos) {
			if (oldInfo.headNr == headNr && oldInfo.tailNr == tailNr)
				return oldInfo;
		}

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
		InterfaceTerms info = new InterfaceTerms(headNr);
		InterfaceTerms revInfo = new InterfaceTerms(tailNr);
		computePathTo(info, left, llWithReason);
		computePathTo(revInfo, right, rrWithReason);
		if (llWithReason != rrWithReason)
			computeCCPath(info, revInfo.tailNr,
					(CCAppTerm)llWithReason, (CCAppTerm)rrWithReason);
		info.mergeRevIface(rrWithReason, revInfo);
		assert (info.tailNr == tailNr);
		cachedInfos.add(info);
		return info;
	}
	
	private Formula convertInterpolant(Set<Formula> interpolants) {
		Formula ip = Atom.TRUE;
		for (Formula f: interpolants)
			ip = closure.engine.andFormula(ip, f);
		return ip; 
	}
	
	public Clause computeCycle(EqualityAtom eq) {
		int eqNr = eq.getLastFormulaNr();
		int firstNr = eq.getFirstFormulaNr();
		if (firstNr <= eqNr)
			firstNr = eqNr;
		InterfaceTerms info = computePath(eqNr, firstNr, eq.getLhs(), eq.getRhs());
		assert (info.tailNr == firstNr);
		/* close the circle */
		info.mergePreconditions(info.headPre);
		
		InterpolationInfo[] interpolants = new InterpolationInfo[interpolant.length];
		int ipNr = 0;
		while (ipNr < eqNr) {
			interpolants[ipNr] = new InterpolationInfo(convertInterpolant(interpolant[ipNr]));
			ipNr++;
		}
		// Mixed literal
		if (eq.isMixed()) {
			FormulaVariable fvar = closure.engine.getSMTTheory().createFreshFormulaVariable("EQ");
			TermVariable mixedVar = eq.getMixedInterpolationTermVar();
			Formula placeHolder = closure.engine.getSMTTheory().atom(fvar);
			while (ipNr < firstNr) {
				Term sharedTerm = closure.convertTermToSMT(info.headIface[ipNr]);
				Interpolator iplator =
					new CCMixedLiteralInterpolator(closure.engine.getSMTTheory(), mixedVar, fvar, sharedTerm);
				Formula ip = addPrecondition(info.tailPre[ipNr], placeHolder);
				interpolant[ipNr].add(ip);
				interpolants[ipNr] = new InterpolationInfo(convertInterpolant(interpolant[ipNr]),
					Collections.singletonMap((DPLLAtom) eq, iplator));
				ipNr++;
			}
		}
		/* Now add the inequality chains */
		while (ipNr < info.maxNr) {
			Formula ip = closure.engine.getSMTTheory().not(
					closure.convertEqualityToSMT(info.tailIface[ipNr], 
							info.headIface[ipNr]));
			ip = addPrecondition(info.tailPre[ipNr], ip);
			interpolant[ipNr].add(ip);
			interpolants[ipNr] = new InterpolationInfo(convertInterpolant(interpolant[ipNr]));
			ipNr++;
		}
		/* The empty inequality chain is FALSE! */ 
		while (ipNr < interpolant.length) {
			interpolant[ipNr].add(addPrecondition(info.tailPre[ipNr], Atom.FALSE));
			interpolants[ipNr] = new InterpolationInfo(convertInterpolant(interpolant[ipNr]));
			ipNr++;
		}
		Literal[] cycle = new Literal[path.size() + 1];
		int i = 0;
		cycle[i++] = eq;
		for (Literal l: path)
			cycle[i++] = l.negate();
		return new Clause(cycle, interpolants);
	}
	
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("IpInfo[");
		String comma = "";
		for (int i = 0; i < interpolant.length; i++) {
			sb.append(comma).append(interpolant[i]);
			comma = " | ";
		}
		sb.append("]");
		return sb.toString();
	}
}
