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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar;

import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Queue;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.MutableRational;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.logic.util.DebugMessage;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.EqualityProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SharedTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ITheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.Model;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.SharedTermEvaluator;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.Value;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.LeafNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.ArrayMap;
import de.uni_freiburg.informatik.ultimate.util.ScopedArrayList;
import de.uni_freiburg.informatik.ultimate.util.ScopedHashMap;

/**
 * Class implementing a decision procedure for linear arithmetic over 
 * rationals and integers. An algorithm proposed by Dutertre and de Moura 
 * is used. It provides tableau simplification, theory propagation, conflict 
 * set generation and interpolation.
 * 
 * To build a tableau, we create slack variables for every linear combination
 * of non-basic variables. To be able to recognize recurring linear
 * combinations, we canonicalize every linear combination and remember them the
 * first time we see them. Canonicalization takes advantage of the ordering of
 * non-basic variables. We transform every linear combination to an equivalent
 * one where the greatest common divisor of the coefficient is equal to one 
 * and the coefficient of the first non-basic variable is positive.
 * 
 * Theory propagation comes in two flavors: bound propagation and bound
 * refinement propagation. 
 * 
 * With bound propagation, we propagate every bound <code>x <= c'</code> after
 * setting bound <code>x <= c</code> where <code>c<=c'</code>. Lower bounds are
 * handled the same way.
 * 
 * With bound refinement propagation, we propagate bounds from the column
 * (non-basic) variables to a row (basic) variable.  The bound for the row
 * variable is a simple linear combination of the bounds for the column
 * variables. For the derived bound we create a composite reason to remember 
 * the bound.  Then we can use this composite reason as a source for bound 
 * propagation and propagate all bounds that are weaker than the composite.
 * 
 * @author Juergen Christ, Jochen Hoenicke
 */
public class LinArSolve implements ITheory {
	private static class UnsimpData {
		LinVar var;
		Rational fac;
		public UnsimpData(LinVar v, Rational f) {
			var = v;
			fac = f;
		}
	}
	/** The DPLL engine. */
	DPLLEngine mengine;
	/** The list of all variables (basic and nonbasic, integer and reals). */
	ArrayList<LinVar> m_linvars;
	/** The list of all non-basic integer variables. */
	ArrayList<LinVar> m_intVars;
	/** The literals that will be propagated. */
	Queue<Literal> mproplist;
	/** The basic variables hashed by their linear combinations. */
	ScopedHashMap<Map<LinVar,Rational>,LinVar> mterms;
	/** List of all variables outside their bounds.
	 * I prefer a tree set here since it provides ordering, retrieval of the 
	 * first element, addition of elements and uniqueness of elements!
	 */
	TreeSet<LinVar> moob;
	/** Map of all variables removed by simplifying operations. Their chains are
	 * converted into maps to provide faster lookup.
	 */
	HashMap<LinVar,TreeMap<LinVar,Rational>> msimps;
	/// --- Statistics variables ---
	/** Pivot counter. */
	int numPivots;
	/** Pivot counter. */
	int numPivotsBland;
	/** Counter for switches to Bland's Rule. */
	int numSwitchToBland;
	/** Time needed for pivoting operations. */
	long pivotTime;
	/** Number of literals created due to composites. */
	int mCompositeCreateLit;
	/** Number of branches since the last cut. */
	private int m_BranchCtr;

	// Statistics
	int numCuts;
	int numBranches;
	long cutGenTime;
	ScopedArrayList<SharedTerm> m_sharedVars =
		new ScopedArrayList<SharedTerm>();
	
	/** The next suggested literals */
	ArrayDeque<Literal> m_suggestions;
	
	/** Backtracking support for Composite Reasons. */
//	private Map<LAReason,Set<CompositeReason>> m_compositeWatchers;
	private long m_propBoundTime;
	private long m_propBoundSetTime;
	private long m_backtrackPropTime;
	private ArrayDeque<LinVar> m_propBounds;
	private LinVar m_conflictVar;
	private Rational m_Eps;
	
	/** Are we in a check-sat? */
	private boolean m_InCheck = false;
	/**
	 * The number of the next variable when created.
	 */
	private int m_VarNum = 0;
	/**
	 * Basic initialization.
	 * @param engine DPLLEngine this theory is used in.
	 */
	public LinArSolve(DPLLEngine engine) {
		mengine = engine;
		m_linvars = new ArrayList<LinVar>();
		m_intVars = new ArrayList<LinVar>();
		m_propBounds = new ArrayDeque<LinVar>();
		mproplist = new ArrayDeque<Literal>();
		m_suggestions = new ArrayDeque<Literal>();
		mterms = new ScopedHashMap<Map<LinVar,Rational>,LinVar>();
		moob = new TreeSet<LinVar>();
		msimps = new HashMap<LinVar, TreeMap<LinVar,Rational>>();
		numPivots = 0;
		numSwitchToBland = 0;
		pivotTime = 0;
		mCompositeCreateLit = 0;
		numCuts = 0;
		numBranches = 0;
		cutGenTime = 0;
//		m_compositeWatchers = new HashMap<LAReason, Set<CompositeReason>>();
	}

	/// --- Assertion check routines ---
	private boolean checkClean() {
		if (Config.EXPENSIVE_ASSERTS) {
			/* check if there are unprocessed bounds */
			for (LinVar v : m_linvars) {
				if (!v.mbasic)
					continue;
				assert v.checkBrpCounters();
				assert (v.getUpperBound().lesseq(v.getUpperComposite()));
				assert (v.getLowerComposite().lesseq(v.getLowerBound()));
				assert (v.getLowerBound().meps == 0 
						|| v.getDiseq(v.getLowerBound().ma) == null);
				assert (v.getUpperBound().meps == 0 
						|| v.getDiseq(v.getUpperBound().ma) == null);
			}
		}
		return true;
	}

	@SuppressWarnings("unused")
	private boolean checkColumn(MatrixEntry mentry) {
		LinVar c = mentry.column;
		assert !c.mbasic;
		assert c.headEntry.column == c;
		assert c.headEntry.row == LinVar.dummylinvar;
		assert c.headEntry.nextInRow == null && c.headEntry.prevInRow == null;
		boolean seen = false;
		for (MatrixEntry entry = c.headEntry.nextInCol;
			entry != c.headEntry; entry = entry.nextInCol) {
			assert entry.nextInCol.prevInCol == entry; 
			assert entry.prevInCol.nextInCol == entry; 
			assert entry.column == c;
			if (mentry == entry)
				seen = true;
		}
		assert c.headEntry.nextInCol.prevInCol == c.headEntry; 
		assert c.headEntry.prevInCol.nextInCol == c.headEntry; 
		assert(seen);
		return true;
	}

	private boolean checkPostSimplify() {
		if( msimps == null )
			return true;
		for( LinVar b : m_linvars ) {
			if (b.mbasic) {
				for (MatrixEntry entry = b.headEntry.nextInRow;
					entry != b.headEntry; entry = entry.nextInRow) {
					LinVar nb = entry.column;
					assert !msimps.containsKey(nb) :
						("Variable " + b + (b.mbasic ? " [basic]" : " [nonbasic]") + " contains simplified variable!");
				}
			} else {
				for (MatrixEntry entry = b.headEntry.nextInCol;
					entry != b.headEntry; entry = entry.nextInCol) {
					LinVar nb = entry.row;
					assert !msimps.containsKey(nb) :
						("Variable " + b + (b.mbasic ? " [basic]" : " [nonbasic]") + " contains simplified variable!");
				}
			}
		}
		return true;
	}
	
	private boolean checkoobcontent() {
		for( LinVar v : m_linvars ) {
			assert !v.outOfBounds() || moob.contains(v) :
				"Variable " + v + " is out of bounds: "
				+ v.getLowerBound() + "<=" + v.m_curval + "<=" + v.getUpperBound();
		}
		return true;
	}

	/// --- Introduction of variables ---
	/**
	 * Add a new non-basic variable.
	 * @param name  Name of the variable
	 * @param isint Is the variable integer valued
	 * @param level The assertion stack level for this variable
	 * @return Newly created variable
	 */
	public LinVar addVar(SharedTerm name, boolean isint, int level) {
		if (mengine.getLogger().isDebugEnabled())
			mengine.getLogger().debug("Creating var " + name);
		LinVar var = new LinVar(name, isint, level, m_VarNum++);
		m_linvars.add(var);
		if (isint)
			m_intVars.add(var);
		return var;
	}

	/**
	 * Add a new basic variable that is defined as linear combination.
	 * @param factors the linear combination as a map from LinVar to its factor.
	 *        The map must be normalized, i.e. divided by its gcd.
	 * @return Newly created variable
	 */
	public LinVar generateLinVar(TreeMap<LinVar, Rational> factors, int level) {
		boolean isInt = true;
		if (factors.size() == 1) {
			Map.Entry<LinVar,Rational> me = factors.entrySet().iterator().next();
			assert(me.getValue().equals(Rational.ONE));
			LinVar var = me.getKey();
			ensureUnsimplified(var);
			return var;
		}
		LinVar var = mterms.get(factors);
		if (var == null) {
			// Linear combination not known yet
			LinVar[] vars = new LinVar[factors.size()];
			BigInteger[] coeffs = new BigInteger[factors.size()];
			int i = 0;
			TreeMap<LinVar,Rational> curcoeffs = new TreeMap<LinVar,Rational>();
			for (Map.Entry<LinVar, Rational> entry : factors.entrySet()) {
				vars[i] = entry.getKey();
				assert(entry.getValue().denominator().equals(BigInteger.ONE));
				coeffs[i] = entry.getValue().numerator();
				unsimplifyAndAdd(entry.getKey(), entry.getValue(), curcoeffs);
				isInt &= vars[i].misint;
				i++;
			}
			ArrayMap<LinVar, BigInteger> intSum = 
				new ArrayMap<LinVar, BigInteger>(vars, coeffs);
			var = new LinVar(new LinTerm(intSum), isInt, level, m_VarNum++);
			insertVar(var, curcoeffs);
			mterms.put(factors, var);
			m_linvars.add(var);
			assert(var.checkBrpCounters());
		}
		return var;
	}
	
	/**
	 * Generate a bound constraint for <code>at <(=) 0</code>.
	 * @param at     Affine input term (may be unit term c_i*x_i+c or 
	 * 				 sum_i c_i*x_i+c)
	 * @param strict   Strict bound (< instead of <=)
	 * @param level		Assertion stack level for the constraint.
	 * @param remember Should the variable remember the generated constraint?
	 * @return
	 */
	public Literal generateConstraint(MutableAffinTerm at,boolean strict,int level) {
		Rational normFactor = at.getGCD().inverse();
		at.mul(normFactor);
		LinVar var = generateLinVar(getSummandMap(at), level);
		return generateConstraint(var, at.m_constant.ma.negate(), normFactor.isNegative(), strict);
	}
	
	private final TreeMap<LinVar, Rational> getSummandMap(MutableAffinTerm at) {
		return at.getSummands();
	}

	
	/**
	 * Update values of all basic variables depending on some non-basic variable.
	 * @param updateVar the non-basic variable.
	 * @param newValue  Value to set for this variable.
	 */
	private void updateVariableValue(LinVar updateVar, InfinitNumber newValue) {
		assert(!updateVar.mbasic);
		InfinitNumber diff = newValue.sub(updateVar.m_curval);
		updateVar.m_curval = newValue;
		for (MatrixEntry entry = updateVar.headEntry.nextInCol;
			entry != updateVar.headEntry; entry = entry.nextInCol) {
			LinVar var = entry.row;
			assert(var.mbasic);
			Rational coeff = Rational.valueOf(entry.coeff, var.headEntry.coeff.negate());
			var.m_curval = var.m_curval.addmul(diff,coeff);
			assert(var.checkBrpCounters());
			assert !(var.m_curval.ma.denominator().equals(BigInteger.ZERO));
			if (var.outOfBounds())
				moob.add(var);
		}
	}

	/**
	 * Update bound of a non-basic variable and generate CompositeReasons for
	 * all its dependent basic variables.
	 * @param updateVar the non-basic variable.
	 * @param isUpper   whether upper or lower bound is assigned.
	 * @param oldBound  the previous bound.
	 * @param newBound  the new bound.
	 * @return Conflict clause detected during bound refinement propagations
	 */
	private Clause updateVariable(LinVar updateVar, boolean isUpper, 
			InfinitNumber oldBound, InfinitNumber newBound) {
		assert(!updateVar.mbasic);
		InfinitNumber diff = newBound.sub(updateVar.m_curval);
		if ((diff.signum() > 0) == isUpper)
			diff = InfinitNumber.ZERO;
		else
			updateVar.m_curval = newBound;
		
		assert !(updateVar.m_curval.ma.denominator().equals(BigInteger.ZERO));
		Clause conflict = null;
		for (MatrixEntry entry = updateVar.headEntry.nextInCol;
			entry != updateVar.headEntry; entry = entry.nextInCol) {
			LinVar var = entry.row;
			assert(var.mbasic);
			Rational coeff = Rational.valueOf(entry.coeff, var.headEntry.coeff.negate());
			if (diff != InfinitNumber.ZERO)
				var.m_curval = var.m_curval.addmul(diff,coeff);
			assert !(var.m_curval.ma.denominator().equals(BigInteger.ZERO));
			if (var.outOfBounds())
				moob.add(var);
			if (isUpper != entry.coeff.signum() < 0) {
				var.updateUpper(entry.coeff, oldBound, newBound);
				assert(var.checkBrpCounters());
				
				if (var.m_numUpperInf == 0) {
					if (conflict == null)
						conflict = propagateBound(var, true);
					else {
//						assert var.isAlive();
						m_propBounds.addLast(var);
					}
				}
			} else {
				var.updateLower(entry.coeff, oldBound, newBound);
				assert(var.checkBrpCounters());
				
				if (var.m_numLowerInf == 0) {
					if (conflict == null)
						conflict = propagateBound(var, false);
					else {
//						assert var.isAlive();
						m_propBounds.addLast(var);
					}
				}
			}
			assert(!var.mbasic || var.checkBrpCounters());
		}
		return conflict;
	}

	private void updatePropagationCountersOnBacktrack(LinVar var,
			InfinitNumber oldBound, InfinitNumber newBound,
			boolean upper) {
		for (MatrixEntry entry = var.headEntry.nextInCol;
			entry != var.headEntry; entry = entry.nextInCol) {
			if (upper != entry.coeff.signum() < 0) {
				entry.row.updateUpper(entry.coeff, oldBound, newBound);
			} else {
				entry.row.updateLower(entry.coeff, oldBound, newBound);
			}
			assert(entry.row.checkBrpCounters());
		}
	}
	
	public void removeReason(LAReason reason) {
		LinVar var = reason.getVar();
		if (var.mbasic && var.headEntry != null) {
//			assert var.isAlive();
			m_propBounds.add(var);
		}
		LAReason chain;
		if (reason.isUpper()) {
			if (var.m_upper == reason) {
				var.m_upper = reason.getOldReason();
				if (!var.mbasic) {
					updatePropagationCountersOnBacktrack(var, reason.getBound(), var.getUpperBound(), true);
					if (var.m_curval.less(var.getLowerBound()))
						updateVariableValue(var, var.getLowerBound());
				} else if (var.outOfBounds()) {
					moob.add(var);
				}
				return;
			}
			chain = var.m_upper;
		} else {
			if (var.m_lower == reason) {
				var.m_lower = reason.getOldReason();
				if (!var.mbasic) {
					updatePropagationCountersOnBacktrack(var, reason.getBound(), var.getLowerBound(), false);
					if (var.getUpperBound().less(var.m_curval))
						updateVariableValue(var, var.getUpperBound());
				} else if (var.outOfBounds()) {
					moob.add(var);
				}
				return;
			}
			chain = var.m_lower;
		}
		while (chain.getOldReason() != reason)
			chain = chain.getOldReason();
		chain.setOldReason(reason.getOldReason());
	}
	
	public void removeLiteralReason(LiteralReason reason) {
		for (LAReason depReason : reason.getDependents()) {
			removeReason(depReason);
		}
		removeReason(reason);
	}
	
	@Override
	public void backtrackLiteral(Literal literal) {
		DPLLAtom atom = literal.getAtom();
		LinVar var;
		InfinitNumber bound;
		if (atom instanceof LAEquality) {
			LAEquality laeq = (LAEquality) atom;
			var = laeq.getVar();
			bound = new InfinitNumber(laeq.getBound(), 0);
			if (laeq == literal.negate()) {
				// disequality: remove from diseq map
				var.removeDiseq(laeq);
			}
		} else if (atom instanceof BoundConstraint) {
			BoundConstraint bc = (BoundConstraint) atom;
			var = bc.getVar();
			bound = bc.getBound();
		} else
			return;

		LAReason reason = var.m_upper;
		while (reason != null && reason.getBound().lesseq(bound)) {
			if ((reason instanceof LiteralReason)
					&& ((LiteralReason)reason).getLiteral() == literal
					&& reason.getLastLiteral() == reason) {
				removeLiteralReason((LiteralReason)reason);
				break;
			}
			reason = reason.getOldReason();
		}
		reason = var.m_lower;
		while (reason != null && bound.lesseq(reason.getBound())) {
			if ((reason instanceof LiteralReason)
					&& ((LiteralReason)reason).getLiteral() == literal
					&& reason.getLastLiteral() == reason) {
				removeLiteralReason((LiteralReason)reason);
				break;
			}
			reason = reason.getOldReason();
		}
	}
	
	/* Check if there is still a pending conflict that must be reported.
	 * @Return the corresponding conflict clause or null, if no conflict pending.
	 */
	public Clause checkPendingConflict() {
		LinVar var = m_conflictVar;
		if (var != null && var.getUpperBound().less(var.getLowerBound())) {
			// we still have a conflict
			Explainer explainer = new Explainer(this, mengine.isProofGenerationEnabled(), null);
			InfinitNumber slack = var.getLowerBound().sub(var.getUpperBound());
			slack = var.m_upper.explain(explainer, slack, Rational.ONE);
			slack = var.m_lower.explain(explainer, slack, Rational.MONE);
			return explainer.createClause(mengine);
		}
		m_conflictVar = null;
		return null;
	}

	@Override
	public Clause backtrackComplete() {
		mproplist.clear();
		m_suggestions.clear();

		Clause conflict = checkPendingConflict();
		if (conflict != null)
			return conflict;
		
		/* check if there are unprocessed bounds */
		while (!m_propBounds.isEmpty()) {
			LinVar b = m_propBounds.removeFirst();
			if (b.dead || !b.mbasic)
				continue;
			assert(b.checkBrpCounters());
			long time;
			if (Config.PROFILE_TIME)
				time = System.nanoTime();
			if (b.m_numUpperInf == 0)
				conflict = propagateBound(b, true);
			if (b.m_numLowerInf == 0) {
				if (conflict == null)
					conflict = propagateBound(b, false);
				else {
//					assert b.isAlive();
					m_propBounds.addLast(b);
				}
			}
			if (Config.PROFILE_TIME)
				m_backtrackPropTime += System.nanoTime() - time;
			if (conflict != null)
				return conflict;
		}
		
		assert(checkClean());
		return fixOobs();
	}

	@Override
	public Clause computeConflictClause() {
		m_suggestions.clear();
		mengine.getLogger().debug("Final Check LA");
		Clause c = fixOobs();
		if (c != null)
			return c;

		c = ensureIntegrals();
		if (c != null || !m_suggestions.isEmpty() || !mproplist.isEmpty())
			return c;
		assert(moob.isEmpty());
		Map<ExactInfinitNumber, List<SharedTerm>> cong = mutate();
		assert (checkClean());
		mengine.getLogger().debug(new DebugMessage("cong: {0}", cong));
		for (LinVar v : m_linvars) {
			LAEquality ea = v.getDiseq(v.m_curval.ma);
			if (ea == null)
				continue;
			// if disequality equals bound, the bound should have 
			// already been refined.
			//assert !v.getUpperBound().equals(ea.getBound());
			//assert !v.getLowerBound().equals(ea.getBound());
			/*
			 * FIX: Since we only recompute the epsilons in ensureDisequality,
			 *      we might try to satisfy an already satisfied disequality. In
			 *      this case, we return null and have nothing to do.
			 */
			Literal lit = ensureDisequality(ea);
			if (lit != null) {
				assert lit.getAtom().getDecideStatus() == null;
				m_suggestions.add(lit);
				mengine.getLogger().debug(new DebugMessage(
					"Using {0} to ensure disequality {1}", lit,
					ea.negate()));
			}
		}
		if (m_suggestions.isEmpty() && mproplist.isEmpty())
			return mbtc(cong);
		assert(compositesSatisfied());
		return null;
	}

	private boolean compositesSatisfied() {
		for (LinVar v : m_linvars) {
			if (v.mbasic)
				v.fixEpsilon();
			assert(v.m_curval.lesseq(v.getUpperBound()));
			assert(v.getLowerBound().lesseq(v.m_curval));
		}
		return true;
	}

	@Override
	public Literal getPropagatedLiteral() {
		while( !mproplist.isEmpty() ) {
			Literal lit = mproplist.remove();
			if (lit.getAtom().getDecideStatus() == null) {
				return lit;
			}
		}
		return null;
	}
	
	private Clause createUnitClause(Literal literal, boolean isUpper,
			InfinitNumber bound, LinVar var) {
		Explainer explainer = new Explainer(this, mengine.isProofGenerationEnabled(), literal);
		if (isUpper) {
			assert(var.getUpperBound().less(bound));
			explainer.addLiteral(literal, Rational.MONE);
			LAReason reason = var.m_upper;
			// Find the first oldest reason that explains the bound
			while (reason.getOldReason() != null
					&& reason.getOldReason().getBound().less(bound))
				reason = reason.getOldReason();
			reason.explain(explainer, 
					bound.sub(reason.getBound()), 
					Rational.ONE);
		} else {
			assert bound.less(var.getLowerBound());
			explainer.addLiteral(literal, Rational.ONE);
			LAReason reason = var.m_lower;
			// Find the first oldest reason that explains the bound
			while (reason.getOldReason() != null
					&& bound.less(reason.getOldReason().getBound()))
				reason = reason.getOldReason();
			reason.explain(explainer, 
					reason.getBound().sub(bound), 
					Rational.MONE);
		}
		return explainer.createClause(mengine);
	}

	@Override
	public Clause getUnitClause(Literal literal) {
		DPLLAtom atom = literal.getAtom();
		if (atom instanceof LAEquality) {
			LAEquality laeq = (LAEquality)atom;
			LinVar var = laeq.getVar();
			if (literal == laeq) {
				InfinitNumber bound = new InfinitNumber(laeq.getBound(), 0);
				LAReason upperReason = var.m_upper;
				while (upperReason.getBound().less(bound))
					upperReason = upperReason.getOldReason();
				LAReason lowerReason = var.m_lower;
				while (bound.less(lowerReason.getBound()))
					lowerReason = lowerReason.getOldReason();
				assert upperReason.getBound().equals(bound) && 
						lowerReason.getBound().equals(bound) :
						"Bounds on variable do not match propagated equality bound";
				Explainer explainer = new Explainer(this, mengine.isProofGenerationEnabled(), literal);
				LiteralReason uppereq = new LiteralReason(var, var.getUpperBound().sub(var.getEpsilon()), 
					true, laeq.negate());
				uppereq.setOldReason(upperReason);
				lowerReason.explain(explainer, var.getEpsilon(), Rational.MONE);
				explainer.addEQAnnotation(uppereq, Rational.ONE);

				return explainer.createClause(mengine);
			} else  {
				InfinitNumber bound = new InfinitNumber(laeq.getBound(), 0);
				// Check if this was propagated due to an upper bound.
				// We also need to make sure that the upper bound does not
				// depend on the inequality literal.
				LAReason upper = var.m_upper;
				while (laeq.getStackPosition() >= 0
						&& upper != null 
						&& upper.getLastLiteral().getStackPosition() >= laeq.getStackPosition())
					upper = upper.getOldReason();
				return createUnitClause(literal, upper != null && upper.getBound().less(bound), bound, var);
			}
		} else if (atom instanceof CCEquality) {
			return generateEqualityClause(literal);
		} else {
			BoundConstraint bc = (BoundConstraint)atom;
			LinVar var = bc.getVar();
			boolean isUpper = literal.getSign() > 0;
			return createUnitClause(literal, isUpper,
					isUpper ? bc.getInverseBound() : bc.getBound(), var);
		}
	}
	
	private Clause generateEqualityClause(Literal cclit) {
		CCEquality cceq = (CCEquality) cclit.getAtom();
		Literal ea = cceq.getLASharedData();
		if (cceq == cclit)
			ea = ea.negate();
		return new Clause(new Literal[] { cclit, ea }, 
				new LeafNode(LeafNode.EQ, null));
	}

	/**
	 * Create a new LiteralReason for a newly created and back-propagated 
	 * literal and add the reason to the right position in the reason chain.
	 * 
	 * @param var The variable that got a new literal
	 * @param lit The newly created literal that was inserted as propagated literal.
	 */
	private void insertReasonOfNewComposite(LinVar var, Literal lit) {
		BoundConstraint bc = (BoundConstraint) lit.getAtom();
		boolean isUpper = lit == bc;
		
		if (isUpper) {
			InfinitNumber bound = bc.getBound();
			LiteralReason reason = new LiteralReason(var, bound, true, lit);
			// insert reason into the reason chain
			if (bound.less(var.getExactUpperBound())) {
				reason.setOldReason(var.m_upper);
				var.m_upper = reason;
			} else {
				LAReason thereason = var.m_upper;
				while (thereason.getOldReason().getExactBound().less(bound)) {
					thereason = thereason.getOldReason();
				}
				assert (thereason.getExactBound().less(bound) && 
						bound.less(thereason.getOldReason().getExactBound()));
				reason.setOldReason(thereason.getOldReason());
				thereason.setOldReason(reason);
			}
			if (var.mbasic && var.outOfBounds())
				moob.add(var);
		} else {
			InfinitNumber bound = bc.getInverseBound();
			LiteralReason reason = new LiteralReason(var, bound, false, lit);
			// insert reason into the reason chain
			if (var.getExactLowerBound().less(bound)) {
				reason.setOldReason(var.m_lower);
				var.m_lower = reason;
			} else {
				LAReason thereason = var.m_lower;
				while (bound.less(thereason.getOldReason().getExactBound())) {
					thereason = thereason.getOldReason();
				}
				assert (thereason.getOldReason().getExactBound().less(bound) && 
						bound.less(thereason.getExactBound()));
				reason.setOldReason(thereason.getOldReason());
				thereason.setOldReason(reason);
			}
			if (var.mbasic && var.outOfBounds())
				moob.add(var);
		}
	}
	
	private Clause setBound(LAReason reason) {
		LinVar var = reason.getVar();
		InfinitNumber bound = reason.getBound();
		InfinitNumber epsilon = var.getEpsilon();
		LiteralReason lastLiteral = reason.getLastLiteral();
		if (reason.isUpper()) {
			// check if bound is stronger
			InfinitNumber oldBound = var.getUpperBound();
			assert (reason.getExactBound().less(var.getExactUpperBound()));
			reason.setOldReason(var.m_upper);
			var.m_upper = reason;

			// Propagate Disequalities
			LAEquality ea;
			while (bound.meps == 0 && (ea = var.getDiseq(bound.ma)) != null) {
				bound = bound.sub(epsilon);				
				if (ea.getStackPosition() > lastLiteral.getStackPosition()) {
					lastLiteral = new LiteralReason(var, bound, 
							true, ea.negate());
					var.m_upper = lastLiteral;
				} else  {
					var.m_upper = new LiteralReason(var, bound, 
							true, ea.negate(), 
							lastLiteral);
					lastLiteral.addDependent(var.m_upper);
				}
				var.m_upper.setOldReason(reason);
				reason = var.m_upper;
			}
			
			if (!var.mbasic) {
				Clause conflict = updateVariable(var, true, oldBound, bound);
				if (conflict != null)
					return conflict;
			} else if (var.outOfBounds())
				moob.add(var);

			for (BoundConstraint bc : 
					var.mconstraints.subMap(bound, oldBound).values()) {
				assert var.getUpperBound().lesseq(bc.getBound());
				mproplist.add(bc);
			}
			for (LAEquality laeq : 
					var.mequalities.subMap(bound.add(var.getEpsilon()), 
							oldBound.add(var.getEpsilon())).values()) {
				mproplist.add(laeq.negate());
			}
		} else {
			// lower
			// check if bound is stronger
			InfinitNumber oldBound = var.getLowerBound();
			assert (var.getExactLowerBound().less(reason.getExactBound()));
			reason.setOldReason(var.m_lower);
			var.m_lower = reason;

			// Propagate Disequalities
			LAEquality ea;
			while (bound.meps == 0 && (ea = var.getDiseq(bound.ma)) != null) {
				bound = bound.add(epsilon);
				if (ea.getStackPosition() > lastLiteral.getStackPosition()) {
					lastLiteral = new LiteralReason(var, bound, 
							false, ea.negate());
					var.m_lower = lastLiteral;
				} else  {
					var.m_lower = new LiteralReason(var, bound, 
							false, ea.negate(), 
							lastLiteral);
					lastLiteral.addDependent(var.m_lower);
				}
				var.m_lower.setOldReason(reason);
				reason = var.m_lower;
			}
			
			if (!var.mbasic) {
				Clause conflict = updateVariable(var, false, oldBound, bound);
				if (conflict != null)
					return conflict;
			} else if (var.outOfBounds())
				moob.add(var);

			for (BoundConstraint bc : 
					var.mconstraints.subMap(oldBound, bound).values()) {
				assert bc.getInverseBound().lesseq(var.getLowerBound());
				mproplist.add(bc.negate());
			}			
			for (LAEquality laeq : 
					var.mequalities.subMap(oldBound, bound).values()) {
				mproplist.add(laeq.negate());
			}
		}
		InfinitNumber ubound = var.getUpperBound();
		InfinitNumber lbound = var.getLowerBound();
		if (lbound.equals(ubound)) {
			LAEquality lasd = var.mequalities.get(lbound);
			if (lasd != null && lasd.getDecideStatus() == null)
				mproplist.add(lasd);
		} else if (ubound.less(lbound)) {
			// we have a conflict
			m_conflictVar = var;
			return checkPendingConflict();
		}
		assert (var.mbasic || !var.outOfBounds());
		return null;
	}
	
	@Override
	public Clause setLiteral(Literal literal) {
		DPLLAtom atom = literal.getAtom();
		assert (checkClean());
		Clause conflict = null;
		if (atom instanceof LAEquality) {
			LAEquality lasd = (LAEquality) atom;
			/* Propagate dependent atoms */
			for (CCEquality eq : lasd.getDependentEqualities()) {
				if (eq.getDecideStatus() == null) {
					mproplist.add(literal == atom ? eq : eq.negate());
				} else if (eq.getDecideStatus().getSign() != literal.getSign()) {
					/* generate conflict */
					return generateEqualityClause(eq.getDecideStatus().negate());
				}
			}
			
			LinVar var = lasd.getVar();
			InfinitNumber bound = new InfinitNumber(lasd.getBound(), 0);
			if (literal.getSign() == 1) {
				// need to assert ea as upper and lower bound
				/* we need to take care of propagations:
				 * x = c ==> x <= c && x >= c should not propagate
				 * x <= c - k1 or x >= c + k2, but
				 * x <= c and x >= c
				 */
				if (mengine.getLogger().isDebugEnabled())
					mengine.getLogger().debug("Setting "+
							lasd.getVar()+" to "+lasd.getBound());
				if (bound.less(var.getUpperBound()))
					conflict = setBound(new LiteralReason(var, bound, 
							true, literal));
				if (conflict != null)
					return conflict;
				if (var.getLowerBound().less(bound))
					conflict = setBound(new LiteralReason(var, bound, 
							false, literal));
			} else {
				// Disequality constraint
				var.addDiseq(lasd);
				if (var.getUpperBound().equals(bound)) {
					conflict = setBound(new LiteralReason(var, 
							bound.sub(var.getEpsilon()), 
							true, literal));
				} else if (var.getLowerBound().equals(bound)) {
					conflict = setBound(new LiteralReason(var, 
							bound.add(var.getEpsilon()), 
							false, literal));
				}
			}
		} else if (atom instanceof BoundConstraint) {
			BoundConstraint bc = (BoundConstraint) atom;
			LinVar var = bc.getVar();
			// Check if the *exact* bound is refined and add this 
			// literal as reason.  This is even done, if we propagated the
			// literal.  If there is already a composite with the
			// same bound, we still may use it later to explain the literal,
			// see LiteralReason.explain.
			if (literal == bc) {
				if (bc.getBound().less(var.getExactUpperBound()))
					conflict = setBound(new LiteralReason(var, bc.getBound(), 
							true, literal));
			} else {
				if (var.getExactLowerBound().less(bc.getInverseBound()))
					conflict = setBound(new LiteralReason(var, bc.getInverseBound(), 
							false, literal));
			}
		}
		assert (conflict != null || checkClean());
		return conflict;
	}

	@Override
	public Clause checkpoint() {
		// Prevent pivoting before tableau simplification
		if (!m_InCheck)
			return null;
		return fixOobs();
	}

	public Rational realValue(LinVar var) {
		if (m_Eps == null)
			prepareModel();
		if (var.dead) {
			Rational val = Rational.ZERO;
			for (Entry<LinVar,Rational> chain : msimps.get(var).entrySet())
				val = val.add(realValue(chain.getKey()).mul(chain.getValue()));
			return val;
		} else {
			Rational cureps = var.computeEpsilon();
			return var.m_curval.ma.addmul(m_Eps, cureps);
		}
	}
	
	public void dumpTableaux(Logger logger) {
		for( LinVar var : m_linvars) {
			if (var.mbasic) {
				StringBuilder sb = new StringBuilder();
				sb.append(var).append(" ; ");
				for (MatrixEntry entry = var.headEntry.nextInRow;
			         entry != var.headEntry; entry = entry.nextInRow) {
					sb.append(" ; ").append(entry.coeff)
						.append("*").append(entry.column);
				}				
				logger.debug(sb.toString());
			}
		}
	}
	
	public void dumpConstraints(Logger logger) {
		for (LinVar var : m_linvars) {
			StringBuilder sb = new StringBuilder();
			sb.append(var).append(": ");
			InfinitNumber lower = var.getLowerBound();
			if (lower != InfinitNumber.NEGATIVE_INFINITY)
				sb.append("lower: ").append(var.getLowerBound()).append(" <= ");
			sb.append(var.m_curval);
			InfinitNumber upper = var.getUpperBound();
			if (upper != InfinitNumber.POSITIVE_INFINITY)
				sb.append(" <= ").append(upper).append(" : upper");
			logger.debug(sb);
		}
	}

	private void prepareModel() {
		/* Shortcut: If info log level is enabled we prepare the model to dump
		 * it as info message and later on when we have to produce a model.
		 * This work can be avoided.
		 */
		if (m_Eps != null)
			return;
//		HashSet<Rational> prohibitions = new HashSet<Rational>();
		TreeSet<Rational> prohibitions = new TreeSet<Rational>();
		InfinitNumber maxeps = computeMaxEpsilon(prohibitions);
		if (maxeps == InfinitNumber.POSITIVE_INFINITY)
			m_Eps = Rational.ONE;
		else
			m_Eps = maxeps.inverse().ceil().ma.inverse();
		// FIX: If we cannot choose the current value since we would violate a
		//      disequality, choose a different number.
//		while (prohibitions.contains(m_Eps))
//			m_Eps = m_Eps.div(Rational.TWO);
		if (prohibitions.contains(m_Eps)) {
			if (prohibitions.size() == 1)
				// No other chance
				m_Eps = m_Eps.div(Rational.TWO);
			else {
				Rational next = prohibitions.lower(m_Eps);
				if (next == null || next.signum() <= 0)
					m_Eps = m_Eps.div(Rational.TWO);
				else
					m_Eps = m_Eps.add(next).div(Rational.TWO);
			}
		}
	}
	
	@Override
	public void dumpModel(Logger logger) {
		prepareModel();
		logger.info("Assignments:");
		for( LinVar var : m_linvars) {
			if (!var.isInitiallyBasic())
				logger.info(var + " = " + realValue(var));
		}
		if( msimps != null ) {
			for (LinVar var : msimps.keySet())
				logger.info(var + " = " + realValue(var));
		}
	}

	@Override
	public void printStatistics(Logger logger) {
		logger.info("Number of Bland pivoting-Operations: "
				+ numPivotsBland + "/" + numPivots);
		logger.info("Number of switches to Bland's Rule: " + numSwitchToBland);
		logger.info("Number of variables: " + m_linvars.size());
		logger.info("Time for pivoting         : " + pivotTime/1000000);
		logger.info("Time for bound computation: " + m_propBoundTime/1000000);
		logger.info("Time for bound setting    : " + m_propBoundSetTime/1000000);
		logger.info("Time for bound comp(back) : " + m_backtrackPropTime/1000000);
		logger.info("No. of simplified variables: " + (msimps != null ? msimps.size() : 0));
		logger.info("Composite::createLit: " + mCompositeCreateLit);
		logger.info("Number of cuts: " + numCuts);
		logger.info("Time for cut-generation: " + cutGenTime/1000000);
		logger.info("Number of branchings: " + numBranches);
	}
	
	/**
	 * Pivot nonbasic versus basic variables along a coefficient.
	 * @param pivotEntry Coefficient specifying basic and nonbasic variable.
	 * @return Conflict clause detected during propagations
	 */
	private final Clause pivot(MatrixEntry pivotEntry) {
		if (mengine.getLogger().isDebugEnabled())
			mengine.getLogger().debug("pivot "+pivotEntry);
		Clause conflict = null;
		++numPivots;
		long starttime;
		if (Config.PROFILE_TIME)
			starttime = System.nanoTime();
		LinVar basic = pivotEntry.row;
		LinVar nonbasic = pivotEntry.column;
		assert(basic.checkChainlength());
		assert(nonbasic.checkChainlength());
		assert (basic.checkBrpCounters());
		assert(basic.mbasic);
		assert(!nonbasic.mbasic);
		basic.mbasic = false;
		nonbasic.mbasic = true;
		
		// Adjust brp numbers
		BigInteger nbcoeff = pivotEntry.coeff;
		BigInteger bcoeff = basic.headEntry.coeff;
		basic.updateUpperLowerClear(nbcoeff, nonbasic);
		nonbasic.moveBounds(basic);
		nonbasic.updateUpperLowerSet(bcoeff, basic);
		assert basic.checkCoeffChain();
		pivotEntry.pivot();
		basic.m_cachedRowVars = null;
		basic.m_cachedRowCoeffs = null;

		assert(nonbasic.checkChainlength());
		assert(basic.checkChainlength());
		assert (nonbasic.m_cachedRowCoeffs == null);
		assert nonbasic.checkCoeffChain();
		assert (nonbasic.checkBrpCounters());

		// Eliminate nonbasic from all equations
		MatrixEntry columnHead = nonbasic.headEntry;
		while (columnHead.nextInCol != columnHead) {
			LinVar row = columnHead.nextInCol.row;
			//assert row.checkCoeffChain();
			assert(row.checkBrpCounters());
			assert(row.checkChainlength());
			columnHead.nextInCol.add(columnHead);
			assert(row.checkChainlength());
			row.m_cachedRowVars = null;
			row.m_cachedRowCoeffs = null;
			assert row.checkCoeffChain();
			assert(row.checkBrpCounters());
			if (row.m_numUpperInf == 0) {
				if (conflict == null)
					conflict = propagateBound(row, true);
				else {
//					assert row.isAlive();
					m_propBounds.addLast(row);
				}
			}
			if (row.m_numLowerInf == 0) {
				if (conflict == null)
					conflict = propagateBound(row, false);
				else{
//					assert row.isAlive();
					m_propBounds.addLast(row);
				}
			}
		}
		
		assert nonbasic.checkChainlength();
		
		if (nonbasic.m_numUpperInf == 0) {
			if (conflict == null)
				conflict = propagateBound(nonbasic, true);
			else {
//				assert nonbasic.isAlive();
				m_propBounds.addLast(nonbasic);
			}
		}
		if (nonbasic.m_numLowerInf == 0) {
			if (conflict == null)
				conflict = propagateBound(nonbasic, false);
			else {
//				assert nonbasic.isAlive();
				m_propBounds.addLast(nonbasic);
			}
		}
		if (Config.PROFILE_TIME)
			pivotTime += System.nanoTime() - starttime;
//		mengine.getLogger().debug("Pivoting took " + (System.nanoTime() - starttime));
		return conflict;
	}
		
	/**
	 * Ensure that all integer variables have integral values. 
	 * @return Conflict clause or <code>null</code> if formula is satisfiable.
	 */
	private Clause ensureIntegrals() {
		boolean isIntegral = true;
		for (LinVar lv : m_intVars) {
			if (!lv.m_curval.isIntegral())
				isIntegral = false;
		}
		if (isIntegral)
			return null;

		Logger logger = mengine.getLogger();
		if (logger.isDebugEnabled())
			dumpTableaux(logger);

		// Satisfiable in the reals
		assert(moob.isEmpty());
		long start;
		if (Config.PROFILE_TIME)
			start = System.nanoTime();
		while (m_BranchCtr++<5) {
			LinVar best = null;
			for (LinVar lv : m_intVars) {
				if (lv.m_curval.isIntegral())
					continue;
				if (best == null)
					best = lv;
				else if (lv.getUpperBound().sub(lv.getLowerBound()).less
						(best.getUpperBound().sub(best.getLowerBound())))
					best = lv;
			}
			if (best == null)
				return null;
			if (best.m_curval.less(best.getLowerBound())
				|| best.getUpperBound().less(best.m_curval)) {
				moob.add(best);
				numCuts++;
			} else {
				Literal branch = generateConstraint(best, best.m_curval.floor(), false);
				m_suggestions.add(branch);
				numBranches++;
			}
			Clause c = fixOobs();
			if (c != null)
				return c;
		}
		m_BranchCtr=0;
		CutCreator cutter = new CutCreator(this);
		cutter.generateCuts();
		if (Config.PROFILE_TIME)
			cutGenTime += System.nanoTime() - start;
		Clause c = checkPendingConflict();
		if (c != null)
			return c;
		c = fixOobs();
		if (c != null)
			return c;
		return null;
	}
	
	/**
	 * Check whether all constraints can be satisfied. Here, we use the set of
	 * all variables outside their bounds. Rest of this algorithm is copied 
	 * from original paper.
	 * 
	 * If the formula is satisfiable, we additionally search for bound 
	 * refinement propagations and calculate the values of all variables
	 * simplified out.
	 * @return Conflict clause or <code>null</code> if formula is satisfiable.
	 */
	@SuppressWarnings("unused")
	private Clause fixOobs() {
//		
//		mengine.getLogger().debug("===Start Of Dump===");
//		dumpTableaux(mengine.getLogger());
//		dumpConstraints(mengine.getLogger());
//		System.exit(0);
//		
		// The number of pivoting operations with our own strategy
		final int switchtobland = Config.BLAND_USE_FACTOR * m_linvars.size();
		assert (checkClean());
		assert (!Config.EXPENSIVE_ASSERTS || checkoobcontent());
		int curnumpivots = 0;
		boolean useBland = false;
	poll_loop:
		while (!moob.isEmpty()) {
			LinVar oob = useBland ? moob.pollFirst() : findBestVar();
			if (oob == null)
				return null;
			assert(oob.mbasic);
			assert(oob.getLowerBound().lesseq(oob.getUpperBound()));
			assert(oob.checkBrpCounters());
			assert(oob.checkCoeffChain());
			InfinitNumber bound;
			InfinitNumber diff;
			BigInteger denom;
			boolean isLower;
			// BUGFIX: Use exact bounds here...
			oob.fixEpsilon();
			if (oob.m_curval.compareTo(oob.getExactLowerBound()) < 0) {
				bound = oob.getLowerBound();
				isLower = oob.headEntry.coeff.signum() < 0;
				diff = oob.m_curval.sub(bound).negate();
				denom = oob.headEntry.coeff;
			} else if (oob.m_curval.compareTo(oob.getExactUpperBound()) > 0) {
				bound = oob.getUpperBound();
				isLower = oob.headEntry.coeff.signum() > 0;
				diff = oob.m_curval.sub(bound);
				denom = oob.headEntry.coeff.negate();
			} else {
				/* no longer out of bounds */
				continue;
			}
			assert InfinitNumber.ZERO.less(diff);
			
			//TODO: This code looks ugly!
			MatrixEntry entry;
			if (useBland) {
				entry = oob.headEntry;
				/* Find the lowest element in the row chain */
				while (entry.column.matrixpos > entry.prevInRow.column.matrixpos)
					entry = entry.nextInRow;
			} else
				entry = findNonBasic(oob, isLower);
			MatrixEntry start = entry;
			/* Iterate elements in the row chain */
			do {
				assert (entry == oob.headEntry || !entry.column.mbasic);
				assert (entry == oob.headEntry || entry.column.m_curval.compareTo(entry.column.getUpperBound()) <= 0);
				assert (entry == oob.headEntry || entry.column.m_curval.compareTo(entry.column.getLowerBound()) >= 0);
				if (entry != oob.headEntry) {
					boolean checkLower = (entry.coeff.signum() < 0) == isLower;
					InfinitNumber colBound = checkLower 
						? entry.column.getLowerBound() 
						: entry.column.getUpperBound();
					InfinitNumber slack = entry.column.m_curval.sub(colBound);
					slack = slack.mul(Rational.valueOf(entry.coeff,denom));
					if (!useBland && slack.less(diff)) {
						if (slack.signum() > 0) {
							updateVariableValue(entry.column, colBound);
							// UpdateVariableValue will put us back into the
							// oob list.  So we remove us.
							moob.remove(oob);
							oob.fixEpsilon();
							/* JC: These assertions are not valid anymore.
							 * Changing the value of a non-basic variable might
							 * actually fix the problem with the basic variable.
							 * However, we still need to pivot once to prevent
							 * trivial non-termination.
							 * 
							 * Alternative: Don't change the value of this
							 * non-basic variable again, but this has some other
							 * side-effects (e.g. in the selection of a new
							 * pivot variable).
							 */
//							assert !oob.m_curval.equals(bound);
							diff = oob.m_curval.sub(bound);
							if (diff.signum() < 0)
								diff.negate();
//							assert diff.signum() != 0;
						}
					} else if (slack.signum() > 0) {
						assert(!moob.contains(oob));
						Clause conflict = pivot(entry);
						boolean oldBland = useBland;
						if (oldBland)
							++numPivotsBland;
						useBland = ++curnumpivots > switchtobland;
						if (useBland && ! oldBland) { 
							mengine.getLogger().debug("Using Blands Rule");
							numSwitchToBland++;
						}
						updateVariableValue(oob, bound);
						if (conflict != null)
							return conflict;
						continue poll_loop;
					}
				}
				entry = useBland ? entry.nextInRow : findNonBasic(oob, isLower);
			} while (!useBland || entry != start);
			assert(oob.checkBrpCounters());
			throw new AssertionError("Bound was not propagated????");
		} // end of queue polling
		assert (checkClean());
		assert (!Config.EXPENSIVE_ASSERTS || checkoobcontent());
		return null;
	}
	
	private Clause propagateBound(LinVar basic, boolean isUpper) {
		long start;
		if (Config.PROFILE_TIME)
			start = System.nanoTime();
		BigInteger denom = basic.headEntry.coeff.negate();
		isUpper ^= denom.signum() < 0;
		InfinitNumber bound = isUpper ? basic.getUpperComposite() 
				: basic.getLowerComposite();
		if (isUpper ? bound.less(basic.getUpperBound())
				    : basic.getLowerBound().less(bound)) {

			LAReason[] reasons;
			Rational[] coeffs;
			LiteralReason lastLiteral = null;
			if (basic.m_cachedRowCoeffs == null) {
				int rowLength = 0;
				for (MatrixEntry entry = basic.headEntry.nextInRow;
				     entry != basic.headEntry; entry = entry.nextInRow)
					rowLength++;
				
				LinVar[] rowVars = new LinVar[rowLength];
				reasons = new LAReason[rowLength];
				coeffs = new Rational[rowLength];
				int i = 0;
				for (MatrixEntry entry = basic.headEntry.nextInRow;
				 	 entry != basic.headEntry; entry = entry.nextInRow) {
					LinVar nb = entry.column;
					Rational coeff = Rational.valueOf(entry.coeff, denom);
					rowVars[i] = nb;
					reasons[i] = coeff.isNegative() != isUpper ? nb.m_upper : nb.m_lower;
					coeffs[i] = coeff;
					LiteralReason lastOfThis = reasons[i].getLastLiteral();
					if (lastLiteral == null 
						|| lastOfThis.getStackPosition() > lastLiteral.getStackPosition()) {
						lastLiteral = lastOfThis;
					}
					i++;
				}
				basic.m_cachedRowCoeffs = coeffs;
				basic.m_cachedRowVars = rowVars;
			} else {
				LinVar[] rowVars = basic.m_cachedRowVars;
				coeffs = basic.m_cachedRowCoeffs;
				reasons = new LAReason[rowVars.length];
				for (int i = 0; i < rowVars.length; i++) {
					reasons[i] = coeffs[i].isNegative() != isUpper 
						? rowVars[i].m_upper : rowVars[i].m_lower;
					LiteralReason lastOfThis = reasons[i].getLastLiteral();
					if (lastLiteral == null 
						|| lastOfThis.getStackPosition() > lastLiteral.getStackPosition()) {
						lastLiteral = lastOfThis;
					}
				}
			}
			CompositeReason newComposite =
				new CompositeReason(basic, bound, isUpper,
						            reasons, coeffs, lastLiteral);
			lastLiteral.addDependent(newComposite);
			long mid;
			if (Config.PROFILE_TIME) {
				mid = System.nanoTime();
				m_propBoundTime += mid - start;
			}
			Clause conflict = setBound(newComposite);
			if (Config.PROFILE_TIME)
				m_propBoundSetTime += System.nanoTime() - mid;
			return conflict;
		}
		if (Config.PROFILE_TIME)
			m_propBoundTime += System.nanoTime() - start;
		return null;
	}
	
	/**
	 * Dump the equations of all variables simplified out of the tableau.
	 */
	@SuppressWarnings("unused")
	private void dumpSimps() {
		if( msimps == null )
			return;
		for( Entry<LinVar, TreeMap<LinVar,Rational>>me : msimps.entrySet() ) {
			mengine.getLogger().debug(me.getKey() + " = " + me.getValue());
		}
	}

	/**
	 * Generate a bound constraint for a given variable. We use
	 * {@link BoundConstraint}s to represent bounds for variables
	 * and linear combination thereof. Those constraints are optimized to
	 * prevent strict bounds by manipulating the bounds.
	 * @param var      Variable to set bound on.
	 * @param bound    Bound to set on <code>var</code>.
	 * @param isLowerBound Is the bound a lower bound?
	 * @param strict   Is the bound strict?
	 * @return Constraint representing this bound.
	 */
	private Literal generateConstraint(LinVar var, Rational bound,
			boolean isLowerBound, boolean strict) {
		InfinitNumber rbound = new InfinitNumber(bound, 
				(strict ^ isLowerBound) ? -1 : 0);
		if (var.isInt())
			rbound = rbound.floor();
		return generateConstraint(var,rbound,isLowerBound);
	}
	
	private Literal generateConstraint(LinVar var, InfinitNumber rbound,
			boolean isLowerBound) {
		if (var.dead)
			ensureUnsimplified(var);
		BoundConstraint bc = var.mconstraints.get(rbound);
		if (bc == null) {
			bc = new BoundConstraint(rbound, var, mengine.getAssertionStackLevel());
			assert(bc.m_var.checkCoeffChain());
			mengine.addAtom(bc);
		}
		return isLowerBound ? bc.negate() : bc;
	}
	
	/**
	 * Insert a new basic variable into the tableau.
	 * @param v      Variable to insert.
	 * @param coeffs Coefficients for this variable wrt mbasics and msimps.
	 */
	private void insertVar(LinVar v, TreeMap<LinVar,Rational> coeffs) {
		v.mbasic = true;
		v.headEntry = new MatrixEntry();
		v.headEntry.column = v;
		v.headEntry.row = v;
		v.headEntry.nextInRow = v.headEntry.prevInRow = v.headEntry;
		v.headEntry.nextInCol = v.headEntry.prevInCol = v.headEntry;
		v.resetComposites();

		MutableInfinitNumber val = new MutableInfinitNumber();
		Rational gcd = Rational.ONE;
		for (Rational c : coeffs.values()) {
			gcd = gcd.gcd(c);
		}
		assert(gcd.numerator().equals(BigInteger.ONE));
		v.headEntry.coeff = gcd.denominator().negate();
		for (Map.Entry<LinVar,Rational> me : coeffs.entrySet()) {
			assert(!me.getKey().mbasic);
			LinVar nb = me.getKey();
			Rational value = me.getValue().div(gcd);
			assert(value.denominator().equals(BigInteger.ONE));
			BigInteger coeff = value.numerator();
			v.headEntry.insertRow(nb, coeff);
			val.addmul(nb.m_curval, value);
			v.updateUpperLowerSet(coeff, nb);
		}
		val = val.mul(gcd);
		v.m_curval = val.toInfinitNumber();
		assert(v.checkBrpCounters());
		if (v.m_numUpperInf == 0) {
			propagateBound(v, true);
			/* ignore conflicts */
		}
		if (v.m_numLowerInf == 0) {
			propagateBound(v, false);
			/* ignore conflicts */
		}
		assert !(v.m_curval.ma.denominator().equals(BigInteger.ZERO));
	}
	
	/**
	 * Remove a basic variable from the tableau. Note that <code>v</code> has
	 * to be a basic variable. So you might need to call pivot before removing
	 * a variable.
	 * @param v Basic variable to remove from the tableau.
	 */
	private TreeMap<LinVar, Rational> removeVar(LinVar v) {
		assert(v.mbasic);
//		mcurbasics.remove(v);
		m_linvars.remove(v);
		TreeMap<LinVar,Rational> res = new TreeMap<LinVar, Rational>();
		BigInteger denom = v.headEntry.coeff.negate();
		for (MatrixEntry entry = v.headEntry.nextInRow;
			entry != v.headEntry; entry = entry.nextInRow) {
			assert(!entry.column.mbasic);
			res.put(entry.column, Rational.valueOf(entry.coeff, denom));
			entry.removeFromMatrix();
		}
		v.headEntry = null;
		return res;
	}
	
	public void removeLinVar(LinVar v) {
		assert moob.isEmpty();
		if (!v.mbasic) {
			// We might have nonbasic variables that do not contribute to a basic variable. 
			if (v.headEntry.nextInCol == v.headEntry) {
				m_linvars.remove(v);
				return;
			}
			Clause conflict = pivot(v.headEntry.nextInCol);
			assert(conflict == null) : "Removing a variable produced a conflict!";
		}
		TreeMap<LinVar, Rational> coeffs = removeVar(v);
		updateSimps(v, coeffs);
	}
	
	/**
	 * This function simplifies the tableau by removing all trivially 
	 * satisfiable equations. In case of rationals, an equation of the
	 * for x_b = sum_i c_i*x_i where there is at least one x_i without
	 * any bound constraint is trivially satisfiable.
	 */
	private Clause simplifyTableau() {
		// We cannot remove more vars than we have basic variables
		List<LinVar> removeVars = new ArrayList<LinVar>(m_linvars.size());
		for( LinVar v : m_linvars ) {
			// Skip integer and already simplified variables
			if (v.isInt() || v.dead)
				continue;
			if (v.unconstrained()) {
				if (v.mbasic) {
					removeVars.add(v);
					v.dead = true;
				} else {
					for (MatrixEntry entry = v.headEntry.nextInCol;
						entry != v.headEntry; entry = entry.nextInCol) {
						LinVar basic = entry.row;
						if (!basic.unconstrained() && !basic.dead &&
								!removeVars.contains(basic)) {
							if (mengine.getLogger().isDebugEnabled())
								mengine.getLogger().debug("simplify pivot "+entry);
							Clause conflict = pivot(entry);
							InfinitNumber bound = basic.getLowerBound();
							if (bound.isInfinity())
								bound = basic.getUpperBound();
							if (!bound.isInfinity())
								updateVariableValue(basic, bound);
							// Just in case it was out of bounds before...
							moob.remove(basic);
							v.dead = true;
							removeVars.add(v);
							if (conflict != null) {
								for (LinVar var : removeVars)
									// We marked them dead, but don't simplify
									// them right now.  Remove the mark!!!
									var.dead = false;
								return conflict;
							}
							break;
						}
					}
				}
			}
		}
		/*
		 * Here, we have a tableau containing some trivially satisfiable
		 * rows. We now remove one var after the other and check against
		 * all simplified variables. This way, all simplified variables
		 * only contain variables relative to the current set of nonbasics.
		 */
		HashMap<LinVar,TreeMap<LinVar,Rational>> newsimps = 
			new HashMap<LinVar, TreeMap<LinVar,Rational>>();
		LinkedHashSet<LinVar> props = new LinkedHashSet<LinVar>(m_propBounds);
		for (LinVar v : removeVars) {
			assert(v.mbasic);
			mengine.getLogger().debug(new DebugMessage("Simplifying {0}",v));
			TreeMap<LinVar,Rational> coeffs = removeVar(v);
			updateSimps(v,coeffs);
			newsimps.put(v,coeffs);
			props.remove(v);
		}
		m_propBounds = new ArrayDeque<LinVar>(props);
		msimps.putAll(newsimps);
		assert(checkPostSimplify());
		return null;
	}
	
	/**
	 * Represents a linvar in terms of the current column (non-basic) variables
	 * and adds it to the map facs.
	 * @param lv    The variable to add.
	 * @param fac   The factor of the variable to add.
	 * @param facs  The map, where to add it.
	 */
	private void unsimplifyAndAdd(LinVar lv,Rational fac, Map<LinVar,Rational> facs) {
		if (lv.dead) {
			// simplified variable
			ArrayDeque<UnsimpData> unsimpStack = new ArrayDeque<UnsimpData>();
			unsimpStack.add(new UnsimpData(lv, fac));
			while (!unsimpStack.isEmpty()) {
				UnsimpData data = unsimpStack.removeFirst();
				if (data.var.dead) {
					for (Entry<LinVar,Rational> simp : 
						msimps.get(data.var).entrySet()) {
						unsimpStack.add(new UnsimpData(simp.getKey(), 
								data.fac.mul(simp.getValue())));
					}
				} else {
					unsimplifyAndAdd(data.var, data.fac, facs);
				}
			}
		} else if (lv.mbasic) {
			// currently basic variable
			BigInteger denom = lv.headEntry.coeff.negate();
			for (MatrixEntry entry = lv.headEntry.nextInRow;
				entry != lv.headEntry;
				entry = entry.nextInRow) {
				Rational coeff = Rational.valueOf(entry.coeff, denom);
				unsimplifyAndAdd(entry.column, fac.mul(coeff), facs);
			}
		} else {
			// Just add it.
			Rational oldval = facs.get(lv);
			if (oldval == null)
				facs.put(lv, fac);
			else {
				Rational newval = oldval.add(fac);
				if (newval.equals(Rational.ZERO))
					facs.remove(lv);
				else
					facs.put(lv, newval);
			}
		}
	}
	
	private void updateSimps(LinVar v, Map<LinVar, Rational> coeffs) {
		for (Map.Entry<LinVar, TreeMap<LinVar,Rational>> me : msimps.entrySet()) {
			TreeMap<LinVar,Rational> cmap = me.getValue();
			Rational cc = cmap.get(v);
			if (cc != null) {
				cmap.remove(v);
				for (Map.Entry<LinVar, Rational> cme : coeffs.entrySet()) {
					Rational c = cmap.get(cme.getKey());
					if (c == null)
						cmap.put(cme.getKey(), cme.getValue().mul(cc));
					else {
						Rational newcoeff = cme.getValue().mul(cc).add(c);
						if (newcoeff.equals(Rational.ZERO))
							cmap.remove(cme.getKey());
						else
							cmap.put(cme.getKey(), newcoeff);
					}
				}
				me.setValue(cmap);
			}
		}
	}
	
	private void ensureUnsimplified(LinVar var) {
		ensureUnsimplified(var, true);
	}
	
	private void ensureUnsimplified(LinVar var, boolean remove) {
		if (var.dead) {
			assert (msimps.containsKey(var));
			mengine.getLogger().debug(
					new DebugMessage("Ensuring {0} is unsimplified",var));
			// Variable is actually simplified. Reintroduce it
			TreeMap<LinVar,Rational> curcoeffs = new TreeMap<LinVar,Rational>();
			unsimplifyAndAdd(var, Rational.ONE, curcoeffs);
			insertVar(var, curcoeffs);
			var.dead = false;
			if (remove)
				msimps.remove(var);
			m_linvars.add(var);
		}
		assert (!var.dead);
	}

	/**
	 * Calculates the values of the simplified variables.
	 * @return The exact values of the simplified variables.
	 */
	Map<LinVar, ExactInfinitNumber> calculateSimpVals() {
		HashMap<LinVar, ExactInfinitNumber> simps =
			new HashMap<LinVar, ExactInfinitNumber>();
		for (Entry<LinVar,TreeMap<LinVar,Rational>> me : msimps.entrySet()) {
			MutableRational real = new MutableRational(0, 1);
			MutableRational eps = new MutableRational(0, 1);
			for (Entry<LinVar,Rational> chain : me.getValue().entrySet()) {
				real.addmul(chain.getKey().m_curval.ma, chain.getValue());
				if (chain.getKey().mbasic)
					eps.addmul(
							chain.getKey().computeEpsilon(), chain.getValue());
				else if (chain.getKey().m_curval.meps < 0)
					eps.sub(chain.getValue());
				else if (chain.getKey().m_curval.meps > 0)
					eps.add(chain.getValue());
					
			}
			Rational rreal = real.toRational();
			me.getKey().m_curval = new InfinitNumber(rreal, eps.signum());
			simps.put(me.getKey(),
					new ExactInfinitNumber(rreal, eps.toRational()));
		}
		return simps;
	}
	/**
     * Compute freedom interval for a nonbasic variable.
     * @param var   Nonbasic variable to compute freedom interval for.
     * @param lower Lower bound to compute.
     * @param upper Upper bound to compute.
     */
	private void freedom(LinVar var, MutableRational lower,
			MutableRational upper) {
		// never assign lower or upper using = but use setValue
		lower.setValue(var.getLowerBound().ma);
		upper.setValue(var.getUpperBound().ma);
		// fast path: Fixed variable
		if (lower.equals(upper))
			return;
		Rational maxBelow = Rational.NEGATIVE_INFINITY;
		Rational minAbove = Rational.POSITIVE_INFINITY;
		for (MatrixEntry me = var.headEntry.nextInCol; me != var.headEntry;
			me = me.nextInCol) {
			Rational coeff = Rational.valueOf(me.row.headEntry.coeff.negate(), me.coeff);
			Rational below = me.row.getLowerBound().ma.sub(me.row.m_curval.ma).mul(coeff);
			Rational above = me.row.getUpperBound().ma.sub(me.row.m_curval.ma).mul(coeff);
			if (coeff.isNegative()) {
				// reverse orders
				Rational t = below;
				below = above;
				above = t;
			}
			assert (below.signum() <= 0 && above.signum() >= 0);
			if (below.compareTo(maxBelow) > 0)
				maxBelow = below;
			if (above.compareTo(minAbove) < 0)
				minAbove = above;
		}
		maxBelow = maxBelow.add(var.m_curval.ma);
		minAbove = minAbove.add(var.m_curval.ma);
		if (maxBelow.compareTo(lower.toRational()) > 0)
			lower.setValue(maxBelow);
		if (minAbove.compareTo(upper.toRational()) < 0)
			upper.setValue(minAbove);
	}
	/**
	 * Mutate a model such that less variables have the same value.
	 * 
	 * TODO This method is still very inefficient. Even if all variables have
	 * distinct values, we still compute a lot of stuff.
	 * @return Multi-Map describing which variables have which (common) value.
	 */
	private Map<ExactInfinitNumber,List<SharedTerm>> mutate() {
		MutableRational lower = new MutableRational(0,1);
		MutableRational upper = new MutableRational(0,1);
		TreeSet<Rational> prohib = new TreeSet<Rational>();
		for (LinVar lv : m_linvars) {
			if (lv.mbasic
				|| lv.getUpperBound().equals(lv.getLowerBound()))
				// variable is basic or is fixed by its own constraints
				continue;
			freedom(lv,lower,upper);
			if (lower.equals(upper))
				// variable is fixed by its own constraints and basic variables
				continue;
			Rational gcd = lv.isInt() ? Rational.ONE : Rational.ZERO;
			Rational curval = lv.m_curval.ma;

			prohib.clear();
			// prevent violating disequalities
			if (lv.mdisequalities != null) {
				for (Rational diseq : lv.mdisequalities.keySet()) {
					prohib.add(diseq);
				}
			}
			
			// Iterate over basic variables
			HashMap<LinVar, Rational> basicFactors = new HashMap<LinVar, Rational>();
			for (MatrixEntry it1 = lv.headEntry.nextInCol; it1 != lv.headEntry;
				it1 = it1.nextInCol) {
				LinVar basic = it1.row;
				Rational coeff = Rational.valueOf(it1.coeff.negate(), it1.row.headEntry.coeff);
				basicFactors.put(basic, coeff);
				if (basic.isInt())
					gcd = gcd.gcd(coeff.abs());
				if (basic.mdisequalities != null) {
					for (Rational diseq : basic.mdisequalities.keySet()) {
						prohib.add(diseq.sub(basic.m_curval.ma).div(coeff).add(curval));
					}
				}
			}
				
			// Do not merge two shared variables
			for (int i = 0; i < m_sharedVars.size(); i++) {
				SharedTerm sh1 = m_sharedVars.get(i);
				LinVar lv1 = sh1.getLinVar();
				Rational coeff1 = basicFactors.get(lv1);
				if (coeff1 == null)
					coeff1 = Rational.ZERO;
				else
					coeff1 = coeff1.mul(sh1.getFactor());
				Rational curval1 = sh1.getOffset();
				if (lv1 != null)
					curval1 = curval1.addmul(lv1.m_curval.ma, sh1.getFactor());
				for (int j = i + 1; j < m_sharedVars.size(); j++) {
					SharedTerm sh2 = m_sharedVars.get(j);
					LinVar lv2 = sh2.getLinVar();
					Rational coeff2 = basicFactors.get(lv2);
					Rational curval2 = sh2.getOffset();
					if (lv2 != null)
						curval2 = curval2.addmul(lv2.m_curval.ma, sh2.getFactor());
					if (coeff2 == null)
						coeff2 = Rational.ZERO;
					else
						coeff2 = coeff2.mul(sh2.getFactor());
					// If coeffs are equal, there is nothing we can do.
					if (coeff1.equals(coeff2))
						continue;
					
					// Prevent shared variables to get equal.
					Rational cdiff = coeff1.sub(coeff2);
					prohib.add(curval.sub(curval1.sub(curval2).div(cdiff)));
				}
			}
			// If there is no integer constraint for the non-basic manipulate
			// it by eps, otherwise incrementing by a multiple of gcd.inverse()
			// will preserve integrity of all depending variables. 
			Rational lcm = gcd.inverse();
			Rational chosen = choose(lower,upper,prohib,lcm,lv.m_curval.ma);
			assert (chosen.compareTo(lower.toRational()) >= 0
					&& chosen.compareTo(upper.toRational()) <= 0);
			if (!chosen.equals(lv.m_curval.ma))
				updateVariableValue(lv, new InfinitNumber(chosen, 0));
		}
		mengine.getLogger().debug("Shared Vars:");
		Map<ExactInfinitNumber, List<SharedTerm>> result = 
			new HashMap<ExactInfinitNumber, List<SharedTerm>>();
		Map<LinVar, ExactInfinitNumber> simps = calculateSimpVals();
		for (SharedTerm shared : m_sharedVars) {
			MutableRational real = new MutableRational(shared.getOffset());
			MutableRational eps = new MutableRational(0, 1);
			if (shared.getLinVar() != null) {
				if (shared.getLinVar().dead) {
					ExactInfinitNumber simpval = simps.get(shared.getLinVar());
					real.addmul(simpval.getRealValue(), shared.getFactor());
					eps.addmul(simpval.getEpsilon(), shared.getFactor());
				} else {
					if (shared.getLinVar().mbasic)
						eps.addmul(shared.getLinVar().computeEpsilon(),
								shared.getFactor());
					else if (shared.getLinVar().m_curval.meps > 0)
						eps.add(shared.getFactor());
					else if (shared.getLinVar().m_curval.meps < 0)
						eps.sub(shared.getFactor());
					real.addmul(shared.getLinVar().m_curval.ma,
							shared.getFactor());
				}
			}
			ExactInfinitNumber curval = new ExactInfinitNumber(
					real.toRational(), eps.toRational());
			if (mengine.getLogger().isDebugEnabled())
				mengine.getLogger().debug(shared+" = "+ curval);
			List<SharedTerm> slot = result.get(curval);
			if (slot == null) {
				slot = new LinkedList<SharedTerm>();
				result.put(curval, slot);
			}
			slot.add(shared);
		}
		return result;
	}
	private Literal ensureDisequality(LAEquality eq) {
		LinVar v = eq.getVar();
		assert (eq.getDecideStatus().getSign() == -1);
		// Disequality already satisfied...
		if (!v.m_curval.ma.equals(eq.getBound()))
			return null;
		if (v.mbasic)
			v.fixEpsilon();
		if (v.m_curval.meps != 0)
			return null;

		// Find already existing literal
		InfinitNumber bound = new InfinitNumber(eq.getBound(), 0);
		BoundConstraint gbc = eq.getVar().mconstraints.get(bound);
		boolean usegt = gbc == null;
		if (!usegt) {
			if (gbc.getDecideStatus() == null)
				return gbc.negate();
		}
		InfinitNumber strictbound = bound.sub(eq.getVar().getEpsilon());
		BoundConstraint lbc = eq.getVar().mconstraints.get(strictbound);
		if (lbc != null) {
			if (lbc.getDecideStatus() == null)
				return lbc;
		}
		// Here, we have neither inequality. Create one...	
		return usegt ?
				generateConstraint(eq.getVar(),eq.getBound(), false, false).negate() :
				generateConstraint(eq.getVar(),eq.getBound(),false,true);
	}
    /**
     * Choose a value from a given interval respecting certain prohibitions.
     * The interval is given symbolically by a lower and an upper bound. All
     * values prohibited are given in a set. Note that this set might also
     * contain values outside the interval. For integer solutions, we also give
     * the lcm such that we can generate an integer solution from an integer
     * solution.
     *
     * If the interval is empty or no value can be found, the current value
     * should be returned.
     * @param lower        Lower bound of the interval.
     * @param upper        Upper bound of the interval.
     * @param prohibitions Prohibited values.
     * @param lcm          Least common multiple of denominators (integer only)
     * @param currentValue Value currently assigned to a variable.
     * @return
     */
	private Rational choose(MutableRational lower,
			MutableRational upper,
			TreeSet<Rational> prohibitions,
			Rational lcm, Rational currentValue) {
		// Check if variable is fixed or allowed.
		if (upper.equals(lower)
			|| !prohibitions.contains(currentValue))
			return currentValue;
		
		if (lcm == Rational.POSITIVE_INFINITY) {
			/* use binary search to find the candidate */
			Rational low = lower.toRational();
			if (low == Rational.NEGATIVE_INFINITY) {
				if (upper.signum() > 0)
					low = Rational.ZERO;
				else
					low = upper.toRational().sub(Rational.ONE);
			}
			Rational mid = upper.toRational().add(low).div(Rational.TWO);
			if (mid == Rational.POSITIVE_INFINITY)
				mid = low.add(Rational.ONE);
			while (prohibitions.contains(mid))
				mid = mid.add(low).div(Rational.TWO);
			return mid;
		} else {
			/* We should change it.  We search upwards and downwards by
			 * incrementing and decrementing currentValue by lcm. 
			 */
			MutableRational up = new MutableRational(currentValue);
			MutableRational down = new MutableRational(currentValue);
			while (true) {
				up.add(lcm);
				if (up.compareTo(upper) > 0)
					break;
				Rational cur = up.toRational();
				if (!prohibitions.contains(cur))
					return cur;
				
				down.sub(lcm);
				if (down.compareTo(lower) < 0)
					break;
				cur = down.toRational();
				if (!prohibitions.contains(cur))
					return cur;
			}
			up.add(lcm);
			while (up.compareTo(upper) <= 0) {
				Rational cur = up.toRational();
				if (!prohibitions.contains(cur))
					return cur;
				up.add(lcm);
			}
			down.sub(lcm);
			while (down.compareTo(lower) >= 0) {
				Rational cur = down.toRational();
				if (!prohibitions.contains(cur))
					return cur;
				down.sub(lcm);
			}
			// this can only be reached in the integer case.
			return currentValue;
		}
	}
	
	private Clause mbtc(Map<ExactInfinitNumber,List<SharedTerm>> cong) {
		for (Map.Entry<ExactInfinitNumber,List<SharedTerm>> congclass : cong.entrySet()) {
			List<SharedTerm> lcongclass = congclass.getValue();
			if (lcongclass.size() <= 1)
				continue;
			mengine.getLogger().debug(new DebugMessage("propagating MBTC: {0}", lcongclass));
			Iterator<SharedTerm> it = lcongclass.iterator();
			SharedTerm shared1 = it.next();
			while (it.hasNext()) {
				SharedTerm shared2 = it.next();
				EqualityProxy eq = shared1.createEquality(shared2);
				assert (eq != EqualityProxy.getTrueProxy());
				assert (eq != EqualityProxy.getFalseProxy());
				CCEquality cceq = eq.createCCEquality(shared1, shared2);
				if (cceq.getLASharedData().getDecideStatus() != null) {
					if (cceq.getDecideStatus() == cceq.negate())
						return generateEqualityClause(cceq);
					else if	(cceq.getDecideStatus() == null)
						mproplist.add(cceq);
					else
						mengine.getLogger().debug(
								new DebugMessage("already set: {0}", 
										cceq.getAtom().getDecideStatus()));
				} else {
					mengine.getLogger().debug(new DebugMessage("MBTC: Suggesting literal {0}",cceq));
					m_suggestions.add(cceq.getLASharedData());
				}
			}
		}
		return null;
	}
	
	@Override
	public Literal getSuggestion() {
		Literal res;
		do {
			if (m_suggestions.isEmpty())
				return null;
			res = m_suggestions.removeFirst();
		} while (res.getAtom().getDecideStatus() != null);
		return res;
	}
	
	private InfinitNumber computeMaxEpsilon(Set<Rational> prohibitions) {
		InfinitNumber maxeps = InfinitNumber.POSITIVE_INFINITY;
		for (LinVar v : m_linvars) {
			if (v.mbasic) {
				Rational epsilons = v.computeEpsilon();
				if (epsilons.signum() > 0) {
					InfinitNumber diff = v.getUpperBound().sub
							(new InfinitNumber(v.m_curval.ma, 0)).div(epsilons);
					if (diff.compareTo(maxeps) < 0)
						maxeps = diff;
				} else if (epsilons.signum() < 0) {
					InfinitNumber diff = v.getLowerBound().sub
						(new InfinitNumber(v.m_curval.ma, 0)).div(epsilons);
					if (diff.compareTo(maxeps) < 0)
						maxeps = diff;
				}
				if (epsilons.signum() != 0 && v.mdisequalities != null) {
					for (Rational prohib : v.mdisequalities.keySet())
						// solve v.mcurval = prohib to eps
						// a+b*eps = p ==> eps = (p-a)/b given b != 0
						prohibitions.add(prohib.sub(v.m_curval.ma).div(epsilons));
				}
			} else {
				if (v.m_curval.meps > 0) {
					InfinitNumber diff = v.getUpperBound().sub
							(new InfinitNumber(v.m_curval.ma, 0));
					if (diff.compareTo(maxeps) < 0)
						maxeps = diff;
					assert (v.m_curval.meps == 1);
					if (v.mdisequalities != null) {
						for (Rational prohib : v.mdisequalities.keySet())
							// solve a+eps = p ==> eps = p-a
							prohibitions.add(prohib.sub(v.m_curval.ma));
					}
				} else if (v.m_curval.meps < 0) {
					InfinitNumber diff = new InfinitNumber(v.m_curval.ma, 0).sub
							(v.getLowerBound());
					if (diff.compareTo(maxeps) < 0)
						maxeps = diff;
					assert (v.m_curval.meps == -1);
					if (v.mdisequalities != null) {
						for (Rational prohib : v.mdisequalities.keySet())
							// solve a-eps = p ==> eps = a-p
							prohibitions.add(v.m_curval.ma.sub(prohib));
					}
				}
			}
		}
		return maxeps;
	}

	@Override
	public void decreasedDecideLevel(int currentDecideLevel) {
	}

	@Override
	public void increasedDecideLevel(int currentDecideLevel) {
	}

	/**
	 * We reset the bounds and bound asserting members but not the current value
	 * since this might be a good start for the next iteration.
	 */
	@Override
	public void restart(int iteration) {
	}

	public LAEquality createEquality(int stackLevel, MutableAffinTerm at) {
		Rational normFactor = at.getGCD().inverse();
		at.mul(normFactor);
		LinVar var = generateLinVar(getSummandMap(at), stackLevel);
		InfinitNumber bound;
		if (at.m_summands.size() == 1) {
			Rational fac = at.m_summands.values().iterator().next();
			bound = at.m_constant.negate().div(fac);
		} else
			bound = at.m_constant.negate();
		assert bound.meps == 0;
		LAEquality sharedData = var.getEquality(bound);
		if (sharedData == null) {
			sharedData = 
				new LAEquality(stackLevel, var, bound.ma);
			mengine.addAtom(sharedData);
			var.addEquality(sharedData);
		}
		ensureUnsimplified(var);
		return sharedData;
	}

	@Override
	public Clause startCheck() {
		m_Eps = null;
		m_InCheck = true; 
		return simplifyTableau();
	}
	
	@Override
	public void endCheck() {
		m_InCheck = false;
	}

	public Literal createCompositeLiteral(LAReason comp, Literal beforeLit) {
		mCompositeCreateLit++;
		int depth = comp.getLastLiteral().getDecideLevel();
		if (mengine.getLogger().isDebugEnabled())
			mengine.getLogger().debug("Create Propagated Literal for "+comp+" @ level "+depth);
		LinVar var = comp.getVar();
		InfinitNumber bound = comp.getBound();
		if (!comp.isUpper())
			bound = bound.sub(var.getEpsilon());
		BoundConstraint bc = new BoundConstraint(bound, var, mengine.getAssertionStackLevel());
		Literal lit = comp.isUpper() ? bc : bc.negate();
		int decideLevel = comp.getLastLiteral().getDecideLevel();
		if (beforeLit != null 
			&& beforeLit.getAtom().getDecideLevel() == decideLevel)
			mengine.insertPropagatedLiteralBefore(this, lit, beforeLit);
		else
			mengine.insertPropagatedLiteral(this, lit, decideLevel);
		InfinitNumber litBound = comp.isUpper() ? bc.getBound() : bc.getInverseBound();
		if (!comp.getExactBound().equals(litBound))
			insertReasonOfNewComposite(var, lit);
		
		return lit;
	}

	public void generateSharedVar(SharedTerm shared, MutableAffinTerm mat, int level) {
		assert mat.getConstant().meps == 0;
		if (mat.isConstant()) {
			shared.setLinVar(Rational.ZERO, null, mat.getConstant().ma);
		} else {
			Rational normFactor = mat.getGCD().inverse();
			Rational offset = mat.getConstant().ma;
			mat.mul(normFactor);
			LinVar linVar = generateLinVar(getSummandMap(mat), level);
			shared.setLinVar(normFactor.inverse(), linVar, offset);
		}
	}

	public void share(SharedTerm shared) {
		m_sharedVars.add(shared);
	}
	
	public void unshare(SharedTerm shared) {
		m_sharedVars.remove(shared);
	}

	@Override
	public void removeAtom(DPLLAtom atom) {
		if (atom instanceof BoundConstraint) {
			BoundConstraint bc = (BoundConstraint) atom;
			LinVar v = bc.getVar();
			v.mconstraints.remove(bc.getBound());
//			if (v.unconstrained()) {
//				if (v.isInitiallyBasic()) {
//					System.err.println("Removing initially basic variable");
//					removeLinVar(bc.getVar());
//				} else if (v.mbasic) {
//					System.err.println("Moving unconstraint variable away");
//					// Move it out of the way and let simplifier handle this
//					for (MatrixEntry entry = v.headEntry.nextInRow; 
//						entry != v.headEntry; entry = entry.nextInRow) {
//						if (entry.column.isInitiallyBasic()) {
//							System.err.println("Using variable " + entry.column);
//							pivot(entry);
//							return;
//						}
//					}
//					throw new IllegalStateException("We should never reach here!!!");
//				}
//			}
		} else if (atom instanceof LAEquality) {
			LAEquality laeq = (LAEquality) atom;
			InfinitNumber num = new InfinitNumber(laeq.getBound(), 0);
			laeq.getVar().mequalities.remove(num);
			for (CCEquality eq : laeq.getDependentEqualities())
				eq.removeLASharedData();
		}
	}

	@Override
	public void pop(Object object, int targetlevel) {
		ArrayList<LinVar> removeVars = new ArrayList<LinVar>();
		for (LinVar v : m_linvars) {
			if (v.assertionstacklevel > targetlevel)
				removeVars.add(v);
		}
		for (LinVar v : msimps.keySet()) {
			if (v.assertionstacklevel > targetlevel)
				removeVars.add(v);
		}
		for (LinVar v : removeVars) {
//			if (/*v.outOfBounds()*/moob.contains(v))
				moob.remove(v);
			if (v.dead)
				msimps.remove(v);
			else
				removeLinVar(v);
			if (v == m_conflictVar)
				m_conflictVar = null;
//			v.mbasic = v.isInitiallyBasic();
			/// Mark variable as dead
			v.assertionstacklevel = -1;
			if (v.isInt())
				m_intVars.remove(v);
		}
		m_sharedVars.endScope();
		mterms.endScope();
		// TODO This is a bit too much but should work
		m_suggestions.clear();
		mproplist.clear();
		// TODO What is this for?
		m_propBounds.clear();
		assert popPost();
	}

	private final boolean popPost() {
		for (Map.Entry<LinVar, TreeMap<LinVar, Rational>> me : msimps.entrySet()) {
			assert me.getKey().dead;
			for (Map.Entry<LinVar, Rational> me2 : me.getValue().entrySet()) {
				assert !me2.getKey().dead;
				assert !msimps.containsKey(me2.getKey());
				assert !me2.getValue().equals(Rational.ZERO);
			}
		}
		return true;
	}
	
	@Override
	public Object push() {
		mterms.beginScope();
		m_sharedVars.beginScope();
		return null;
	}

	@Override
	public Object[] getStatistics() {
		return new Object[] {
				":LA", new Object[][] {
						{"Pivot", numPivots},
						{"PivotBland", numPivotsBland},
						{"SwitchToBland", numSwitchToBland},
						{"Vars", m_linvars.size()},
						{"SimpVars", (msimps != null ? msimps.size() : 0)},
						{"CompLits", mCompositeCreateLit},
						{"Cuts", numCuts},
						{"Branches", numBranches},
						{"Times", new Object[][]{
								{"Pivot", pivotTime/1000000},
								{"BoundComp", m_propBoundTime/1000000},
								{"BoundSet", m_propBoundSetTime/1000000},
								{"BoundBack", m_backtrackPropTime/1000000},
								{"CutGen", cutGenTime/1000000}}
						}
				}};
	}

	// utilities for the new pivoting strategy
	private LinVar findBestVar() {
		LinVar best = null;
		for (LinVar v : moob) {
			if (best == null || best.chainlength > v.chainlength)
				best = v;
		}
		if (best != null)
			moob.remove(best);
		return best;
	}
	private MatrixEntry findNonBasic(LinVar basic, boolean isLower) {
		assert(basic.mbasic);
		MatrixEntry best = null;
		// Is the correct side unbounded?
		boolean unboundedSide = false;
		for (MatrixEntry entry = basic.headEntry.nextInRow;
		entry != basic.headEntry; entry = entry.nextInRow) {
			LinVar col = entry.column;
			if (col.m_upper == null && col.m_lower == null)
				// Unbounded at every side => trivially satisfied row
				return entry;
			boolean checkLower = isLower == (entry.coeff.signum() < 0);
			if (checkLower) {
				if (col.m_lower == null) {
					if (unboundedSide &&
							best.column.chainlength > col.chainlength)
						best = entry;
					else {
						best = entry;
						unboundedSide = true;
					}
				} else if (!unboundedSide && col.isDecrementPossible() &&
						(best == null ||
								best.column.chainlength > col.chainlength))
					best = entry;
			} else {
				if (col.m_upper == null) {
					if (unboundedSide &&
							best.column.chainlength > col.chainlength)
						best = entry;
					else {
						best = entry;
						unboundedSide = true;
					}
				} else if (!unboundedSide && col.isIncrementPossible() &&
						(best == null ||
								best.column.chainlength > col.chainlength))
					best = entry;
			}
		}
		return best;
	}
	
	/**
	 * Check whether the LA solver should fill in the value for this term.  This
	 * is the case, if it is an ApplicationTerm corresponding to a 0-ary
	 * function.
	 * @param term Term to check.
	 * @return Symbol that gets a value from the LA solver.
	 */
	private FunctionSymbol getsValueFromLA(Term term) {
		if (term instanceof ApplicationTerm) {
			ApplicationTerm at = (ApplicationTerm) term;
			if (at.getParameters().length == 0)
				return at.getFunction();
		}
		return null;
	}

	@Override
	public void fillInModel(Model model, Theory t, SharedTermEvaluator ste) {
		prepareModel();
		for (LinVar var : m_linvars) {
			if (!var.isInitiallyBasic()) {
				Term term = var.getSharedTerm().getTerm();
				FunctionSymbol fsym = getsValueFromLA(term);
				if (fsym != null) {
					Rational val = realValue(var);
					model.extend(fsym,
							new Value(val.toTerm(fsym.getReturnSort())));
				}
			}
		}
		if (msimps != null ) {
			for (Entry<LinVar,TreeMap<LinVar,Rational>> me : msimps.entrySet()) {
				LinVar var = me.getKey();
				if (!var.isInitiallyBasic()) {
					Term term = var.getSharedTerm().getTerm();
					FunctionSymbol fsym = getsValueFromLA(term);
					if (fsym != null) {
						Rational val = Rational.ZERO;
						for (Entry<LinVar,Rational> chain : me.getValue().entrySet())
							val = val.add(realValue(chain.getKey()).mul(chain.getValue()));
						model.extend(fsym,
								new Value(val.toTerm(fsym.getReturnSort())));
					}
				}
			}
		}
	}
	
}
