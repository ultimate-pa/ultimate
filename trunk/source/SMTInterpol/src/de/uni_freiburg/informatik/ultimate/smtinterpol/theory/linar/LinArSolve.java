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
import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;
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

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.EqualityProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ITheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.Model;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.NumericSortInterpretation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.model.SharedTermEvaluator;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.LeafNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.ScopedArrayList;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashMap;

/**
 * Class implementing a decision procedure for linear arithmetic over rationals
 * and integers. An algorithm proposed by Dutertre and de Moura is used. It
 * provides tableau simplification, theory propagation, conflict set generation
 * and interpolation.
 *
 * To build a tableau, we create slack variables for every linear combination of
 * non-basic variables. To be able to recognize recurring linear combinations,
 * we canonicalize every linear combination and remember them the first time we
 * see them. Canonicalization takes advantage of the ordering of non-basic
 * variables. We transform every linear combination to an equivalent one where
 * the greatest common divisor of the coefficient is equal to one and the
 * coefficient of the first non-basic variable is positive.
 *
 * Theory propagation comes in two flavors: bound propagation and bound
 * refinement propagation.
 *
 * With bound propagation, we propagate every bound <code>x <= c'</code> after
 * setting bound <code>x <= c</code> where <code>c<=c'</code>. Lower bounds are
 * handled the same way.
 *
 * With bound refinement propagation, we propagate bounds from the column
 * (non-basic) variables to a row (basic) variable. The bound for the row
 * variable is a simple linear combination of the bounds for the column
 * variables. For the derived bound we create a composite reason to remember the
 * bound. Then we can use this composite reason as a source for bound
 * propagation and propagate all bounds that are weaker than the composite.
 *
 * @author Juergen Christ, Jochen Hoenicke
 */
public class LinArSolve implements ITheory {
	/** The Clausifier. */
	final Clausifier mClausifier;
	/**
	 * The list of all variables (basic and nonbasic, integer and reals) indexed by
	 * their matrix position.
	 */
	final ScopedArrayList<LinVar> mLinvars;
	/**
	 * The tableaux, represented as list of all tableaux row indexed by matrix
	 * position. The entries for column variables (nonbasic) must be null.
	 */
	final ArrayList<TableauxRow> mTableaux;
	/**
	 * The tableaux row occurence. For each column variable gives the set of row
	 * variables (represented as bitset indexed with matrix position), where the
	 * tableaux row contains the column variable. The entries for row variables must
	 * be null.
	 */
	final ArrayList<BitSet> mDependentRows;
	/** All non-basic integer variables. */
	final Set<LinVar> mIntVars;
	/** The literals that will be propagated. */
	final Queue<Literal> mProplist;
	/** The basic variables hashed by their linear combinations. */
	final ScopedHashMap<Map<LinVar, Rational>, LinVar> mBasics;
	/**
	 * List of all variables outside their bounds. I prefer a tree set here since it
	 * provides ordering, retrieval of the first element, addition of elements and
	 * uniqueness of elements!
	 */
	final Set<LinVar> mOob;
	/// --- Statistics variables ---
	/** Pivot counter. */
	int mNumPivots;
	/** Pivot counter. */
	int mNumPivotsBland;
	/** Time needed for pivoting operations. */
	long mPivotTime;
	/** Time needed for fixOobs (including searching for pivot). */
	long mFixTime;
	/** Number of literals created due to composites. */
	int mCompositeCreateLit;

	int mCountGetUpperBound;
	long mTimeGetUpperBound;

	// Statistics
	int mNumCuts;
	int mNumBranches;
	long mCutGenTime;
	final ScopedArrayList<LASharedTerm> mSharedVars = new ScopedArrayList<>();

	/** The next suggested literals */
	final ArrayDeque<Literal> mSuggestions;

	private long mPropBoundTime;
	private long mPropBoundSetTime;
	private long mBacktrackPropTime;
	/**
	 * The variables for which we need to recompute the composite bounds.
	 */
	private final BitSet mDirty;
	private LinVar mConflictVar;
	private Rational mEps;

	/** Are we in a check-sat? */
	private boolean mInCheck = false;
	/**
	 * This is -1 if no non-linear var exists, otherwise the push/pop level where
	 * the first non-linear variable was introduced.
	 */
	private int mHasNonLinearVar = -1;
	/** Current number of pushes. */
	private int mPushPopLevel = 0;

	/**
	 * Basic initialization.
	 *
	 * @param engine DPLLEngine this theory is used in.
	 */
	public LinArSolve(final Clausifier clausifier) {
		mClausifier = clausifier;
		mLinvars = new ScopedArrayList<>();
		mTableaux = new ArrayList<>();
		mDependentRows = new ArrayList<>();
		mIntVars = new LinkedHashSet<>();
		mDirty = new BitSet();
		mProplist = new ArrayDeque<>();
		mSuggestions = new ArrayDeque<>();
		mBasics = new ScopedHashMap<>();
		mOob = new HashSet<>();
		mNumPivots = 0;
		mPivotTime = 0;
		mFixTime = 0;
		mCompositeCreateLit = 0;
		mNumCuts = 0;
		mNumBranches = 0;
		mCutGenTime = 0;
//		m_compositeWatchers = new HashMap<LAReason, Set<CompositeReason>>();
	}

	public DPLLEngine getEngine() {
		return mClausifier.getEngine();
	}

	public LogProxy getLogger() {
		return mClausifier.getLogger();
	}

	/// --- Assertion check routines ---
	private boolean checkClean() {
		if (Config.EXPENSIVE_ASSERTS) {
			/* check if there are unprocessed bounds */
			for (final LinVar v : mLinvars) {
				assert mLinvars.get(v.mMatrixpos) == v;
				if (!v.mBasic) {
					continue;
				}
				assert v.getTightLowerBound().mEps != 0 || v == mConflictVar
						|| v.getDiseq(v.getTightLowerBound().mReal) == null;
				assert v.getTightUpperBound().mEps != 0 || v == mConflictVar
						|| v.getDiseq(v.getTightUpperBound().mReal) == null;
				assert v.checkReasonChains();
			}
		}
		return true;
	}

	private boolean checkoobcontent() {
		for (final LinVar v : mLinvars) {
			assert !v.outOfBounds() || mOob.contains(v) : "Variable " + v + " is out of bounds: " + v.getLowerBound()
					+ "<=" + v.getValue() + "<=" + v.getUpperBound();
		}
		return true;
	}

	/// --- Introduction of variables ---
	/**
	 * Add a new non-basic variable.
	 *
	 * @param name  Name of the variable
	 * @param isint Is the variable integer valued
	 * @param level The assertion stack level for this variable
	 * @return Newly created variable
	 */
	public LinVar addVar(final Term name, final boolean isint, final int level) {
		if ((name instanceof ApplicationTerm)
				&& ((ApplicationTerm) name).getFunction().getName().equals(SMTLIBConstants.MUL)) {
			mHasNonLinearVar = mPushPopLevel;
		}
		mClausifier.getLogger().debug("Creating var %s", name);
		final LinVar var = new LinVar(name, isint, level, mLinvars.size());
		mLinvars.add(var);
		mDependentRows.add(new BitSet());
		mTableaux.add(null);
		if (isint) {
			mIntVars.add(var);
		}
		return var;
	}

	/**
	 * Add a new basic variable that is defined as linear combination.
	 *
	 * @param factors the linear combination as a map from LinVar to its factor. The
	 *                map must be normalized, i.e. divided by its gcd.
	 * @return Newly created variable
	 */
	private LinVar generateLinVar(final TreeMap<LinVar, Rational> factors) {
		if (factors.size() == 1) {
			final Map.Entry<LinVar, Rational> me = factors.entrySet().iterator().next();
			assert me.getValue().equals(Rational.ONE);
			final LinVar var = me.getKey();
			return var;
		}
		LinVar var = mBasics.get(factors);
		if (var == null) {
			// Linear combination not known yet
			final LinVar[] vars = new LinVar[factors.size()];
			final BigInteger[] coeffs = new BigInteger[factors.size()];
			int i = 0;
			final TreeMap<LinVar, Rational> curcoeffs = new TreeMap<>();
			boolean isInt = true;
			for (final Map.Entry<LinVar, Rational> entry : factors.entrySet()) {
				vars[i] = entry.getKey();
				assert entry.getValue().denominator().equals(BigInteger.ONE);
				coeffs[i] = entry.getValue().numerator();
				unsimplifyAndAdd(entry.getKey(), entry.getValue(), curcoeffs);
				isInt &= vars[i].mIsInt;
				i++;
			}
			final int index = mLinvars.size();
			var = new LinVar(new LinTerm(vars, coeffs), isInt, mClausifier.getStackLevel(), index);
			mBasics.put(factors, var);
			mLinvars.add(var);
			mDependentRows.add(null);
			mTableaux.add(new TableauxRow(var, curcoeffs));
			mDirty.set(index);
			mClausifier.getLogger().debug("Generated LinVar %1$s", var);
			var.mBasic = true;
			ExactInfinitesimalNumber curValue = ExactInfinitesimalNumber.ZERO;
			for (final MatrixEntry entry : var.getTableauxRow(this)) {
				final LinVar colVar = entry.getColumn();
				final Rational coeff = Rational.valueOf(entry.getCoeff(), entry.getHeadCoeff().negate());
				curValue = curValue.add(colVar.getValue().mul(coeff));
				mDependentRows.get(colVar.mMatrixpos).set(var.mMatrixpos);
			}
			var.setValue(curValue);
			assert var.checkCoeffChain(this);
		}
		return var;
	}

	/**
	 * Generate a bound constraint for <code>at <(=) 0</code>.
	 *
	 * @param at       Affine input term (may be unit term c_i*x_i+c or sum_i
	 *                 c_i*x_i+c)
	 * @param strict   Strict bound (< instead of <=)
	 * @param level    Assertion stack level for the constraint.
	 * @param remember Should the variable remember the generated constraint?
	 * @return
	 */
	public Literal generateConstraint(final MutableAffineTerm at, final boolean strict) {
		final Rational normFactor = at.getGCD().inverse();
		at.mul(normFactor);
		final LinVar var = generateLinVar(getSummandMap(at));
		return generateConstraint(var, at.mConstant.mReal.negate(), normFactor.isNegative(), strict);
	}

	private final TreeMap<LinVar, Rational> getSummandMap(final MutableAffineTerm at) {
		return at.getSummands();
	}

	/**
	 * Update values of all basic variables depending on some non-basic variable.
	 *
	 * @param updateVar the non-basic variable.
	 * @param newValue  Value to set for this variable.
	 */
	void updateVariableValue(final LinVar updateVar, final ExactInfinitesimalNumber newValue) {
		assert (!updateVar.mBasic);
		final ExactInfinitesimalNumber diff = newValue.sub(updateVar.getValue());
		updateVar.addValue(diff);
		for (final MatrixEntry entry : updateVar.getTableauxColumn(this)) {
			final LinVar var = entry.getRow();
			assert var.mBasic;
			final Rational coeff = Rational.valueOf(entry.getCoeff(), entry.getHeadCoeff().negate());
			var.addValue(diff.mul(coeff));
			assert !var.getValue().getRealValue().denominator().equals(BigInteger.ZERO);
			if (var.outOfBounds()) {
				mOob.add(var);
			}
		}
	}

	/**
	 * Update bound of a non-basic variable and generate CompositeReasons for all
	 * its dependent basic variables.
	 *
	 * @param updateVar the non-basic variable.
	 * @param isUpper   whether upper or lower bound is assigned.
	 * @param oldBound  the previous bound.
	 * @param newBound  the new bound.
	 * @return Conflict clause detected during bound refinement propagations
	 */
	private void updateVariable(final LinVar updateVar, final boolean isUpper, final InfinitesimalNumber oldBound,
			final InfinitesimalNumber newBound) {
		assert (!updateVar.mBasic);
		final ExactInfinitesimalNumber diff = updateVar.getValue().isub(newBound);
		final boolean changeVar = isUpper ? (diff.signum() < 0) : diff.signum() > 0;
		if (changeVar) {
			updateVar.addValue(diff);
		}

		assert !(updateVar.getValue().getRealValue().denominator().equals(BigInteger.ZERO));
		final BitSet dependencies = mDependentRows.get(updateVar.mMatrixpos);
		mDirty.or(dependencies);
		for (final MatrixEntry entry : updateVar.getTableauxColumn(this)) {
			final LinVar var = entry.getRow();
			assert var.mBasic;
			final Rational coeff = Rational.valueOf(entry.getCoeff(), entry.getHeadCoeff().negate());
			if (changeVar) {
				var.addValue(diff.mul(coeff));
			}
			assert !var.getValue().getRealValue().denominator().equals(BigInteger.ZERO);
			if (var.outOfBounds()) {
				mOob.add(var);
			}
		}
	}

	public void removeReason(final LAReason reason) {
		final LinVar var = reason.getVar();
		LAReason chain;
		if (reason.isUpper()) {
			if (var.mUpper == reason) {
				var.mUpper = reason.getOldReason();
				if (var.mUpperLiteral == reason) {
					var.mUpperLiteral = ((LiteralReason) reason).getOldLiteralReason();
				} else {
					assert reason instanceof CompositeReason;
				}
				if (!var.mBasic) { // NOPMD
					if (var.getValue().compareTo(var.getLowerBound()) < 0) {
						updateVariableValue(var, new ExactInfinitesimalNumber(var.getLowerBound()));
					}
				} else if (var.outOfBounds()) {
					mOob.add(var);
				}
				return;
			}
			chain = var.mUpper;
			if (var.mUpperLiteral == reason) {
				var.mUpperLiteral = ((LiteralReason) reason).getOldLiteralReason();
			}
		} else {
			if (var.mLower == reason) {
				var.mLower = reason.getOldReason();
				if (var.mLowerLiteral == reason) {
					var.mLowerLiteral = ((LiteralReason) reason).getOldLiteralReason();
				} else {
					assert reason instanceof CompositeReason;
				}
				if (!var.mBasic) { // NOPMD
					if (var.getValue().compareTo(var.getUpperBound()) > 0) {
						updateVariableValue(var, new ExactInfinitesimalNumber(var.getUpperBound()));
					}
				} else if (var.outOfBounds()) {
					mOob.add(var);
				}
				return;
			}
			chain = var.mLower;
			if (var.mLowerLiteral == reason) {
				var.mLowerLiteral = ((LiteralReason) reason).getOldLiteralReason();
			}
		}
		while (true) {
			if (chain instanceof LiteralReason && ((LiteralReason) chain).getOldLiteralReason() == reason) {
				((LiteralReason) chain).setOldLiteralReason(((LiteralReason) reason).getOldLiteralReason());
			}
			if (chain.getOldReason() == reason) {
				chain.setOldReason(reason.getOldReason());
				break;
			}
			chain = chain.getOldReason();
		}
	}

	public void removeLiteralReason(final LiteralReason reason) {
		assert checkClean();
		for (final LAReason depReason : reason.getDependents()) {
			removeReason(depReason);
		}
		removeReason(reason);
		assert checkClean();
	}

	@Override
	public void backtrackLiteral(final Literal literal) {
		assert checkClean();
		final DPLLAtom atom = literal.getAtom();
		LinVar var;
		InfinitesimalNumber bound;
		if (atom instanceof LAEquality) {
			final LAEquality laeq = (LAEquality) atom;
			var = laeq.getVar();
			bound = new InfinitesimalNumber(laeq.getBound(), 0);
			if (laeq == literal.negate()) {
				// disequality: remove from diseq map
				var.removeDiseq(laeq);
			}
		} else if (atom instanceof BoundConstraint) {
			final BoundConstraint bc = (BoundConstraint) atom;
			var = bc.getVar();
			bound = bc.getBound();
		} else {
			return;
		}

		LAReason reason = var.mUpper;
		while (reason != null && reason.getBound().lesseq(bound)) {
			if ((reason instanceof LiteralReason) && ((LiteralReason) reason).getLiteral() == literal
					&& reason.getLastLiteral() == reason) {
				removeLiteralReason((LiteralReason) reason);
				break;
			}
			reason = reason.getOldReason();
		}
		reason = var.mLower;
		while (reason != null && bound.lesseq(reason.getBound())) {
			if ((reason instanceof LiteralReason) && ((LiteralReason) reason).getLiteral() == literal
					&& reason.getLastLiteral() == reason) {
				removeLiteralReason((LiteralReason) reason);
				break;
			}
			reason = reason.getOldReason();
		}
	}

	/**
	 * Check if there is still a pending conflict that must be reported.
	 *
	 * @return the corresponding conflict clause or null, if no conflict pending.
	 */
	public Clause checkPendingConflict() {
		final LinVar var = mConflictVar;
		if (var != null && var.getTightUpperBound().less(var.getTightLowerBound())) {
			// we still have a conflict
			final Explainer explainer = new Explainer(this, getEngine().isProofGenerationEnabled(), null);
			InfinitesimalNumber slack = var.getTightLowerBound().sub(var.getTightUpperBound());
			slack = var.mUpper.explain(explainer, slack, Rational.ONE);
			slack = var.mLower.explain(explainer, slack, Rational.MONE);
			return explainer.createClause(getEngine());
		}
		mConflictVar = null;
		return null;
	}

	@Override
	public void backtrackAll() {
		mProplist.clear();
		mSuggestions.clear();
	}

	@Override
	public void backtrackStart() {
		mProplist.clear();
		mSuggestions.clear();
	}

	@Override
	public Clause backtrackComplete() {
		Clause conflict = checkPendingConflict();
		if (conflict != null) {
			return conflict;
		}
		conflict = checkPendingBoundPropagations();
		if (conflict != null) {
			return conflict;
		}
		// recheck bound propagations
		for (final LinVar lv : mLinvars) {
			if (lv.hasTightUpperBound()) {
				for (final BoundConstraint bc : lv.mConstraints.tailMap(lv.getTightUpperBound(), true).values()) {
					assert lv.getTightUpperBound().lesseq(bc.getBound());
					if (bc.getDecideStatus() == null) {
						mProplist.add(bc);
					}
				}
				for (final LAEquality laeq : lv.mEqualities.tailMap(lv.getTightUpperBound(), false).values()) {
					if (laeq.getDecideStatus() == null) {
						mProplist.add(laeq.negate());
					}
				}
			}
			if (lv.hasTightLowerBound()) {
				for (final BoundConstraint bc : lv.mConstraints.headMap(lv.getTightLowerBound(), false).values()) {
					if (bc.getDecideStatus() == null) {
						mProplist.add(bc.negate());
					}
				}
				for (final LAEquality laeq : lv.mEqualities.headMap(lv.getTightLowerBound(), false).values()) {
					if (laeq.getDecideStatus() == null) {
						mProplist.add(laeq.negate());
					}
				}
			}
		}

		assert checkClean();
		return fixOobs();
	}

	Clause checkPendingBoundPropagations() {
		while (!mDirty.isEmpty()) {
			final int matrixPos = mDirty.nextSetBit(0);
			final LinVar var = mLinvars.get(matrixPos);
			mDirty.clear(matrixPos);
			if (!var.mBasic) {
				continue;
			}
			long time;
			if (Config.PROFILE_TIME) {
				time = System.nanoTime();
			}

			boolean hasUpper = true, hasLower = true;
			final TableauxRow row = mTableaux.get(var.mMatrixpos);
			final int sign = -row.getRawCoeff(0).signum();
			for (int i = 1; i < row.size(); i++) {
				final int coeffSign = row.getRawCoeff(i).signum();
				final LinVar colvar = mLinvars.get(row.getRawIndex(i));
				if (hasUpper) {
					final InfinitesimalNumber colBound = coeffSign == sign ? colvar.getUpperBound()
							: colvar.getLowerBound();
					if (colBound.isInfinity()) {
						hasUpper = false;
					}
				}
				if (hasLower) {
					final InfinitesimalNumber colBound = coeffSign == sign ? colvar.getLowerBound()
							: colvar.getUpperBound();
					if (colBound.isInfinity()) {
						hasLower = false;
					}
				}
			}
			if (Config.PROFILE_TIME) {
				mBacktrackPropTime += System.nanoTime() - time;
				time = System.nanoTime();
			}
			if (hasUpper || hasLower) {
				InfinitesimalNumber upperBound = InfinitesimalNumber.ZERO;
				InfinitesimalNumber lowerBound = InfinitesimalNumber.ZERO;
				for (final MatrixEntry entry : var.getTableauxRow(this)) {
					final Rational coeff = Rational.valueOf(entry.getCoeff(), entry.getHeadCoeff().negate());
					final LinVar colvar = entry.getColumn();
					if (hasUpper) {
						final InfinitesimalNumber colBound = coeff.signum() > 0 ? colvar.getUpperBound()
								: colvar.getLowerBound();
						upperBound = upperBound.add(colBound.mul(coeff));
					}
					if (hasLower) {
						final InfinitesimalNumber colBound = coeff.signum() > 0 ? colvar.getLowerBound()
								: colvar.getUpperBound();
						lowerBound = lowerBound.add(colBound.mul(coeff));
					}
				}
				Clause conflict = null;
				if (hasUpper) {
					conflict = propagateBound(var, upperBound, true);
				}
				if (hasLower) {
					if (conflict == null) {
						conflict = propagateBound(var, lowerBound, false);
					} else {
						mDirty.set(var.mMatrixpos);
					}
				}
				if (conflict != null) {
					if (Config.PROFILE_TIME) {
						mPropBoundTime += System.nanoTime() - time;
					}
					return conflict;
				}
			}
			if (Config.PROFILE_TIME) {
				mPropBoundTime += System.nanoTime() - time;
			}
		}
		return null;
	}

	@Override
	public Clause computeConflictClause() {
		mSuggestions.clear();
		mClausifier.getLogger().debug("Final Check LA");
		assert mOob.isEmpty();
		final Clause c = ensureIntegrals();
		if (c != null || !mSuggestions.isEmpty() || !mProplist.isEmpty()) {
			return c;
		}
		assert mOob.isEmpty();
		mutate();
		assert mOob.isEmpty();
		final Map<ExactInfinitesimalNumber, List<LASharedTerm>> cong = getSharedCongruences();
		assert checkClean();
		mClausifier.getLogger().debug("cong: %s", cong);
		for (final LinVar v : mLinvars) {
			final LAEquality ea = v.getDiseq(v.getValue().getRealValue());
			if (ea == null) {
				continue;
			}
			// if disequality equals bound, the bound should have
			// already been refined.
			// assert !v.getUpperBound().equals(ea.getBound());
			// assert !v.getLowerBound().equals(ea.getBound());
			/*
			 * FIX: Since we only recompute the epsilons in ensureDisequality, we might try
			 * to satisfy an already satisfied disequality. In this case, we return null and
			 * have nothing to do.
			 */
			final Literal lit = ensureDisequality(ea);
			if (lit != null) {
				assert lit.getAtom().getDecideStatus() == null;
				mSuggestions.add(lit);
				mClausifier.getLogger().debug("Using %s to ensure disequality %s", lit, ea.negate());
			}
		}
		if (mSuggestions.isEmpty() && mProplist.isEmpty()) {
			return mbtc(cong);
		}
		assert compositesSatisfied();
		return null;
	}

	@Override
	public int checkCompleteness() {
		if (mHasNonLinearVar >= 0) {
			return DPLLEngine.INCOMPLETE_THEORY;
		}
		return DPLLEngine.COMPLETE;
	}

	private boolean compositesSatisfied() {
		for (final LinVar v : mLinvars) {
			assert v.getValue().roundToInfinitesimal().compareTo(v.getTightUpperBound()) <= 0;
			assert v.getValue().roundToInfinitesimal().compareTo(v.getTightLowerBound()) >= 0;
		}
		return true;
	}

	@Override
	public Literal getPropagatedLiteral() {
		while (!mProplist.isEmpty()) {
			final Literal lit = mProplist.remove();
			if (lit.getAtom().getDecideStatus() == null) {
				return lit;
			}
		}
		return null;
	}

	private Clause createUnitClause(final Literal literal, final boolean isUpper, final InfinitesimalNumber bound,
			final LinVar var) {
		final Explainer explainer = new Explainer(this, getEngine().isProofGenerationEnabled(), literal);
		if (isUpper) {
			assert var.getTightUpperBound().less(bound);
			explainer.addLiteral(literal, Rational.MONE);
			LAReason reason = var.mUpper;
			// Find the first oldest reason that explains the bound
			while (reason.getOldReason() != null && reason.getOldReason().getBound().less(bound)) {
				reason = reason.getOldReason();
			}
			reason.explain(explainer, bound.sub(reason.getBound()), Rational.ONE);
		} else {
			assert bound.less(var.getTightLowerBound());
			explainer.addLiteral(literal, Rational.ONE);
			LAReason reason = var.mLower;
			// Find the first oldest reason that explains the bound
			while (reason.getOldReason() != null && bound.less(reason.getOldReason().getBound())) {
				reason = reason.getOldReason();
			}
			reason.explain(explainer, reason.getBound().sub(bound), Rational.MONE);
		}
		return explainer.createClause(getEngine());
	}

	@Override
	public Clause getUnitClause(final Literal literal) {
		final DPLLAtom atom = literal.getAtom();
		if (atom instanceof LAEquality) {
			final LAEquality laeq = (LAEquality) atom;
			final LinVar var = laeq.getVar();
			if (literal == laeq) {
				final InfinitesimalNumber bound = new InfinitesimalNumber(laeq.getBound(), 0);
				LAReason upperReason = var.mUpper;
				while (upperReason.getBound().less(bound)) {
					upperReason = upperReason.getOldReason();
				}
				LAReason lowerReason = var.mLower;
				while (bound.less(lowerReason.getBound())) {
					lowerReason = lowerReason.getOldReason();
				}
				assert upperReason.getBound().equals(bound) && lowerReason.getBound().equals(bound)
						: "Bounds on variable do not match propagated equality bound";
				final Explainer explainer = new Explainer(this, getEngine().isProofGenerationEnabled(), literal);
				final LiteralReason uppereq = new LiteralReason(var, var.mUpperLiteral,
						var.getTightUpperBound().sub(var.getEpsilon()), true, laeq.negate());
				uppereq.setOldReason(upperReason);
				lowerReason.explain(explainer, var.getEpsilon(), Rational.MONE);
				explainer.addEQAnnotation(uppereq, Rational.ONE);

				return explainer.createClause(getEngine());
			} else {
				final InfinitesimalNumber bound = new InfinitesimalNumber(laeq.getBound(), 0);
				// Check if this was propagated due to an upper bound.
				// We also need to make sure that the upper bound does not
				// depend on the inequality literal.
				LAReason upper = var.mUpper;
				while (laeq.getStackPosition() >= 0 && upper != null
						&& upper.getLastLiteral().getStackPosition() >= laeq.getStackPosition()) {
					upper = upper.getOldReason();
				}
				return createUnitClause(literal, upper != null && upper.getBound().less(bound), bound, var);
			}
		} else if (atom instanceof CCEquality) {
			return generateEqualityClause(literal);
		} else {
			final BoundConstraint bc = (BoundConstraint) atom;
			final LinVar var = bc.getVar();
			final boolean isUpper = literal.getSign() > 0;
			return createUnitClause(literal, isUpper, isUpper ? bc.getInverseBound() : bc.getBound(), var);
		}
	}

	private Clause generateEqualityClause(final Literal cclit) {
		final CCEquality cceq = (CCEquality) cclit.getAtom();
		Literal ea = cceq.getLASharedData();
		if (cceq == cclit) {
			ea = ea.negate();
		}
		return new Clause(new Literal[] { cclit, ea }, new LeafNode(LeafNode.EQ, EQAnnotation.EQ));
	}

	/**
	 * Create a new LiteralReason for a newly created and back-propagated literal
	 * and add the reason to the right position in the reason chain.
	 *
	 * @param var The variable that got a new literal
	 * @param lit The newly created literal that was inserted as propagated literal.
	 */
	private void insertReasonOfNewComposite(final LinVar var, final Literal lit) {
		final BoundConstraint bc = (BoundConstraint) lit.getAtom();
		final boolean isUpper = lit == bc;

		if (isUpper) {
			final InfinitesimalNumber bound = bc.getBound();
			// find reason where to insert into literal bound chain
			LiteralReason prevReason = null;
			LiteralReason nextReason = var.mUpperLiteral;
			while (nextReason != null && nextReason.getBound().less(bound)) {
				prevReason = nextReason;
				nextReason = nextReason.getOldLiteralReason();
			}
			final LiteralReason reason = new LiteralReason(var, nextReason, bound, true, lit);
			if (prevReason != null) {
				prevReason.setOldLiteralReason(reason);
			} else {
				var.mUpperLiteral = reason;
			}
			// insert reason into the reason chain
			if (bound.less(var.getExactUpperBound())) {
				reason.setOldReason(var.mUpper);
				var.mUpper = reason;
			} else {
				LAReason thereason = var.mUpper;
				while (thereason.getOldReason().getExactBound().less(bound)) {
					thereason = thereason.getOldReason();
				}
				assert (thereason.getExactBound().less(bound) && bound.less(thereason.getOldReason().getExactBound()));
				reason.setOldReason(thereason.getOldReason());
				thereason.setOldReason(reason);
			}
			if (var.outOfBounds()) {
				if (var.mBasic) {
					mOob.add(var);
				} else {
					updateVariableValue(var, new ExactInfinitesimalNumber(bound));
				}
			}
		} else {
			final InfinitesimalNumber bound = bc.getInverseBound();
			// find reason where to insert into literal bound chain
			LiteralReason prevReason = null;
			LiteralReason nextReason = var.mLowerLiteral;
			while (nextReason != null && bound.less(nextReason.getBound())) {
				prevReason = nextReason;
				nextReason = nextReason.getOldLiteralReason();
			}
			final LiteralReason reason = new LiteralReason(var, nextReason, bound, false, lit);
			if (prevReason != null) {
				prevReason.setOldLiteralReason(reason);
			} else {
				var.mLowerLiteral = reason;
			}
			// insert reason into the reason chain
			if (var.getExactLowerBound().less(bound)) {
				reason.setOldReason(var.mLower);
				var.mLower = reason;
			} else {
				LAReason thereason = var.mLower;
				while (bound.less(thereason.getOldReason().getExactBound())) {
					thereason = thereason.getOldReason();
				}
				assert (thereason.getOldReason().getExactBound().less(bound) && bound.less(thereason.getExactBound()));
				reason.setOldReason(thereason.getOldReason());
				thereason.setOldReason(reason);
			}
			if (var.outOfBounds()) {
				if (var.mBasic) {
					mOob.add(var);
				} else {
					updateVariableValue(var, new ExactInfinitesimalNumber(bound));
				}
			}
		}
	}

	private Clause setBound(LAReason reason) {
		final LinVar var = reason.getVar();
		InfinitesimalNumber bound = reason.getBound();
		final InfinitesimalNumber epsilon = var.getEpsilon();
		LiteralReason lastLiteral = reason.getLastLiteral();
		if (reason instanceof LiteralReason) {
			if (reason.isUpper()) {
				reason.getVar().mUpperLiteral = (LiteralReason) reason;
			} else {
				reason.getVar().mLowerLiteral = (LiteralReason) reason;
			}
		}
		if (reason.isUpper()) {
			// check if bound is stronger
			final InfinitesimalNumber oldBound = var.getTightUpperBound();
			assert reason.getExactBound().less(var.getExactUpperBound());
			reason.setOldReason(var.mUpper);
			var.mUpper = reason;

			// Propagate Disequalities
			LAEquality ea;
			while (bound.mEps == 0 && (ea = var.getDiseq(bound.mReal)) != null) {
				bound = bound.sub(epsilon);
				if (ea.getStackPosition() > lastLiteral.getStackPosition()) {
					lastLiteral = new LiteralReason(var, var.mUpperLiteral, bound, true, ea.negate());
					var.mUpper = var.mUpperLiteral = lastLiteral;
				} else {
					var.mUpper = var.mUpperLiteral = new LiteralReason(var, var.mUpperLiteral, bound, true, ea.negate(),
							lastLiteral);
					lastLiteral.addDependent(var.mUpper);
				}
				var.mUpper.setOldReason(reason);
				reason = var.mUpper;
			}

			if (!var.mBasic) {
				updateVariable(var, true, oldBound, bound);
			} else if (var.outOfBounds()) {
				mOob.add(var);
			}

			for (final BoundConstraint bc : var.mConstraints.subMap(bound, oldBound).values()) {
				assert var.getTightUpperBound().lesseq(bc.getBound());
				mProplist.add(bc);
			}
			for (final LAEquality laeq : var.mEqualities
					.subMap(bound.add(var.getEpsilon()), oldBound.add(var.getEpsilon())).values()) {
				mProplist.add(laeq.negate());
			}
		} else {
			// lower
			// check if bound is stronger
			final InfinitesimalNumber oldBound = var.getTightLowerBound();
			assert var.getExactLowerBound().less(reason.getExactBound());
			reason.setOldReason(var.mLower);
			var.mLower = reason;

			// Propagate Disequalities
			LAEquality ea;
			while (bound.mEps == 0 && (ea = var.getDiseq(bound.mReal)) != null) {
				bound = bound.add(epsilon);
				if (ea.getStackPosition() > lastLiteral.getStackPosition()) {
					lastLiteral = new LiteralReason(var, var.mLowerLiteral, bound, false, ea.negate());
					var.mLower = var.mLowerLiteral = lastLiteral;
				} else {
					var.mLower = var.mLowerLiteral = new LiteralReason(var, var.mLowerLiteral, bound, false,
							ea.negate(), lastLiteral);
					lastLiteral.addDependent(var.mLower);
				}
				var.mLower.setOldReason(reason);
				reason = var.mLower;
			}

			if (!var.mBasic) {
				updateVariable(var, false, oldBound, bound);
			} else if (var.outOfBounds()) {
				mOob.add(var);
			}

			for (final BoundConstraint bc : var.mConstraints.subMap(oldBound, bound).values()) {
				assert bc.getInverseBound().lesseq(var.getTightLowerBound());
				mProplist.add(bc.negate());
			}
			for (final LAEquality laeq : var.mEqualities.subMap(oldBound, bound).values()) {
				mProplist.add(laeq.negate());
			}
		}
		final InfinitesimalNumber ubound = var.getTightUpperBound();
		final InfinitesimalNumber lbound = var.getTightLowerBound();
		if (lbound.equals(ubound)) {
			final LAEquality lasd = var.mEqualities.get(lbound);
			if (lasd != null && lasd.getDecideStatus() == null) {
				mProplist.add(lasd);
			}
		} else if (ubound.less(lbound)) {
			// we have a conflict
			mConflictVar = var;
			return checkPendingConflict();
		}
		assert (var.mBasic || !var.outOfBounds());
		return null;
	}

	@Override
	public Clause setLiteral(final Literal literal) {
		Clause conflict = checkPendingBoundPropagations();
		if (conflict != null) {
			return conflict;
		}
		assert checkClean();
		if (mProplist.contains(literal.negate())) {
			return getUnitClause(literal.negate());
		}
		final DPLLAtom atom = literal.getAtom();
		if (atom instanceof LAEquality) {
			final LAEquality lasd = (LAEquality) atom;
			/* Propagate dependent atoms */
			for (final CCEquality eq : lasd.getDependentEqualities()) {
				if (eq.getDecideStatus() == null) {
					mProplist.add(literal == atom ? eq : eq.negate());
				} else if (eq.getDecideStatus().getSign() != literal.getSign()) {
					/* generate conflict */
					return generateEqualityClause(eq.getDecideStatus().negate());
				}
			}

			final LinVar var = lasd.getVar();
			final InfinitesimalNumber bound = new InfinitesimalNumber(lasd.getBound(), 0);
			if (literal.getSign() == 1) {
				// need to assert ea as upper and lower bound
				/*
				 * we need to take care of propagations: x = c ==> x <= c && x >= c should not
				 * propagate x <= c - k1 or x >= c + k2, but x <= c and x >= c
				 */
				if (mClausifier.getLogger().isDebugEnabled()) {
					mClausifier.getLogger().debug("Setting " + lasd.getVar() + " to " + lasd.getBound());
				}
				if (bound.less(var.getTightUpperBound())) {
					conflict = setBound(new LiteralReason(var, var.mUpperLiteral, bound, true, literal));
				}
				if (conflict != null) {
					return conflict;
				}
				if (var.getTightLowerBound().less(bound)) {
					conflict = setBound(new LiteralReason(var, var.mLowerLiteral, bound, false, literal));
				}
			} else {
				// Disequality constraint
				var.addDiseq(lasd);
				if (var.getTightUpperBound().equals(bound)) {
					conflict = setBound(
							new LiteralReason(var, var.mUpperLiteral, bound.sub(var.getEpsilon()), true, literal));
				} else if (var.getTightLowerBound().equals(bound)) {
					conflict = setBound(
							new LiteralReason(var, var.mLowerLiteral, bound.add(var.getEpsilon()), false, literal));
				}
			}
		} else if (atom instanceof BoundConstraint) {
			final BoundConstraint bc = (BoundConstraint) atom;
			final LinVar var = bc.getVar();
			// Check if the *exact* bound is refined and add this
			// literal as reason. This is even done, if we propagated the
			// literal. If there is already a composite with the
			// same bound, we still may use it later to explain the literal,
			// see LiteralReason.explain.
			if (literal == bc) {
				if (bc.getBound().less(var.getExactUpperBound())) {
					conflict = setBound(new LiteralReason(var, var.mUpperLiteral, bc.getBound(), true, literal));
				}
			} else {
				if (var.getExactLowerBound().less(bc.getInverseBound())) {
					conflict = setBound(
							new LiteralReason(var, var.mLowerLiteral, bc.getInverseBound(), false, literal));
				}
			}
		}
		assert (conflict != null || checkClean());
		return conflict;
	}

	public boolean checkPendingPropagation() {
		final Iterator<Literal> it = mProplist.iterator();
		while (it.hasNext()) {
			final Literal propLit = it.next();
			if (propLit.getAtom().getDecideStatus() == propLit) {
				it.remove();
			} else {
				return true;
			}
		}
		return false;
	}

	@Override
	public Clause checkpoint() {
		do {
			Clause conflict = checkPendingBoundPropagations();
			if (conflict != null) {
				return conflict;
			}
			if (checkPendingPropagation()) {
				return null;
			}
			// Prevent pivoting before tableau simplification
			if (!mInCheck) {
				return null;
			}
			conflict = fixOobs();
			if (conflict != null) {
				return conflict;
			}
		} while (!mDirty.isEmpty());
		return null;
	}

	public Rational realValue(final LinVar var) {
		if (mEps == null) {
			prepareModel();
		}
		final ExactInfinitesimalNumber value = var.getValue();
		return value.getRealValue().addmul(value.getEpsilon(), mEps);
	}

	public void dumpTableaux(final LogProxy logger) {
		for (final TableauxRow row : mTableaux) {
			if (row != null) {
				final StringBuilder sb = new StringBuilder();
				sb.append(row.getRawCoeff(0)).append('*').append(mLinvars.get(row.getRawIndex(0)));
				String comma = "";
				for (int i = 0; i < row.size(); i++) {
					sb.append(comma).append(row.getRawCoeff(i)).append('*').append(mLinvars.get(row.getRawIndex(i)));
					comma = " ; ";
				}
				logger.debug(sb.toString());
			}
		}
	}

	public void dumpConstraints(final LogProxy logger) {
		for (final LinVar var : mLinvars) {
			final StringBuilder sb = new StringBuilder();
			sb.append(var).append(var.mIsInt ? "[int]" : "[real]").append(": ");
			final InfinitesimalNumber lower = var.getLowerBound();
			if (lower != InfinitesimalNumber.NEGATIVE_INFINITY) {
				sb.append("lower: ").append(var.getLowerBound()).append(" <= ");
			}
			sb.append(var.getValue());
			final InfinitesimalNumber upper = var.getUpperBound();
			if (upper != InfinitesimalNumber.POSITIVE_INFINITY) {
				sb.append(" <= ").append(upper).append(" : upper");
			}
			logger.debug(sb);
		}
	}

	private void prepareModel() {
		/*
		 * Shortcut: If info log level is enabled we prepare the model to dump it as
		 * info message and later on when we have to produce a model. This work can be
		 * avoided.
		 */
		if (mEps != null) {
			return;
		}
		final TreeSet<Rational> prohibitions = new TreeSet<>();
		final InfinitesimalNumber maxeps = computeMaxEpsilon(prohibitions);
		if (maxeps == InfinitesimalNumber.POSITIVE_INFINITY) {
			mEps = Rational.ONE;
		} else {
			mEps = maxeps.inverse().ceil().mReal.inverse();
		}
		final Map<Rational, Set<ExactInfinitesimalNumber>> sharedPoints = new TreeMap<>();
		// Do not merge two shared variables that are not yet merged.
		final Map<ExactInfinitesimalNumber, List<LASharedTerm>> cong = getSharedCongruences();
		for (final ExactInfinitesimalNumber value : cong.keySet()) {
			final Rational eps = value.getEpsilon();
			Set<ExactInfinitesimalNumber> confl = sharedPoints.get(eps);
			if (confl == null) {
				confl = new TreeSet<>();
				sharedPoints.put(eps, confl);
			}
			confl.add(new ExactInfinitesimalNumber(value.getRealValue()));
		}
		// If we cannot choose the current value since we would violate a
		// disequality, choose a different number.
		while (prohibitions.contains(mEps) || hasSharing(sharedPoints, new ExactInfinitesimalNumber(mEps))) {
			mEps = mEps.inverse().add(Rational.ONE).inverse();
		}
	}

	@Override
	public void dumpModel(final LogProxy logger) {
		if (logger.isInfoEnabled()) {
			prepareModel();
			logger.info("Assignments:");
			for (final LinVar var : mLinvars) {
				if (!var.isInitiallyBasic()) {
					logger.info(var + " = " + realValue(var));
				}
			}
		}
	}

	@Override
	public void printStatistics(final LogProxy logger) {
		if (logger.isInfoEnabled()) {
			logger.info("Number of Bland pivoting-Operations: " + mNumPivotsBland + "/" + mNumPivots);
			int basicVars = 0;
			for (final LinVar var : mLinvars) {
				if (!var.isInitiallyBasic()) {
					basicVars++;
				}
			}
			logger.info("Number of variables: " + mLinvars.size() + " nonbasic: " + basicVars + " shared: "
					+ mSharedVars.size());
			logger.info("Time for fix Oob          : " + mFixTime / 1000000);
			logger.info("Time for pivoting         : " + mPivotTime / 1000000);
			logger.info("Time for bound computation: " + mPropBoundTime / 1000000);
			logger.info("Time for bound setting    : " + mPropBoundSetTime / 1000000);
			logger.info("Time for bound comp(back) : " + mBacktrackPropTime / 1000000);
			logger.info("Composite::createLit: " + mCompositeCreateLit);
			logger.info("Number of cuts: " + mNumCuts);
			logger.info("Time for cut-generation: " + mCutGenTime / 1000000);
			logger.info("Count/Time for getUpperBound: %d / %d.%03d", mCountGetUpperBound,
					mTimeGetUpperBound / 1000000000, mTimeGetUpperBound / 1000000 % 1000);
			logger.info("Number of branchings: " + mNumBranches);
		}
	}

	/**
	 * Pivot nonbasic versus basic variables along a coefficient. After calling
	 * this, you need to check for pending bound propagations.
	 *
	 * @param pivotEntry Coefficient specifying basic and nonbasic variable.
	 */
	final void pivot(final int rowMatrixPos, final int colMatrixPos) {
		++mNumPivots;
		long starttime;
		if (Config.PROFILE_TIME) {
			starttime = System.nanoTime();
		}
		final LinVar basic = mLinvars.get(rowMatrixPos);
		final LinVar nonbasic = mLinvars.get(colMatrixPos);
		final TableauxRow row = mTableaux.get(rowMatrixPos);
		if (mClausifier.getLogger().isDebugEnabled()) {
			mClausifier.getLogger().debug("pivot " + basic + " / " + nonbasic);
		}
		assert basic.mBasic;
		assert !nonbasic.mBasic;
		basic.mBasic = false;
		nonbasic.mBasic = true;

		// Adjust brp numbers
//		final BigInteger nbcoeff = row.getCoeffForPos(colMatrixPos);
//		final BigInteger bcoeff = row.getRawCoeff(0);
//		basic.updateUpperLowerClear(nbcoeff, nonbasic);
//		nonbasic.moveBounds(basic);
//		nonbasic.updateUpperLowerSet(bcoeff, basic);
		assert basic.checkCoeffChain(this);
		mTableaux.set(rowMatrixPos, null);
		row.swapRowCol(colMatrixPos);
		mTableaux.set(colMatrixPos, row);
		final BitSet todo = mDependentRows.set(colMatrixPos, null);
		mDependentRows.set(rowMatrixPos, new BitSet());
		for (int i = 1; i < row.size(); i++) {
			final BitSet dependencies = mDependentRows.get(row.getRawIndex(i));
			assert row.getRawIndex(i) == rowMatrixPos || dependencies.get(rowMatrixPos);
			dependencies.clear(rowMatrixPos);
			dependencies.set(colMatrixPos);
		}
		basic.mCachedRowVars = null;
		basic.mCachedRowCoeffs = null;

		mDirty.set(colMatrixPos);
		assert nonbasic.mCachedRowCoeffs == null;
		assert nonbasic.checkCoeffChain(this);

		todo.clear(rowMatrixPos);
		// Eliminate nonbasic from all equations
		while (!todo.isEmpty()) {
			final int rowIdx = todo.nextSetBit(0);
			final LinVar rowVar = mLinvars.get(rowIdx);
			todo.clear(rowIdx);
			mTableaux.get(rowIdx).addRow(this, row);
			rowVar.mCachedRowVars = null;
			rowVar.mCachedRowCoeffs = null;
			mDirty.set(rowVar.mMatrixpos);
			assert rowVar.checkCoeffChain(this);
		}
		if (Config.PROFILE_TIME) {
			mPivotTime += System.nanoTime() - starttime;
		}
		// mClausifier.getLogger().debug("Pivoting took " + (System.nanoTime() -
		// starttime));
	}

	/**
	 * Ensure that all integer variables have integral values.
	 *
	 * @return Conflict clause or <code>null</code> if formula is satisfiable.
	 */
	private Clause ensureIntegrals() {
		boolean isIntegral = true;
		for (final LinVar lv : mIntVars) {
			final ExactInfinitesimalNumber value = lv.getValue();
			if (!value.getRealValue().isIntegral() || !value.getEpsilon().equals(Rational.ZERO)) {
				isIntegral = false;
			}
		}
		if (isIntegral) {
			return null;
		}

		final LogProxy logger = mClausifier.getLogger();
		if (logger.isDebugEnabled()) {
			dumpTableaux(logger);
			dumpConstraints(logger);
		}

		// Satisfiable in the reals
		assert mOob.isEmpty();
		long start;
		if (Config.PROFILE_TIME) {
			start = System.nanoTime();
		}
		final CutCreator cutter = new CutCreator(this);
		cutter.generateCuts();
		if (Config.PROFILE_TIME) {
			mCutGenTime += System.nanoTime() - start;
		}
		Clause c = checkPendingConflict();
		if (c != null) {
			return c;
		}
		c = checkpoint();
		if (c != null) {
			return c;
		}
		return null;
	}

	/**
	 * Check whether all constraints can be satisfied. Here, we use the set of all
	 * variables outside their bounds. Rest of this algorithm is copied from
	 * original paper.
	 *
	 * If the formula is satisfiable, we additionally search for bound refinement
	 * propagations and calculate the values of all variables simplified out.
	 *
	 * @return Conflict clause or <code>null</code> if formula is satisfiable.
	 */
	@SuppressWarnings("unused")
	private Clause fixOobs() {
		long starttime;
		if (Config.PROFILE_TIME) {
			starttime = System.nanoTime();
		}

		boolean hasOob = false;
		for (final Iterator<LinVar> it = mOob.iterator(); it.hasNext();) {
			final LinVar var = it.next();
			if (var.outOfBounds()) {
				hasOob = true;
			} else {
				it.remove();
			}
		}
		if (!hasOob) {
			return null;
		}

		final Clause conflict = new SOIPivoter(this).fixOobs();
		if (conflict == null) {
			mOob.clear();
		}
		assert checkClean();
		assert !Config.EXPENSIVE_ASSERTS || checkoobcontent();
		if (Config.PROFILE_TIME) {
			mFixTime += System.nanoTime() - starttime;
		}
		return conflict;
	}

	/**
	 * Propagate all literals that are implied by the composite bounds computed from
	 * the current tableaux. This function creates a composite reason to remember
	 * why the bound was propagated and to explain the propagated literals later.
	 *
	 * @param basic   The variable on which literals are propagated
	 * @param bound   The new composite bound of the literal, computed from the
	 *                tableaux.
	 * @param isUpper True, if the bound is an upper bound for basic, false,
	 *                otherwise.
	 * @return A conflict clause if a conflict was found (one of the literals
	 *         already set with different polarity).
	 */
	private Clause propagateBound(final LinVar basic, final InfinitesimalNumber bound, final boolean isUpper) {
		long start;
		if (Config.PROFILE_TIME) {
			start = System.nanoTime();
		}
		if (isUpper ? bound.less(basic.getTightUpperBound()) : basic.getTightLowerBound().less(bound)) {
			final TableauxRow row = mTableaux.get(basic.mMatrixpos);
			final BigInteger denom = row.getRawCoeff(0).negate();

			LAReason[] reasons;
			Rational[] coeffs;
			LiteralReason lastLiteral = null;
			if (basic.mCachedRowCoeffs == null) {
				final int rowLength = row.size() - 1;
				final LinVar[] rowVars = new LinVar[rowLength];
				reasons = new LAReason[rowLength];
				coeffs = new Rational[rowLength];
				for (int i = 0; i < rowLength; i++) {
					final LinVar nb = mLinvars.get(row.getRawIndex(i + 1));
					final Rational coeff = Rational.valueOf(row.getRawCoeff(i + 1), denom);
					rowVars[i] = nb;
					reasons[i] = coeff.isNegative() == isUpper ? nb.mLowerLiteral : nb.mUpperLiteral;
					coeffs[i] = coeff;
					final LiteralReason lastOfThis = reasons[i].getLastLiteral();
					if (lastLiteral == null || lastOfThis.getStackPosition() > lastLiteral.getStackPosition()) {
						lastLiteral = lastOfThis;
					}
				}
				basic.mCachedRowCoeffs = coeffs;
				basic.mCachedRowVars = rowVars;
			} else {
				final LinVar[] rowVars = basic.mCachedRowVars;
				coeffs = basic.mCachedRowCoeffs;
				reasons = new LAReason[rowVars.length];
				for (int i = 0; i < rowVars.length; i++) {
					reasons[i] = coeffs[i].isNegative() == isUpper ? rowVars[i].mLowerLiteral
							: rowVars[i].mUpperLiteral;
					final LiteralReason lastOfThis = reasons[i].getLastLiteral();
					if (lastLiteral == null || lastOfThis.getStackPosition() > lastLiteral.getStackPosition()) {
						lastLiteral = lastOfThis;
					}
				}
			}
			final CompositeReason newComposite = new CompositeReason(basic, bound, isUpper, reasons, coeffs,
					lastLiteral);
			lastLiteral.addDependent(newComposite);
			long mid;
			if (Config.PROFILE_TIME) {
				mid = System.nanoTime();
				mPropBoundTime += mid - start;
			}
			final Clause conflict = setBound(newComposite);
			if (Config.PROFILE_TIME) {
				mPropBoundSetTime += System.nanoTime() - mid;
			}
			return conflict;
		}
		if (Config.PROFILE_TIME) {
			mPropBoundTime += System.nanoTime() - start;
		}
		return null;
	}

	/**
	 * Generate a bound constraint for a given variable. We use
	 * {@link BoundConstraint}s to represent bounds for variables and linear
	 * combination thereof. Those constraints are optimized to prevent strict bounds
	 * by manipulating the bounds.
	 *
	 * @param var          Variable to set bound on.
	 * @param bound        Bound to set on <code>var</code>.
	 * @param isLowerBound Is the bound a lower bound?
	 * @param strict       Is the bound strict?
	 * @return Constraint representing this bound.
	 */
	private Literal generateConstraint(final LinVar var, final Rational bound, final boolean isLowerBound,
			final boolean strict) {
		InfinitesimalNumber rbound = new InfinitesimalNumber(bound, (strict ^ isLowerBound) ? -1 : 0);
		if (var.isInt()) {
			rbound = rbound.floor();
		}
		return generateConstraint(var, rbound, isLowerBound);
	}

	private Literal generateConstraint(final LinVar var, final InfinitesimalNumber rbound, final boolean isLowerBound) {
		BoundConstraint bc = var.mConstraints.get(rbound);
		if (bc == null) {
			bc = new BoundConstraint(rbound, var, getEngine().getAssertionStackLevel());
			assert bc.mVar.checkCoeffChain(this);
			getEngine().addAtom(bc);
			if (var.getTightUpperBound().lesseq(rbound)) {
				mProplist.add(bc);
			}
			if (rbound.less(var.getTightLowerBound())) {
				mProplist.add(bc.negate());
			}
		}
		return isLowerBound ? bc.negate() : bc;
	}

	/**
	 * Remove a basic variable from the tableaux.
	 *
	 * @param v Basic variable to remove from the tableau.
	 */
	private void removeLinVar(final LinVar v) {
		if (!v.mBasic) {
			// We might have nonbasic variables that do not contribute to a basic variable.
			final BitSet dependencies = mDependentRows.get(v.mMatrixpos);
			if (!dependencies.isEmpty()) {
				final int row = dependencies.nextSetBit(0);
				pivot(row, v.mMatrixpos);
			}
		}
		assert v.mBasic || mDependentRows.get(v.mMatrixpos).isEmpty();
		assert v.mMatrixpos == mLinvars.size() - 1;
		mLinvars.remove(v.mMatrixpos);
		if (v.mBasic) {
			final TableauxRow row = mTableaux.get(v.mMatrixpos);
			for (int i = 1; i < row.size(); i++) {
				final LinVar col = mLinvars.get(row.getRawIndex(i));
				assert (!col.mBasic);
				mDependentRows.get(col.mMatrixpos).clear(v.mMatrixpos);
			}
		}
		mTableaux.remove(v.mMatrixpos);
		mDependentRows.remove(v.mMatrixpos);
	}

	/**
	 * Represents a linvar in terms of the current column (non-basic) variables and
	 * adds it to the map facs.
	 *
	 * @param lv   The variable to add.
	 * @param fac  The factor of the variable to add.
	 * @param facs The map, where to add it.
	 */
	private void unsimplifyAndAdd(final LinVar lv, final Rational fac, final Map<LinVar, Rational> facs) {
		if (lv.mBasic) {
			// currently basic variable
			final TableauxRow row = mTableaux.get(lv.mMatrixpos);
			final BigInteger denom = row.getRawCoeff(0).negate();
			for (int i = 1; i < row.size(); i++) {
				final Rational coeff = Rational.valueOf(row.getRawCoeff(i), denom);
				unsimplifyAndAdd(mLinvars.get(row.getRawIndex(i)), fac.mul(coeff), facs);
			}
		} else {
			// Just add it.
			final Rational oldval = facs.get(lv);
			if (oldval == null) {
				facs.put(lv, fac);
			} else {
				final Rational newval = oldval.add(fac);
				if (newval.equals(Rational.ZERO)) {
					facs.remove(lv);
				} else {
					facs.put(lv, newval);
				}
			}
		}
	}

	/**
	 * Compute freedom interval for a nonbasic variable.
	 *
	 * @param var Nonbasic variable to compute freedom interval for.
	 * @return the minimum and maximum amount the current nonbasic can be changed
	 *         without violating any bounds.
	 */
	private ExactInfinitesimalNumber[] freedom(final LinVar var) {
		final ExactInfinitesimalNumber value = var.getValue();
		ExactInfinitesimalNumber min = value.isub(var.getLowerBound());
		ExactInfinitesimalNumber max = value.isub(var.getUpperBound());
		for (final MatrixEntry me : var.getTableauxColumn(this)) {
			assert min.signum() <= 0 && max.signum() >= 0;
			final LinVar rowVar = me.getRow();
			final Rational coeff = Rational.valueOf(me.getHeadCoeff().negate(), me.getCoeff());
			final ExactInfinitesimalNumber rowvalue = rowVar.getValue();
			final ExactInfinitesimalNumber below = rowvalue.isub(rowVar.getLowerBound()).mul(coeff);
			final ExactInfinitesimalNumber above = rowvalue.isub(rowVar.getUpperBound()).mul(coeff);
			if (coeff.isNegative()) {
				// reverse orders
				assert below.signum() >= 0 && above.signum() <= 0;
				if (below.compareTo(max) < 0) {
					max = below;
				}
				if (above.compareTo(min) > 0) {
					min = above;
				}
			} else {
				assert below.signum() <= 0 && above.signum() >= 0;
				if (above.compareTo(max) < 0) {
					max = above;
				}
				if (below.compareTo(min) > 0) {
					min = below;
				}
			}
		}
		assert min.signum() <= 0 && max.signum() >= 0;
		return new ExactInfinitesimalNumber[] { min, max };
	}

	/**
	 * Mutate a model such that less variables have the same value.
	 *
	 * TODO This method is still very inefficient. Even if all variables have
	 * distinct values, we still compute a lot of stuff.
	 */
	private void mutate() {
		final Map<Rational, Set<ExactInfinitesimalNumber>> sharedPoints = new TreeMap<>();
		final Set<ExactInfinitesimalNumber> prohib = new TreeSet<>();
		for (final LinVar mutatingLV : mLinvars) {
			if (mutatingLV.mBasic || mutatingLV.getTightUpperBound().equals(mutatingLV.getTightLowerBound())) {
				// variable is basic or is fixed by its own constraints
				continue;
			}
			final ExactInfinitesimalNumber[] lowerupper = freedom(mutatingLV);
			if (lowerupper[0].equals(lowerupper[1])) {
				// variable is fixed by its own constraints and basic variables
				continue;
			}
			Rational gcd = mutatingLV.isInt() ? Rational.ONE : Rational.ZERO;
			final ExactInfinitesimalNumber exactval = mutatingLV.getValue();

			// prohib gives the differences that we should not choose as they cause a
			// disequality to not hold any more.
			// sharedPoints gives for each basic factor the current values of the shared
			// variables having that factor.
			// this allows us to quickly determine if we get a new shared conflict.
			sharedPoints.clear();
			prohib.clear();
			// prevent violating disequalities
			if (mutatingLV.mDisequalities != null) {
				for (final Rational diseq : mutatingLV.mDisequalities.keySet()) {
					prohib.add(new ExactInfinitesimalNumber(diseq).sub(exactval));
				}
			}

			// Iterate over basic variables
			final HashMap<LinVar, Rational> basicFactors = new HashMap<>();
			if (!mutatingLV.isInitiallyBasic()) {
				basicFactors.put(mutatingLV, Rational.ONE);
			}
			for (final MatrixEntry it1 : mutatingLV.getTableauxColumn(this)) {
				final LinVar basic = it1.getRow();
				final Rational coeff = Rational.valueOf(it1.getCoeff().negate(), it1.getHeadCoeff());
				if (!basic.isInitiallyBasic()) {
					basicFactors.put(basic, coeff);
				}
				if (basic.isInt()) {
					gcd = gcd.gcd(coeff.abs());
				}
				if (basic.mDisequalities != null) {
					for (final Rational diseq : basic.mDisequalities.keySet()) {
						final ExactInfinitesimalNumber basicval = basic.getValue();
						prohib.add(new ExactInfinitesimalNumber(diseq).sub(basicval).div(coeff));
					}
				}
			}

			// Do not merge two shared variables
			for (final LASharedTerm sharedVar : mSharedVars) {
				Rational sharedCoeff = Rational.ZERO;
				ExactInfinitesimalNumber sharedCurVal = new ExactInfinitesimalNumber(sharedVar.getOffset(),
						Rational.ZERO);
				for (final Entry<LinVar, Rational> entry : sharedVar.getSummands().entrySet()) {
					final LinVar lv = entry.getKey();
					final Rational factor = entry.getValue();
					if (basicFactors.containsKey(lv)) {
						sharedCoeff = sharedCoeff.addmul(basicFactors.get(lv), factor);
					}
					sharedCurVal = sharedCurVal.add(lv.getValue().mul(factor));
				}
				Set<ExactInfinitesimalNumber> set = sharedPoints.get(sharedCoeff);
				if (set == null) {
					set = new TreeSet<>();
					sharedPoints.put(sharedCoeff, set);
				}
				set.add(sharedCurVal);
			}
			// If there is no integer constraint for the non-basic manipulate
			// it by eps, otherwise incrementing by a multiple of gcd.inverse()
			// will preserve integrity of all depending variables.
			final Rational lcm = gcd.inverse();
			final ExactInfinitesimalNumber chosen = choose(lowerupper[0], lowerupper[1], prohib, sharedPoints, lcm);
			assert (chosen.compareTo(lowerupper[0]) >= 0 && chosen.compareTo(lowerupper[1]) <= 0);
			if (chosen.signum() != 0) {
				updateVariableValue(mutatingLV, mutatingLV.getValue().add(chosen));
			}
		}
	}

	/**
	 * Compute the value of each shared variable as exact infinite number.
	 *
	 * @return A map from the value to the list of shared variables that have this
	 *         value.
	 */
	Map<ExactInfinitesimalNumber, List<LASharedTerm>> getSharedCongruences() {
		mClausifier.getLogger().debug("Shared Vars:");
		final Map<ExactInfinitesimalNumber, List<LASharedTerm>> result = new HashMap<>();
		for (final LASharedTerm shared : mSharedVars) {
			ExactInfinitesimalNumber value = new ExactInfinitesimalNumber(shared.getOffset());
			for (final Entry<LinVar, Rational> entry : shared.getSummands().entrySet()) {
				final LinVar lv = entry.getKey();
				final Rational factor = entry.getValue();
				value = value.add(lv.getValue().mul(factor));
			}
			mClausifier.getLogger().debug("%s = %s", shared, value);
			List<LASharedTerm> slot = result.get(value);
			if (slot == null) {
				slot = new LinkedList<>();
				result.put(value, slot);
			}
			slot.add(shared);
		}
		return result;
	}

	private Literal ensureDisequality(final LAEquality eq) {
		final LinVar v = eq.getVar();
		assert (eq.getDecideStatus().getSign() == -1);
		final ExactInfinitesimalNumber value = v.getValue();
		// Disequality already satisfied...
		if (!value.getRealValue().equals(eq.getBound()) || value.getEpsilon().signum() != 0) {
			return null;
		}

		// Find already existing literal
		final InfinitesimalNumber bound = new InfinitesimalNumber(eq.getBound(), 0);
		final BoundConstraint gbc = eq.getVar().mConstraints.get(bound);
		final boolean usegt = gbc == null;
		if (!usegt && gbc.getDecideStatus() == null) {
			return gbc.negate();
		}
		final InfinitesimalNumber strictbound = bound.sub(eq.getVar().getEpsilon());
		final BoundConstraint lbc = eq.getVar().mConstraints.get(strictbound);
		if (lbc != null && lbc.getDecideStatus() == null) {
			return lbc;
		}
		// Here, we have neither inequality. Create one...
		return usegt ? generateConstraint(eq.getVar(), eq.getBound(), false, false).negate()
				: generateConstraint(eq.getVar(), eq.getBound(), false, true);
	}

	/**
	 * Choose a value from a given interval respecting certain prohibitions. The
	 * interval is given symbolically by a lower and an upper bound. All values
	 * prohibited are given in a set. Note that this set might also contain values
	 * outside the interval. For integer solutions, we also give the lcm such that
	 * we can generate an integer solution from an integer solution.
	 *
	 * If the interval is empty or no value can be found, the current value should
	 * be returned.
	 *
	 * @param lower        a negative value giving the maximum amount we can
	 *                     decrease the current non-basic value without violating a
	 *                     bound constraint.
	 * @param upper        a positive value giving the maximum amount we can
	 *                     increase the current non-basic value without violating a
	 *                     bound constraint.
	 * @param prohibitions Prohibited values. No difference that occurs in this set
	 *                     should be chosen.
	 * @param sharedPoints A map from shared term factors to current shared term
	 *                     values. The factor determines by how much the shared
	 *                     variable increases or decreases if current non-basic
	 *                     value is changed by one. We do not choose a difference
	 *                     that will create a new collision between shared
	 *                     variables.
	 * @param lcm          Least common multiple of denominators (integer only)
	 * @return The difference by which current non-basic value should be increased
	 *         (or decreased if negative).
	 */
	private ExactInfinitesimalNumber choose(final ExactInfinitesimalNumber lower, final ExactInfinitesimalNumber upper,
			final Set<ExactInfinitesimalNumber> prohibitions,
			final Map<Rational, Set<ExactInfinitesimalNumber>> sharedPoints, final Rational lcm) {
		// Check if variable is fixed or allowed.
		final ExactInfinitesimalNumber zero = ExactInfinitesimalNumber.ZERO;
		if (upper.equals(lower) || (!prohibitions.contains(zero) && !hasSharing(sharedPoints, zero))) {
			return zero;
		}

		if (lcm == Rational.POSITIVE_INFINITY) {
			// we have infinitely many values at our hand. Just iterate until we found a
			// solution
			// we only change epsilon values
			if (lower.getRealValue().equals(upper.getRealValue())) {
				// We can only change epsilons; we either choose as difference upper/2 or
				// lower/2 and half the
				// difference until we find a solution.
				ExactInfinitesimalNumber curDiff = (upper.signum() > 0 ? upper : lower).div(Rational.TWO);
				assert curDiff.signum() != 0 && lower.compareTo(curDiff) < 0 && curDiff.compareTo(upper) < 0;
				while (prohibitions.contains(curDiff) || hasSharing(sharedPoints, curDiff)) {
					curDiff = curDiff.div(Rational.TWO);
				}
				return curDiff;
			}
			// we have infinitely many epsilons slack either above or below current value.
			final ExactInfinitesimalNumber step;
			if (upper.getRealValue().signum() > 0) {
				// We search linear upwards from starting from the current value, incrementing
				// eps part by one
				step = new ExactInfinitesimalNumber(Rational.ZERO, Rational.ONE);
			} else {
				// We search linear downwards from starting from the current value, decrementing
				// eps part by one
				step = new ExactInfinitesimalNumber(Rational.ZERO, Rational.MONE);
			}
			ExactInfinitesimalNumber curDiff = step;
			while (prohibitions.contains(curDiff) || hasSharing(sharedPoints, curDiff)) {
				curDiff = curDiff.add(step);
			}
			return curDiff;
		} else {
			// This is the integer case (or a real variable on which an integer variable
			// depends).
			// We search upwards and downwards by incrementing and decrementing currentValue
			// by lcm.
			ExactInfinitesimalNumber up = new ExactInfinitesimalNumber(lcm);
			ExactInfinitesimalNumber down = up.negate();
			boolean searchUp = true;
			boolean searchDown = true;
			while (searchUp || searchDown) {
				if (searchUp) {
					if (up.compareTo(upper) > 0) {
						searchUp = false;
					} else {
						if (!prohibitions.contains(up) && !hasSharing(sharedPoints, up)) {
							return up;
						}
					}
					up = up.add(lcm);
				}
				if (searchDown) {
					if (down.compareTo(lower) < 0) {
						searchDown = false;
					} else {
						if (!prohibitions.contains(down) && !hasSharing(sharedPoints, down)) {
							return down;
						}
					}
					down = down.add(lcm.negate());
				}
			}
			return ExactInfinitesimalNumber.ZERO;
		}
	}

	/**
	 * Test for merging of at least two shared terms. Shared terms in our setting
	 * have form <code>c*x+o</code> for variable <code>x</code>. Given a map of
	 * <code>c</code> and the current value of <code>c*x+o</code>, and the desired
	 * difference, we check if two shared terms will be merged by this update.
	 *
	 * @param sharedPoints Map from slope to current value.
	 * @param diff         Expected difference.
	 * @return Did this difference merge two shared terms.
	 */
	private boolean hasSharing(final Map<Rational, Set<ExactInfinitesimalNumber>> sharedPoints,
			final ExactInfinitesimalNumber diff) {
		final TreeSet<ExactInfinitesimalNumber> used = new TreeSet<>();
		for (final Entry<Rational, Set<ExactInfinitesimalNumber>> entry : sharedPoints.entrySet()) {
			final ExactInfinitesimalNumber sharedDiff = diff.mul(entry.getKey());
			for (final ExactInfinitesimalNumber r : entry.getValue()) {
				if (!used.add(r.add(sharedDiff))) {
//					System.err.println("found sharing");
					return true;
				}
			}
		}
		return false;
	}

	private Clause mbtc(final Map<ExactInfinitesimalNumber, List<LASharedTerm>> cong) {
		for (final Map.Entry<ExactInfinitesimalNumber, List<LASharedTerm>> congclass : cong.entrySet()) {
			final List<LASharedTerm> lcongclass = congclass.getValue();
			if (lcongclass.size() <= 1) {
				continue;
			}
			mClausifier.getLogger().debug("propagating MBTC: %s", lcongclass);
			final Iterator<LASharedTerm> it = lcongclass.iterator();
			final LASharedTerm shared1 = it.next();
			LASharedTerm shared1OtherSort = null;
			while (it.hasNext()) {
				final LASharedTerm shared2 = it.next();
				final EqualityProxy eq;
				final CCEquality cceq;
				Term lhs = shared1.getTerm();
				final Term rhs = shared2.getTerm();
				if (lhs.getSort() != rhs.getSort()) {
					/*
					 * never merge terms of different sort. Note that mixed int/real equalities are
					 * translated to LA in the preprocessor.
					 *
					 * We need to remember this term in case there are more shared terms of this
					 * sort.
					 */
					if (shared1OtherSort == null) {
						shared1OtherSort = shared2;
						continue;
					} else {
						// only two numeric sorts supported
						lhs = shared1OtherSort.getTerm();
					}
				}
				assert lhs.getSort() == rhs.getSort();
				eq = mClausifier.createEqualityProxy(lhs, rhs, null);
				assert eq != EqualityProxy.getTrueProxy();
				assert eq != EqualityProxy.getFalseProxy();
				cceq = eq.createCCEquality(lhs, rhs);
				if (cceq.getLASharedData().getDecideStatus() != null) { // NOPMD
					if (cceq.getDecideStatus() == cceq.negate()) {
						return generateEqualityClause(cceq);
					} else if (cceq.getDecideStatus() == null) {
						mProplist.add(cceq);
					} else {
						mClausifier.getLogger().debug("already set: %s", cceq.getAtom().getDecideStatus());
					}
				} else {
					mClausifier.getLogger().debug("MBTC: Suggesting literal %s", cceq);
					mSuggestions.add(cceq.getLASharedData());
				}
			}
		}
		return null;
	}

	@Override
	public Literal getSuggestion() {
		Literal res;
		do {
			if (mSuggestions.isEmpty()) {
				return null;
			}
			res = mSuggestions.removeFirst();
		} while (res.getAtom().getDecideStatus() != null);
		return res;
	}

	private InfinitesimalNumber computeMaxEpsilon(final Set<Rational> prohibitions) {
		InfinitesimalNumber maxeps = InfinitesimalNumber.POSITIVE_INFINITY;
		for (final LinVar v : mLinvars) {
			final ExactInfinitesimalNumber value = v.getValue();
			if (value.getEpsilon().signum() > 0) {
				final InfinitesimalNumber diff = v.getUpperBound().sub(new InfinitesimalNumber(value.getRealValue(), 0))
						.div(value.getEpsilon());
				if (diff.compareTo(maxeps) < 0) {
					maxeps = diff;
				}
			} else if (value.getEpsilon().signum() < 0) {
				final InfinitesimalNumber diff = v.getLowerBound().sub(new InfinitesimalNumber(value.getRealValue(), 0))
						.div(value.getEpsilon());
				if (diff.compareTo(maxeps) < 0) {
					maxeps = diff;
				}
			}
			if (value.getEpsilon().signum() != 0 && v.mDisequalities != null) {
				for (final Rational prohib : v.mDisequalities.keySet()) {
					// solve v.mcurval = prohib to eps
					// a+b*eps = p ==> eps = (p-a)/b given b != 0
					prohibitions.add(prohib.sub(value.getRealValue()).div(value.getEpsilon()));
				}
			}
		}
		return maxeps;
	}

	@Override
	public void decreasedDecideLevel(final int currentDecideLevel) {
		// Nothing to do
	}

	@Override
	public void increasedDecideLevel(final int currentDecideLevel) {
		// Nothing to do
	}

	/**
	 * We reset the bounds and bound asserting members but not the current value
	 * since this might be a good start for the next iteration.
	 */
	@Override
	public void restart(final int iteration) {
		// Nothing to do
	}

	public LAEquality createEquality(final MutableAffineTerm at) {
		final Rational normFactor = at.getGCD().inverse();
		at.mul(normFactor);
		final LinVar var = generateLinVar(getSummandMap(at));
		InfinitesimalNumber bound;
		if (at.mSummands.size() == 1) {
			final Rational fac = at.mSummands.values().iterator().next();
			bound = at.mConstant.negate().div(fac);
		} else {
			bound = at.mConstant.negate();
		}
		assert bound.mEps == 0;
		LAEquality sharedData = var.getEquality(bound);
		if (sharedData == null) {
			sharedData = new LAEquality(mClausifier.getStackLevel(), var, bound.mReal);
			getEngine().addAtom(sharedData);
			var.addEquality(sharedData);
		}
		return sharedData;
	}

	@Override
	public Clause startCheck() {
		mEps = null;
		mInCheck = true;
		return null; // simplifyTableau();
	}

	@Override
	public void endCheck() {
		mInCheck = false;
	}

	public Literal createCompositeLiteral(final LAReason comp, final Literal beforeLit) {
		mCompositeCreateLit++;
		final int depth = comp.getLastLiteral().getDecideLevel();
		if (mClausifier.getLogger().isDebugEnabled()) {
			mClausifier.getLogger().debug("Create Propagated Literal for " + comp + " @ level " + depth);
		}
		final LinVar var = comp.getVar();
		InfinitesimalNumber bound = comp.getBound();
		if (!comp.isUpper()) {
			bound = bound.sub(var.getEpsilon());
		}
		final BoundConstraint bc = new BoundConstraint(bound, var, mClausifier.getStackLevel());
		final Literal lit = comp.isUpper() ? bc : bc.negate();
		final int decideLevel = comp.getLastLiteral().getDecideLevel();
		if (beforeLit != null && beforeLit.getAtom().getDecideLevel() == decideLevel) {
			getEngine().insertPropagatedLiteralBefore(this, lit, beforeLit);
		} else {
			getEngine().insertPropagatedLiteral(this, lit, decideLevel);
		}
		final InfinitesimalNumber litBound = comp.isUpper() ? bc.getBound() : bc.getInverseBound();
		if (!comp.getExactBound().equals(litBound)) {
			insertReasonOfNewComposite(var, lit);
		}

		return lit;
	}

	public void addSharedTerm(final LASharedTerm sharedTerm) {
		assert !mSharedVars.contains(sharedTerm);
		mSharedVars.add(sharedTerm);
		getLogger().info("LAShare %s", sharedTerm.getTerm());
	}

	@Override
	public void removeAtom(final DPLLAtom atom) {
		if (atom instanceof BoundConstraint) {
			final BoundConstraint bc = (BoundConstraint) atom;
			final LinVar v = bc.getVar();
			v.mConstraints.remove(bc.getBound());
		} else if (atom instanceof LAEquality) {
			final LAEquality laeq = (LAEquality) atom;
			final InfinitesimalNumber num = new InfinitesimalNumber(laeq.getBound(), 0);
			laeq.getVar().mEqualities.remove(num);
			for (final CCEquality eq : laeq.getDependentEqualities()) {
				eq.removeLASharedData();
			}
		}
	}

	@Override
	public void pop() {
		final int prevVarNum = mLinvars.getLastScopeSize();
		for (int i = mLinvars.size() - 1; i >= prevVarNum; i--) {
			final LinVar var = mLinvars.get(i);
			if (var == mConflictVar) {
				mConflictVar = null;
			}
			removeLinVar(var);
			mDirty.clear(i);
			mOob.remove(var);
			/// Mark variable as dead
			var.mAssertionstacklevel = -1;
			if (var.isInt()) {
				mIntVars.remove(var);
			}
		}
		if (mPushPopLevel == mHasNonLinearVar) {
			mHasNonLinearVar = -1;
		}
		mPushPopLevel--;
		mLinvars.endScope();
		mSharedVars.endScope();
		mBasics.endScope();
		// TODO This is a bit too much but should work
		mSuggestions.clear();
		mProplist.clear();
		assert popPost();
	}

	private final boolean popPost() {
		return true;
	}

	@Override
	public void push() {
		mBasics.beginScope();
		mSharedVars.beginScope();
		mLinvars.beginScope();
		mPushPopLevel++;
	}

	@Override
	public Object[] getStatistics() {
		return new Object[] { ":LA",
				new Object[][] { { "Pivot", mNumPivots }, { "PivotBland", mNumPivotsBland },
						{ "Vars", mLinvars.size() }, { "CompLits", mCompositeCreateLit }, { "Cuts", mNumCuts },
						{ "Branches", mNumBranches }, { "GetUpperBound", mCountGetUpperBound },
						{ "Times", new Object[][] { { "Pivot", mPivotTime / 1000000 }, { "Fix", mFixTime / 1000000 },
								{ "BoundComp", mPropBoundTime / 1000000 }, { "BoundSet", mPropBoundSetTime / 1000000 },
								{ "BoundBack", mBacktrackPropTime / 1000000 }, { "CutGen", mCutGenTime / 1000000 },
								{ "GetUpperBound", mTimeGetUpperBound / 1000000 } } } } };
	}

	/**
	 * Check whether the LA solver should fill in the value for this term. This is
	 * the case, if it is an ApplicationTerm corresponding to a 0-ary function.
	 *
	 * @param term Term to check.
	 * @return Symbol that gets a value from the LA solver.
	 */
	private FunctionSymbol getsValueFromLA(final Term term) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm at = (ApplicationTerm) term;
			if (at.getParameters().length == 0) {
				return at.getFunction();
			}
		}
		return null;
	}

	public void fillInModel(final Model model, final Theory t, final SharedTermEvaluator ste) {
		prepareModel();
		for (final LinVar var : mLinvars) {
			if (!var.isInitiallyBasic()) {
				final Term term = var.getTerm();
				final FunctionSymbol fsym = getsValueFromLA(term);
				if (fsym != null) {
					final Term value = realValue(var).toTerm(term.getSort());
					final NumericSortInterpretation si = (NumericSortInterpretation) model
							.provideSortInterpretation(term.getSort());
					si.register(value);
					model.map(fsym, value);
				}
			}
		}
	}

	/// --- Query partial model ---
	/**
	 * Return some upper bound for an smt affine term that is implied by the current
	 * model. This may return POSITIVE_INFINITY if no such upper bound is implied or
	 * if it is not obvious from the current state.
	 *
	 * @param clausifier The Clausifier used to convert terms to shared terms.
	 * @param smtTerm    The SMT affine term whose bound is to be determined.
	 * @return An infinitesimal number giving some implied upper bound. There is no
	 *         guarantee that it is the most strict implied bound.
	 */
	public InfinitesimalNumber getUpperBound(final MutableAffineTerm at) {
		final long start = System.nanoTime();
		mCountGetUpperBound++;
		if (at.isConstant()) {
			mTimeGetUpperBound += System.nanoTime() - start;
			return at.getConstant();
		}

		// get the linvar for the normalized mutable affine term
		final InfinitesimalNumber offset = at.getConstant();
		final Rational normFactor = at.getGCD();
		final MutableAffineTerm atNormalized = new MutableAffineTerm();
		atNormalized.add(normFactor.inverse(), at);
		final LinVar var = generateLinVar(atNormalized.getSummands());

		// check the bounds of the linvar
		final InfinitesimalNumber bound = normFactor.signum() > 0 ? var.getTightUpperBound() : var.getTightLowerBound();
		mTimeGetUpperBound += System.nanoTime() - start;
		return bound.mul(normFactor).add(offset);
	}
}
