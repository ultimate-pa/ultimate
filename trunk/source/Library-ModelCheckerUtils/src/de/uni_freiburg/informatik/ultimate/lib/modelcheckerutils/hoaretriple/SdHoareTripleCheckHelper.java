/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2022 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple;

import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateCoverageChecker;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 * Abstract class for data-flow based Hoare triple checks. Subclasses are checks for internal, call, and return. Because
 * we can only override methods with the same signature (in Java) we use the 3-parameter-signature for return (with
 * hierarchical state) and use null as hierarchical state for call and internal.
 *
 * @param <L>
 *            The type of actions for which Hoare triples are checked.
 */
public abstract class SdHoareTripleCheckHelper<L extends IAction> {
	protected final IPredicateCoverageChecker mCoverage;
	protected final IPredicate mFalsePredicate;
	protected final IPredicate mTruePredicate;
	protected final HoareTripleCheckerStatisticsGenerator mStatistics;
	protected final ModifiableGlobalsTable mModifiableGlobals;

	/**
	 * @param sdHoareTripleChecker
	 */
	SdHoareTripleCheckHelper(final IPredicateCoverageChecker coverage, final IPredicate falsePredicate,
			final IPredicate truePredicate, final HoareTripleCheckerStatisticsGenerator statistics,
			final ModifiableGlobalsTable modifiableGlobals) {
		mCoverage = Objects.requireNonNull(coverage);
		mFalsePredicate = falsePredicate;
		mTruePredicate = truePredicate;
		mStatistics = statistics;
		mModifiableGlobals = modifiableGlobals;
	}

	public Validity check(final IPredicate preLin, final IPredicate preHier, final L act, final IPredicate succ) {
		if (act.getTransformula().isInfeasible() == Infeasibility.INFEASIBLE) {
			return Validity.VALID;
		}

		boolean unknownCoverage = false;

		// check if preLin is equivalent to false
		final Boolean isPreFalse = isCovered(preLin, mFalsePredicate);
		if (isPreFalse == null) {
			unknownCoverage = true;
		} else if (isPreFalse) {
			return Validity.VALID;
		}

		// check if preHier is equivalent to false
		if (preHier != null) {
			final Boolean isPreHierFalse = isCovered(preHier, mFalsePredicate);
			if (isPreHierFalse == null) {
				unknownCoverage = true;
			} else if (isPreHierFalse) {
				return Validity.VALID;
			}
		}

		// check if succ is equivalent to true
		final Boolean isSuccTrue = isCovered(mTruePredicate, succ);
		if (isSuccTrue == null) {
			unknownCoverage = true;
		} else if (isSuccTrue) {
			return Validity.VALID;
		}

		if (unknownCoverage) {
			return Validity.UNKNOWN;
		}

		final boolean isInductiveSelfloop = isInductiveSelfloop(preLin, preHier, act, succ);
		if (isInductiveSelfloop) {
			return Validity.VALID;
		}
		if (SmtUtils.isFalseLiteral(succ.getFormula())) {
			final Validity toFalse = sdecToFalse(preLin, preHier, act);
			if (toFalse == null) {
				// we are unable to determine validity with SD checks
				assert sdec(preLin, preHier, act, succ) == null : "inconsistent check results";
				return Validity.UNKNOWN;
			}
			switch (toFalse) {
			case INVALID:
				return Validity.INVALID;
			case NOT_CHECKED:
				throw new AssertionError("unchecked predicate");
			case UNKNOWN:
				throw new AssertionError("this case should have been filtered out before");
			case VALID:
				throw new AssertionError("this case should have been filtered out before");
			default:
				throw new AssertionError("unknown case");
			}
		}
		final Validity general;
		if (SdHoareTripleChecker.LAZY_CHECKS) {
			general = sdLazyEc(preLin, preHier, act, succ);
		} else {
			general = sdec(preLin, preHier, act, succ);
		}
		if (general != null) {
			switch (general) {
			case INVALID:
				return Validity.INVALID;
			case NOT_CHECKED:
				throw new AssertionError("unchecked predicate");
			case UNKNOWN:
				throw new AssertionError("this case should have been filtered out before");
			case VALID:
				return Validity.VALID;
			default:
				throw new AssertionError("unknown case");
			}
		}
		return Validity.UNKNOWN;
	}

	private Boolean isCovered(final IPredicate lhs, final IPredicate rhs) {
		switch (mCoverage.isCovered(lhs, rhs)) {
		case INVALID:
			return false;
		case NOT_CHECKED:
			throw new AssertionError("unchecked predicate");
		case UNKNOWN:
			return null;
		case VALID:
			return true;
		default:
			throw new AssertionError("unknown case");
		}
	}

	public abstract Validity sdecToFalse(IPredicate preLin, IPredicate preHier, L act);

	public abstract boolean isInductiveSelfloop(IPredicate preLin, IPredicate preHier, L act, IPredicate succ);

	public abstract Validity sdec(IPredicate preLin, IPredicate preHier, L act, IPredicate succ);

	public abstract Validity sdLazyEc(IPredicate preLin, IPredicate preHier, L act, IPredicate succ);

	protected static boolean varsDisjointFromInVars(final IPredicate state, final UnmodifiableTransFormula tf) {
		return DataStructureUtils.haveEmptyIntersection(state.getVars(), tf.getInVars().keySet());
	}

	protected static boolean varsDisjointFromAssignedVars(final IPredicate state, final UnmodifiableTransFormula tf) {
		return DataStructureUtils.haveEmptyIntersection(state.getVars(), tf.getAssignedVars());
	}

	protected static boolean disjointFunctions(final IPredicate state, final UnmodifiableTransFormula tf) {
		// TODO Use tf.getNonTheoryFunctions() once it is supported
		return DataStructureUtils.haveEmptyIntersection(state.getFuns(), (Set) tf.getNonTheoryConsts());
	}

	protected static boolean disjointFunctions(final IPredicate pred1, final IPredicate pred2) {
		return DataStructureUtils.haveEmptyIntersection(pred1.getFuns(), pred2.getFuns());
	}

	/**
	 * Checks if the predicate contains both a non-modifiable global variable x and old(x).
	 *
	 * In such cases, we can often not not give a verdict, because a formula such as (= x |old(x)|) always evaluates to
	 * true within the context of the procedure, but this is not detected by mCoverage (because it does not take
	 * procedure context into account). Similarly, a formula such as (distinct x |old(x)|) essentially behaves like it
	 * is inconsistent, but mCoverage does not detect this.
	 *
	 * @param proc
	 *            The procedure within which the predicate is evaluated
	 * @param p
	 *            The predicate to examine
	 * @return (as described above)
	 */
	protected boolean containsConflictingNonModifiableOldVars(final String proc, final IPredicate p) {
		for (final var pv : p.getVars()) {
			if (pv.isOldvar()) {
				final var pnov = ((IProgramOldVar) pv).getNonOldVar();
				if (!mModifiableGlobals.isModifiable(pnov, proc) && p.getVars().contains(pnov)) {
					return true;
				}
			}
		}
		return false;
	}

	/**
	 * Returns true if the formula of this predicate is an or-term or an ite-term.
	 */
	protected static boolean isOrIteFormula(final IPredicate p) {
		final Term formula = p.getFormula();
		if (formula instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) formula;
			final FunctionSymbol symbol = appTerm.getFunction();
			return "or".equals(symbol.getName()) || "ite".equals(symbol.getName());
		}
		return false;
	}

}