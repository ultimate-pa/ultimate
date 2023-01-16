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

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadOther;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadOther;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateCoverageChecker;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;

/**
 * Implements simple dataflow-based Hoare triple checks for internal actions.
 *
 * This class is only meant for internal usage by {@link SdHoareTripleChecker}.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
class InternalCheckHelper extends SdHoareTripleCheckHelper<IInternalAction> {
	private static final String PRE_HIER_ERROR = "Unexpected hierarchical precondition for internal action";

	InternalCheckHelper(final IPredicateCoverageChecker coverage, final IPredicate falsePredicate,
			final IPredicate truePredicate, final HoareTripleCheckerStatisticsGenerator statistics,
			final ModifiableGlobalsTable modifiableGlobals) {
		super(coverage, falsePredicate, truePredicate, statistics, modifiableGlobals);
	}

	/**
	 * This method handles 2 cases of Hoare triples where the postcondition is "false":
	 *
	 * 1. If the action is infeasible, the Hoare triple is valid.
	 *
	 * 2. If the action is feasible, and does not constrain any variables or constants mentioned in pre, then the Hoare
	 * triple is invalid.
	 */
	@Override
	public Validity sdecToFalse(final IPredicate pre, final IPredicate preHier, final IInternalAction act) {
		assert preHier == null : PRE_HIER_ERROR;
		final var tf = act.getTransformula();

		switch (tf.isInfeasible()) {
		case INFEASIBLE:
			return Validity.VALID;
		case UNPROVEABLE:
			if (varsDisjointFromInVars(pre, tf) && disjointFunctions(pre, tf)
					&& !containsConflictingNonModifiableOldVars(act.getPrecedingProcedure(), pre)) {
				mStatistics.getSDtfsCounter().incIn();
				return Validity.INVALID;
			}
			return null;
		case NOT_DETERMINED:
			return null;
		}
		throw new IllegalArgumentException();
	}

	/**
	 * If pre- and postcondition are equal, and the assigned variables of the action are disjoint from the variables in
	 * the pre/postcondition, the Hoare triple is trivially valid.
	 */
	@Override
	public boolean isInductiveSelfloop(final IPredicate preLin, final IPredicate preHier, final IInternalAction act,
			final IPredicate succ) {
		assert preHier == null : PRE_HIER_ERROR;
		if (preLin != succ) {
			return false;
		}

		if (varsDisjointFromAssignedVars(preLin, act.getTransformula())) {
			mStatistics.getSDsluCounter().incIn();
			return true;
		}
		return false;
	}

	/**
	 * This method essentially handles 2 cases:
	 *
	 * 1. If pre implies post, and no relevant variables are modified by the action, then the Hoare triple is valid.
	 *
	 * 2. If pre does not imply post, pre and post do not constrain the variables and constants read or assigned by the
	 * action, and the action is feasible, then the Hoare triple is invalid.
	 *
	 * The method assumes that the given action is not marked as infeasible.
	 *
	 * {@inheritDoc}
	 */
	@Override
	public Validity sdec(final IPredicate pre, final IPredicate preHier, final IInternalAction act,
			final IPredicate post) {
		assert preHier == null : PRE_HIER_ERROR;

		final UnmodifiableTransFormula tf = act.getTransformula();

		// TODO In the presence of axioms, we have to check (pre /\ axiom |= post).
		final Validity preImpliesPost = mCoverage.isCovered(pre, post);
		switch (preImpliesPost) {
		case VALID:
			// If pre implies post, and act does not modify any variable in pre, then the Hoare triple is valid.
			// Similarly, if act does not modify any variable in post, the Hoare triple is also valid.
			if (varsDisjointFromAssignedVars(pre, tf) || varsDisjointFromAssignedVars(post, tf)) {
				mStatistics.getSDsluCounter().incIn();
				return Validity.VALID;
			}
			return null;
		case INVALID:
			// continue below
			break;
		case UNKNOWN:
		case NOT_CHECKED:
			return null;
		default:
			throw new AssertionError("illegal value");
		}

		if (!varsDisjointFromInVars(pre, tf) || !varsDisjointFromInVars(post, tf)
				|| !varsDisjointFromAssignedVars(post, tf)) {
			return null;
		}

		if (!disjointFunctions(pre, tf) || !disjointFunctions(post, tf)) {
			return null;
		}

		// The lines below address a special case that is relevant for e.g., the following example. Let's assume that x
		// is a global variable, pre is `x = 42`, post is `old(x) = 42`, and the action represents an `assume true`
		// statement. Hence, all variables are disjoint, pre does not imply post, and at a first glance it seems like
		// the Hoare triple is invalid. If however the preceding and succeeding procedure of the action does not have
		// `x` in its modifies clause, we consider the Hoare triple to be valid.
		final String proc = act.getPrecedingProcedure();
		if (!proc.equals(act.getSucceedingProcedure())) {
			assert act instanceof IIcfgForkTransitionThreadOther<?>
					|| act instanceof IIcfgJoinTransitionThreadOther<?> : "internal statement must not change procedure";
			// Unclear what we can do for fork and join statements.
			return null;
		}
		if (containsConflictingNonModifiableOldVars(proc, pre, post)
				|| containsConflictingNonModifiableOldVars(proc, pre)
				|| containsConflictingNonModifiableOldVars(proc, post)) {
			return null;
		}

		// We know that the variables of pre and post are both disjoint from the variables of act, and act does not
		// constrain the value of any program constants. Thus, if act is feasible, the Hoare triple must be invalid.
		// TODO In the presence of axioms, we need feasibility modulo the axioms.
		switch (act.getTransformula().isInfeasible()) {
		case INFEASIBLE:
			throw new IllegalArgumentException("case should have been handled before");
		case NOT_DETERMINED:
			return null;
		case UNPROVEABLE:
			// FIXME only invalid if feasibility of transformula proven
			mStatistics.getSDsCounter().incIn();
			return Validity.INVALID;
		default:
			throw new AssertionError("illegal value");
		}
	}

	/**
	 * FIXME 20210810 Matthias: Bad name: "incomplete" would be better than "lazy". Idea: If succedent of implication
	 * does (in NNF) not contain a disjunction and contains some variable that does not occur in the antecedent the
	 * implication does not hold very often.
	 */
	@Deprecated
	@Override
	public Validity sdLazyEc(final IPredicate preLin, final IPredicate preHier, final IInternalAction act,
			final IPredicate succ) {
		assert preHier == null : PRE_HIER_ERROR;
		if (isOrIteFormula(succ)) {
			return sdec(preLin, null, act, succ);
		}
		for (final IProgramVar bv : succ.getVars()) {
			if (!preLin.getVars().contains(bv) || !act.getTransformula().getInVars().containsKey(bv)
					|| !act.getTransformula().getOutVars().containsKey(bv)) {
				// occurs neither in pre not in codeBlock, probably unsat
				mStatistics.getSdLazyCounter().incIn();
				return Validity.INVALID;
			}
		}
		return null;
	}

	// Checks if one predicate contains a non-modifiable global variable x and the other contains old(x).
	private boolean containsConflictingNonModifiableOldVars(final String proc, final IPredicate p1,
			final IPredicate p2) {
		for (final var pv : p1.getVars()) {
			if (pv instanceof IProgramOldVar) {
				final var pnov = ((IProgramOldVar) pv).getNonOldVar();
				if (!mModifiableGlobals.isModifiable(pnov, proc) && p2.getVars().contains(pnov)) {
					return true;
				}
			} else if (pv instanceof IProgramNonOldVar) {
				final var pnov = (IProgramNonOldVar) pv;
				if (!mModifiableGlobals.isModifiable(pnov, proc) && p2.getVars().contains(pnov.getOldVar())) {
					return true;
				}
			}
		}

		return false;
	}
}