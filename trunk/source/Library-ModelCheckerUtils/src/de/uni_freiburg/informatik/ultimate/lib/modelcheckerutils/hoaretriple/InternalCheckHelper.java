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

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgForkThreadOtherTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgJoinThreadOtherTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateCoverageChecker;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

class InternalCheckHelper extends SdHoareTripleCheckHelper {
	InternalCheckHelper(final IPredicateCoverageChecker coverage, final IPredicate falsePredicate,
			final IPredicate truePredicate, final HoareTripleCheckerStatisticsGenerator statistics) {
		super(coverage, falsePredicate, truePredicate, statistics);
	}

	/**
	 * Idea: If the formula of the code block is satisfiable, the predecessor is satisfiable and the vars of predecessor
	 * are disjoint from the inVars of the code block, then a transition to false is not inductive. Idea with UNKNOWN:
	 * if the solver was unable to decide feasibility of cb, the predecessor is satisfiable and the vars of predecessor
	 * are disjoint from the inVars of the code block, then the solver will be unable to show that a transition to false
	 * is inductive.
	 *
	 * FIXME: Check for precondition false, not for precondition true.
	 */
	@Override
	public Validity sdecToFalse(final IPredicate preLin, final IPredicate preHier, final IAction act) {
		assert preHier == null;
		final Infeasibility infeasiblity = act.getTransformula().isInfeasible();
		if (infeasiblity == Infeasibility.UNPROVEABLE) {
			if (varsDisjointFromInVars(preLin, act.getTransformula())
					&& act.getTransformula().getNonTheoryConsts().isEmpty()) {
				mStatistics.getSDtfsCounter().incIn();
				return Validity.INVALID;
			}
			return null;
		}
		if (infeasiblity == Infeasibility.INFEASIBLE) {
			return Validity.VALID;
		}
		if (infeasiblity == Infeasibility.NOT_DETERMINED) {
			return null;
		}
		throw new IllegalArgumentException();
	}

	/**
	 * If the assigned vars of cb are disjoint from the variables in p the selfloop (p,cb,p) is trivially inductive.
	 * Returns HTTV.VALID if selfloop is inductive. Returns null if we are not able to determine inductivity selfloop.
	 */
	@Override
	public boolean isInductiveSelfloop(final IPredicate preLin, final IPredicate preHier, final IAction act,
			final IPredicate succ) {
		assert preHier == null;
		if (preLin != succ) {
			return false;
		}

		final Set<IProgramVar> assignedVars = act.getTransformula().getAssignedVars();
		final Set<IProgramVar> occVars = preLin.getVars();
		for (final IProgramVar occVar : occVars) {
			if (assignedVars.contains(occVar)) {
				return false;
			}
		}
		mStatistics.getSDsluCounter().incIn();
		return true;
	}

	/**
	 * FIXME: Mention assumptions. Idea: If
	 * <ul>
	 * <li>the formula of the code block is satisfiable,
	 * <li>the predecessor is satisfiable,
	 * <li>the successor is not unsatisfiable,
	 * <li>the variables of the predecessor are disjoint from the invars of the code block, and
	 * <li>the variables of the successor are disjoint from the outvars of the code block, from the invars of the code
	 * block and from the vars of the predecessor,
	 * </ul>
	 * then a transition (pre, act, post) is not inductive.
	 *
	 * FIXME: Check for preconditions, postcondition?
	 */
	@Override
	public Validity sdec(final IPredicate preLin, final IPredicate preHier, final IAction act, final IPredicate succ) {
		assert preHier == null;

		final UnmodifiableTransFormula tf = act.getTransformula();

		// If pre implies post, and act does not modify any variable in pre, then the Hoare triple is valid.
		if (mCoverage.isCovered(preLin, succ) == Validity.VALID
				&& DataStructureUtils.haveEmptyIntersection(preLin.getVars(), tf.getAssignedVars())) {
			mStatistics.getSDsluCounter().incIn();
			return Validity.VALID;
		}

		// TODO Why no check for pre and outVars?
		if (DataStructureUtils.haveNonEmptyIntersection(preLin.getVars(), tf.getInVars().keySet())
				|| DataStructureUtils.haveNonEmptyIntersection(succ.getVars(), tf.getInVars().keySet())
				|| DataStructureUtils.haveNonEmptyIntersection(succ.getVars(), tf.getOutVars().keySet())) {
			return null;
		}

		if (!tf.getNonTheoryConsts().isEmpty()) {
			// TODO We could instead check if tf has any constants in common with pre or post.
			// However, this requires IAbstractPredicate::getConstants to be supported.
			return null;
		}

		// Now, we know that the variables of pre and post are both disjoint from the variables of act, and act does not
		// constrain the value of any program constants.
		// Hence the Hoare triple is valid iff pre implies post.
		final Validity sat = mCoverage.isCovered(preLin, succ);
		if (sat == Validity.VALID) {
			mStatistics.getSDsluCounter().incIn();
			return Validity.VALID;
		}
		if (sat == Validity.UNKNOWN) {
			return null;
		}
		if (sat == Validity.NOT_CHECKED) {
			return null;
		}
		if (sat == Validity.INVALID) {
			final String proc = act.getPrecedingProcedure();
			assert proc.equals(act.getSucceedingProcedure()) || act instanceof IcfgForkThreadOtherTransition
					|| act instanceof IcfgJoinThreadOtherTransition : "internal statement must not change procedure";

			// TODO Commented out per discussion with Matthias. Run tests to see effects, then delete.
			// if (mModifiableGlobalVariableManager.containsNonModifiableOldVars(preLin, proc)
			// || mModifiableGlobalVariableManager.containsNonModifiableOldVars(succ, proc)) {
			// return null;
			// }
			// // continue and return Validity.INVALID
		}

		mStatistics.getSDsCounter().incIn();
		switch (act.getTransformula().isInfeasible()) {
		case INFEASIBLE:
			throw new IllegalArgumentException("case should have been handled before");
		case NOT_DETERMINED:
			return null;
		case UNPROVEABLE:
			// FIXME: only invalid if feasibility of transformula proven
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
	@Override
	public Validity sdLazyEc(final IPredicate preLin, final IPredicate preHier, final IAction act,
			final IPredicate succ) {
		assert preHier == null;
		if (SdHoareTripleCheckerHelper.isOrIteFormula(succ)) {
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
}