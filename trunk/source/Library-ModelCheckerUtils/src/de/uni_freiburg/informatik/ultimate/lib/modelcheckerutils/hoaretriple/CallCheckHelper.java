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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateCoverageChecker;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;

class CallCheckHelper extends SdHoareTripleCheckHelper<ICallAction> {
	private static final String PRE_HIER_ERROR = "Unexpected hierarchical precondition for call action";

	CallCheckHelper(final IPredicateCoverageChecker coverage, final IPredicate falsePredicate,
			final IPredicate truePredicate, final HoareTripleCheckerStatisticsGenerator statistics,
			final ModifiableGlobalsTable modifiableGlobals) {
		super(coverage, falsePredicate, truePredicate, statistics, modifiableGlobals);
	}

	@Override
	public Validity sdecToFalse(final IPredicate pre, final IPredicate preHier, final ICallAction call) {
		assert preHier == null : PRE_HIER_ERROR;

		// If the precondition is e.g. (distinct x |old(x)|) for some non-modifiable x, the triple is valid.
		if (containsConflictingNonModifiableOldVars(call.getPrecedingProcedure(), pre)) {
			return null;
		}

		// TODO: there could be a contradiction if the Call is not a simple call
		// but interprocedural sequential composition

		mStatistics.getSDtfsCounter().incCa();
		return Validity.INVALID;
	}

	/**
	 * Returns true if p contains only non-old globals, or non-modifiable old variables.
	 */
	@Override
	public boolean isInductiveSelfloop(final IPredicate pre, final IPredicate preHier, final ICallAction call,
			final IPredicate post) {
		assert preHier == null : PRE_HIER_ERROR;
		if (pre != post) {
			return false;
		}

		final String caller = call.getPrecedingProcedure();
		for (final IProgramVar bv : pre.getVars()) {
			// If pre contains a local variable, the triple might be invalid, as local variables could be modified
			// (assigned or havoced) by the call.
			if (!bv.isGlobal()) {
				return false;
			}
			// Similarly, pre must also not contain any final old variables belonging to modifiable global variables, as
			// such old variables could also be modified by the call.
			if (bv.isOldvar() && mModifiableGlobals.isModifiable((IProgramOldVar) bv, caller)) {
				return false;
			}
		}

		// TODO Is this really enough? In particular, interprocedural compositions might assign global variables, right?
		// TODO So wouldn't it be better to examine the assigned variables of the transition formula?
		// TODO But do those contain ALL the modifications (params, local vars of caller and callee, old vars) ?

		mStatistics.getSDsluCounter().incCa();
		return true;
	}

	@Override
	public Validity sdec(final IPredicate pre, final IPredicate preHier, final ICallAction call,
			final IPredicate post) {
		assert preHier == null : PRE_HIER_ERROR;

		final var caller = call.getPrecedingProcedure();
		final var callee = call.getSucceedingProcedure();

		if (mModifiableGlobals.containsNonModifiableOldVars(pre, caller)
				|| mModifiableGlobals.containsNonModifiableOldVars(post, callee)) {
			return null;
		}

		if (!disjointFunctions(pre, post)) {
			// If pre and post both refer to the same constant (or function), the triple could be valid.
			return null;
		}

		for (final IProgramVar bv : post.getVars()) {
			if (bv.isOldvar()) {
				// If post contains old vars, e.g. post is (= x |old(x)|), the triple could be valid.
				// Unlike other cases, here it does not matter whether x is modifiable or not.
				return null;
			} else if (bv.isGlobal() && pre.getVars().contains(bv)) {
				return null;
			}
		}

		// workaround see preHierIndependent()
		final UnmodifiableTransFormula locVarAssignTf = call.getLocalVarsAssignment();
		if (!varsDisjointFromOutVars(pre, locVarAssignTf)) {
			return null;
		}
		// TODO: Matthias 7.10.2012 I hoped following would be sufficient. But this is not sufficient when constant
		// assigned to invar, e.g. post is x!=0 and call is x_Out=1. Might be solved with dataflow map.
		//
		// 8.10.2012 consider also case where inVar is non-modifiable global which does not occur in pre, but in post
		//
		// if (!varSetDisjoint(pre.getVars(), locVarAssignTf.getInVars().keySet())
		// && !varSetDisjoint(locVarAssignTf.getAssignedVars(), post.getVars())) {
		// return false;
		// }
		//
		// workaround for preceding problem
		if (!varsDisjointFromOutVars(post, locVarAssignTf)) {
			return null;
		}


		mStatistics.getSDsCounter().incCa();
		return Validity.INVALID;
	}

	@Override
	public Validity sdLazyEc(final IPredicate pre, final IPredicate preHier, final ICallAction call,
			final IPredicate post) {
		assert preHier == null : PRE_HIER_ERROR;

		if (isOrIteFormula(post)) {
			return sdec(pre, null, call, post);
		}

		final UnmodifiableTransFormula locVarAssignTf = call.getLocalVarsAssignment();
		final boolean argumentsRestrictedByPre = !varsDisjointFromInVars(pre, locVarAssignTf);
		for (final IProgramVar bv : post.getVars()) {
			if (bv.isGlobal()) {
				continue;
			}
			if (locVarAssignTf.getOutVars().keySet().contains(bv)) {
				if (argumentsRestrictedByPre) {
					continue;
				}
			}
			mStatistics.getSdLazyCounter().incCa();
			return Validity.INVALID;
		}
		return null;
	}
}