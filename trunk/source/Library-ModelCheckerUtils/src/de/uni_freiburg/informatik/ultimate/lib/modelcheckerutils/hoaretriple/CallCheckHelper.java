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

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateCoverageChecker;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;

class CallCheckHelper extends SdHoareTripleCheckHelper {
	private static final String PRE_HIER_ERROR = "Unexpected hierarchical precondition for call action";

	CallCheckHelper(final IPredicateCoverageChecker coverage, final IPredicate falsePredicate,
			final IPredicate truePredicate, final HoareTripleCheckerStatisticsGenerator statistics,
			final ModifiableGlobalsTable modifiableGlobals) {
		super(coverage, falsePredicate, truePredicate, statistics, modifiableGlobals);
	}

	@Override
	public Validity sdecToFalse(final IPredicate preLin, final IPredicate preHier, final IAction act) {
		assert preHier == null : PRE_HIER_ERROR;
		// TODO: there could be a contradiction if the Call is not a simple call
		// but interprocedural sequential composition
		mStatistics.getSDtfsCounter().incCa();
		return Validity.INVALID;
	}

	/**
	 * Returns UNSAT if p contains only non-old globals.
	 */
	@Override
	public boolean isInductiveSelfloop(final IPredicate pre, final IPredicate preHier, final IAction act,
			final IPredicate post) {
		assert preHier == null : PRE_HIER_ERROR;
		if (pre != post) {
			return false;
		}

		for (final IProgramVar bv : pre.getVars()) {
			if (!bv.isGlobal()) {
				return false;
			}
			if (bv.isOldvar()) {
				return false;
			}
		}
		mStatistics.getSDsluCounter().incCa();
		return true;
	}

	@Override
	public Validity sdec(final IPredicate pre, final IPredicate preHier, final IAction act, final IPredicate post) {
		assert preHier == null : PRE_HIER_ERROR;

		if (mModifiableGlobalVariableManager.containsNonModifiableOldVars(pre, act.getPrecedingProcedure())
				|| mModifiableGlobalVariableManager.containsNonModifiableOldVars(post, act.getSucceedingProcedure())) {
			return null;
		}
		for (final IProgramVar bv : post.getVars()) {
			if (bv.isOldvar()) {
				// if oldVar occurs this edge might be inductive since
				// old(g)=g is true
				return null;
			}
			if (bv.isGlobal()) {
				assert !bv.isOldvar();
				if (pre.getVars().contains(bv)) {
					return null;
				}
			}
		}

		// workaround see preHierIndependent()
		final var call = (ICallAction) act;
		final UnmodifiableTransFormula locVarAssignTf = call.getLocalVarsAssignment();
		if (!varsDisjointFromAssignedVars(pre, locVarAssignTf)) {
			return null;
		}
		if (preHierIndependent(post, pre, call.getLocalVarsAssignment(), act.getSucceedingProcedure())) {
			mStatistics.getSDsCounter().incCa();
			return Validity.INVALID;
		}
		return null;
	}

	@Override
	public Validity sdLazyEc(final IPredicate pre, final IPredicate preHier, final IAction act, final IPredicate post) {
		assert preHier == null : PRE_HIER_ERROR;

		if (isOrIteFormula(post)) {
			return sdec(pre, null, act, post);
		}

		final var call = (ICallAction) act;
		final UnmodifiableTransFormula locVarAssignTf = call.getLocalVarsAssignment();
		final boolean argumentsRestrictedByPre = !varsDisjointFromInVars(pre, locVarAssignTf);
		for (final IProgramVar bv : post.getVars()) {
			if (bv.isGlobal()) {
				continue;
			}
			if (locVarAssignTf.getAssignedVars().contains(bv)) {
				if (argumentsRestrictedByPre) {
					continue;
				}
			}
			mStatistics.getSdLazyCounter().incCa();
			return Validity.INVALID;
		}
		return null;
	}

	private boolean preHierIndependent(final IPredicate pre, final IPredicate hier,
			final UnmodifiableTransFormula localVarsAssignment, final String calledProcedure) {
		// TODO: Matthias 7.10.2012 I hoped following would be sufficient.
		// But this is not sufficient when constant assigned to invar
		// e.g. pre is x!=0 and call is x_Out=1. Might be solved with
		// dataflow map.
		// 8.10.2012 consider also case where inVar is non-modifiable global
		// which does not occur in hier, but in pre
		// if (!varSetDisjoint(hier.getVars(), locVarAssignTf.getInVars().keySet())
		// && !varSetDisjoint(locVarAssignTf.getAssignedVars(), pre.getVars())) {
		// return false;
		// }
		// workaround for preceding problem
		if (!varsDisjointFromAssignedVars(pre, localVarsAssignment)) {
			return false;
		}

		// cases where pre and hier share non-modifiable var g, or
		// g occurs in hier, and old(g) occurs in pre.
		final Set<IProgramNonOldVar> modifiableGlobals =
				mModifiableGlobalVariableManager.getModifiedBoogieVars(calledProcedure);

		for (final IProgramVar bv : pre.getVars()) {
			if (bv.isGlobal()) {
				if (bv.isOldvar()) {
					if (hier.getVars().contains(((IProgramOldVar) bv).getNonOldVar())) {
						return false;
					}
				} else if (!modifiableGlobals.contains(bv) && hier.getVars().contains(bv)) {
					return false;
				}
			}
		}
		return true;
	}
}