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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateCoverageChecker;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;

public class ReturnCheckHelper extends SdHoareTripleCheckHelper<IReturnAction> {
	ReturnCheckHelper(final IPredicateCoverageChecker coverage, final IPredicate falsePredicate,
			final IPredicate truePredicate, final HoareTripleCheckerStatisticsGenerator statistics,
			final ModifiableGlobalsTable modifiableGlobals) {
		super(coverage, falsePredicate, truePredicate, statistics, modifiableGlobals);
	}

	@Override
	public Validity sdecToFalse(final IPredicate preLin, final IPredicate preHier, final IReturnAction ret) {
		if (preHierNotFalse(preLin, preHier, ret.getLocalVarsAssignmentOfCall(), ret.getPrecedingProcedure())) {
			mStatistics.getSDtfsCounter().incRe();
			return Validity.INVALID;
		}
		return null;
	}

	@Override
	public boolean isInductiveSelfloop(final IPredicate preLin, final IPredicate preHier, final IReturnAction ret,
			final IPredicate succ) {
		if (preLin == succ && sdecReturnSelfloopPre(preLin, ret) == Validity.VALID) {
			return true;
		}
		return preHier == succ && sdecReturnSelfloopHier(preHier, ret) == Validity.VALID;
	}

	private Validity sdecReturnSelfloopPre(final IPredicate p, final IReturnAction ret) {
		final Set<IProgramVar> assignedVars = ret.getAssignmentOfReturn().getOutVars().keySet();
		for (final IProgramVar bv : p.getVars()) {
			if (!bv.isGlobal()) {
				return null;
			}
			if (bv.isOldvar()) {
				return null;
			}
			if (assignedVars.contains(bv)) {
				return null;
			}
		}
		mStatistics.getSDsluCounter().incRe();
		return Validity.VALID;
	}

	private Validity sdecReturnSelfloopHier(final IPredicate p, final IReturnAction ret) {
		final Set<IProgramVar> assignedVars = ret.getAssignmentOfReturn().getOutVars().keySet();
		final String proc = ret.getPrecedingProcedure();
		final Set<IProgramNonOldVar> modifiableGlobals = mModifiableGlobals.getModifiedBoogieVars(proc);

		for (final IProgramVar bv : p.getVars()) {
			if (modifiableGlobals.contains(bv)) {
				return null;
			}
			if (assignedVars.contains(bv)) {
				return null;
			}
		}
		return Validity.VALID;
	}

	@Override
	public Validity sdec(final IPredicate preLin, final IPredicate preHier, final IReturnAction ret,
			final IPredicate post) {
		if (mModifiableGlobals.containsNonModifiableOldVars(preLin, ret.getPrecedingProcedure())
				|| mModifiableGlobals.containsNonModifiableOldVars(preHier, ret.getSucceedingProcedure())
				|| mModifiableGlobals.containsNonModifiableOldVars(post, ret.getSucceedingProcedure())) {
			return null;
		}
		if (hierPostIndependent(preHier, ret, post)
				&& preHierNotFalse(preLin, preHier, ret.getLocalVarsAssignmentOfCall(), ret.getPrecedingProcedure())
				&& prePostIndependent(preLin, ret, post)) {
			mStatistics.getSDsCounter().incRe();
			return Validity.INVALID;

		}
		return null;
	}

	@Override
	public Validity sdLazyEc(final IPredicate preLin, final IPredicate preHier, final IReturnAction ret,
			final IPredicate post) {
		if (isOrIteFormula(post)) {
			return sdec(preLin, preHier, ret, post);
		}

		/*
		 * Old Version. Does not work if param set to constant.
		 *
		 * // If there is an argument in post which is not assigned by return // and an parameter is in pre we have to
		 * return UNKNOWN Map<BoogieVar, TermVariable> arguments = call.getTransitionFormula().getInVars();
		 * Set<BoogieVar> parameters = call.getTransitionFormula().getAssignedVars(); if (!varSetDisjoint(parameters,
		 * pre.getVars())) { for (BoogieVar bv : arguments.keySet()) { if (post.getVars().contains(bv) &&
		 * !assignedVars.contains(bv)) { mLazyEdgeCheckQueries++; return null; } } }
		 *
		 */
		if (!varsDisjointFromOutVars(preLin, ret.getLocalVarsAssignmentOfCall())) {
			return null;
		}

		final String proc = ret.getPrecedingProcedure();
		final Set<IProgramNonOldVar> modifiableGlobals = mModifiableGlobals.getModifiedBoogieVars(proc);
		final boolean assignedVarsRestrictedByPre = !varsDisjointFromInVars(preLin, ret.getAssignmentOfReturn());
		final Set<IProgramVar> assignedVars = ret.getAssignmentOfReturn().getOutVars().keySet();
		for (final IProgramVar bv : post.getVars()) {
			if (!continueSdLazyEcReturnLoop(bv, modifiableGlobals, preHier, preLin, assignedVars,
					assignedVarsRestrictedByPre)) {
				mStatistics.getSdLazyCounter().incRe();
				return Validity.INVALID;
			}
		}
		return null;
	}

	private static boolean continueSdLazyEcReturnLoop(final IProgramVar bv,
			final Set<IProgramNonOldVar> modifiableGlobals, final IPredicate hier, final IPredicate pre,
			final Set<IProgramVar> assignedVars, final boolean assignedVarsRestrictedByPre) {
		if (bv.isGlobal()) {
			if (bv.isOldvar()) {
				if (hier.getVars().contains(bv)) {
					return true;
				}
			} else {
				if (modifiableGlobals.contains(bv)) {
					if (pre.getVars().contains(bv)) {
						return true;
					}
				} else {
					if (hier.getVars().contains(bv)) {
						return true;
					}
					if (pre.getVars().contains(bv)) {
						return true;
					}
				}
				if (assignedVars.contains(bv) && assignedVarsRestrictedByPre) {
					return true;
				}
			}

		} else if (assignedVars.contains(bv)) {
			if (assignedVarsRestrictedByPre) {
				return true;
			}
		} else if (hier.getVars().contains(bv)) {
			return true;
		}
		return false;
	}

	private boolean preHierNotFalse(final IPredicate pre, final IPredicate hier,
			final UnmodifiableTransFormula localVarsAssignment, final String calledProcedure) {

		// pre hier not connected via call
		// local in disjoint or local out disjoint
		// not if pre contains old and global in hier or localVarsAssignment
		// or not modifiable and hier contains oldvar
		final Set<IProgramNonOldVar> modifiableGlobals = mModifiableGlobals.getModifiedBoogieVars(calledProcedure);
		final boolean isSelfConnectedViaLocalVarsAssignment =
				isSelfConnectedViaLocalVarsAssignment(pre, localVarsAssignment);
		if (isSelfConnectedViaLocalVarsAssignment) {
			return false;
		}
		final boolean isConnectedViaLocalVarsAssignment =
				isConnectedViaLocalVarsAssignment(hier, localVarsAssignment, pre);
		if (isConnectedViaLocalVarsAssignment) {
			return false;
		}
		final Validity preImpliesHier = mCoverage.isCovered(pre, hier);
		final boolean canBeCrossConnectedViaGlobalVars =
				canBeCrossConnectedViaGlobalVars(hier, pre, modifiableGlobals, preImpliesHier == Validity.VALID);
		if (canBeCrossConnectedViaGlobalVars) {
			return false;
		}
		if (preImpliesHier == Validity.VALID) {
			return true;
		}
		return disjointOnNonModifiableGlobals(hier, pre, modifiableGlobals);
	}

	/**
	 * Example1: hier: g = 5 returnPred: old(g) = 7 both predicates are "crosslinked" because old(g) callee and g of
	 * caller coincide
	 *
	 * Example1: hier: g = 5 returnPred: g = 7 Special case of "crosslinking" if g is not modifiable by callee if
	 * returnPred implies hier, crosslinking is not dangerous (proof sketch: hier contained in returnPred, intersection
	 * cannot be empty, if we have non-modifiables returnPred becomes only smaller, non-modifiables of returnPred are
	 * non-modifiables of hier)
	 *
	 */
	private static boolean canBeCrossConnectedViaGlobalVars(final IPredicate hier, final IPredicate returnPred,
			final Set<IProgramNonOldVar> modifiableGlobals, final boolean returnPredImpliesHier) {
		for (final IProgramVar pv : returnPred.getVars()) {
			if (pv instanceof IProgramOldVar) {
				final IProgramNonOldVar nonOld = ((IProgramOldVar) pv).getNonOldVar();
				if (hier.getVars().contains(nonOld)) {
					return true;
				}
				if (!returnPredImpliesHier && !modifiableGlobals.contains(nonOld)) {
					// there is some risk that pv is also not modifiable by
					// caller and then the oldvar of the caller coincides
					// with the global var of the caller
					if (hier.getVars().contains(pv)) {
						return true;
					}
				}
			} else if (pv instanceof IProgramNonOldVar) {
				if (!returnPredImpliesHier && !modifiableGlobals.contains(pv)) {
					if (hier.getVars().contains(pv)) {
						return true;
					}
					final IProgramOldVar oldVar = ((IProgramNonOldVar) pv).getOldVar();
					// there is some risk that pv is also not modifiable by
					// caller and then the oldvar of the caller coincides
					// with the global var of the caller
					if (hier.getVars().contains(oldVar)) {
						return true;
					}
				}
			}
		}
		return false;
	}

	private static boolean disjointOnNonModifiableGlobals(final IPredicate hier, final IPredicate returnPred,
			final Set<IProgramNonOldVar> modifiableGlobals) {
		for (final IProgramVar pv : returnPred.getVars()) {
			if (pv instanceof IProgramNonOldVar && !modifiableGlobals.contains(pv) && hier.getVars().contains(pv)) {
				return false;
			}
		}
		return true;
	}

	private static boolean isConnectedViaLocalVarsAssignment(final IPredicate hier,
			final UnmodifiableTransFormula localVarsAssignment, final IPredicate returnPred) {
		return !varsDisjointFromOutVars(returnPred, localVarsAssignment)
				&& !varsDisjointFromInVars(hier, localVarsAssignment);
	}

	/**
	 * E.g., returnPred: x != 1 localVarsAssignment x := 1
	 */
	private static boolean isSelfConnectedViaLocalVarsAssignment(final IPredicate returnPred,
			final UnmodifiableTransFormula localVarsAssignment) {
		return !varsDisjointFromOutVars(returnPred, localVarsAssignment);
	}

	private static boolean prePostIndependent(final IPredicate pre, final IReturnAction ret, final IPredicate post) {
		final UnmodifiableTransFormula returnAssignTf = ret.getAssignmentOfReturn();
		if (!varsDisjointFromInVars(pre, returnAssignTf) && !varsDisjointFromOutVars(post, returnAssignTf)) {
			return false;
		}
		final UnmodifiableTransFormula locVarAssignTf = ret.getLocalVarsAssignmentOfCall();
		if (!varsDisjointFromInVars(post, locVarAssignTf) && !varsDisjointFromOutVars(pre, locVarAssignTf)) {
			return false;
		}
		for (final IProgramVar bv : pre.getVars()) {
			if (bv.isGlobal() && !bv.isOldvar()) {
				if (post.getVars().contains(bv)) {
					return false;
				}
			}
		}
		return true;
	}

	private boolean hierPostIndependent(final IPredicate hier, final IReturnAction ret, final IPredicate post) {
		final Set<IProgramVar> assignedVars = ret.getAssignmentOfReturn().getOutVars().keySet();

		final String proc = ret.getPrecedingProcedure();
		final Set<IProgramNonOldVar> modifiableGlobals = mModifiableGlobals.getModifiedBoogieVars(proc);

		for (final IProgramVar bv : post.getVars()) {
			if (modifiableGlobals.contains(bv)) {
				// do nothing
				continue;
			}
			if (assignedVars.contains(bv)) {
				// do nothing
				continue;
			}
			if (hier.getVars().contains(bv)) {
				return false;
			}
		}
		return true;
	}
}