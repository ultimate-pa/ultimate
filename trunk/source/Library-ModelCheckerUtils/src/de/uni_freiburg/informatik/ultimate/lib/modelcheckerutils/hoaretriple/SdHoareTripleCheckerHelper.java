/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateCoverageChecker;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.IncrementalPlicationChecker.Validity;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

@Deprecated
public class SdHoareTripleCheckerHelper {

	private final ModifiableGlobalsTable mModifiableGlobalVariableManager;

	private final HoareTripleCheckerStatisticsGenerator mHoareTripleCheckerStatistics;
	private final IPredicateCoverageChecker mPredicateCoverageChecker;

	public SdHoareTripleCheckerHelper(final CfgSmtToolkit csToolkit,
			final IPredicateCoverageChecker predicateCoverageChecker,
			final HoareTripleCheckerStatisticsGenerator edgeCheckerBenchmarkGenerator) {
		mModifiableGlobalVariableManager = csToolkit.getModifiableGlobalsTable();
		mPredicateCoverageChecker = predicateCoverageChecker;
		if (edgeCheckerBenchmarkGenerator == null) {
			mHoareTripleCheckerStatistics = new HoareTripleCheckerStatisticsGenerator();
		} else {
			mHoareTripleCheckerStatistics = edgeCheckerBenchmarkGenerator;
		}
	}

	public HoareTripleCheckerStatisticsGenerator getEdgeCheckerBenchmark() {
		return mHoareTripleCheckerStatistics;
	}

	private static boolean varSetDisjoint(final Set<IProgramVar> set1, final Set<IProgramVar> set2) {
		return DataStructureUtils.haveEmptyIntersection(set1, set2);
	}

	/**
	 * Returns true iff the variables occurring in state are disjoint from the inVars of CodeBlock letter.
	 *
	 * @param state
	 * @param symbol
	 * @return
	 */
	private static boolean varsDisjointFromInVars(final IPredicate state, final UnmodifiableTransFormula tf) {
		return DataStructureUtils.haveEmptyIntersection(state.getVars(), tf.getInVars().keySet());
	}

	public Validity sdecReturn(final IPredicate pre, final IPredicate hier, final IReturnAction ret,
			final IPredicate post) {
		if (mModifiableGlobalVariableManager.containsNonModifiableOldVars(pre, ret.getPrecedingProcedure())
				|| mModifiableGlobalVariableManager.containsNonModifiableOldVars(hier, ret.getSucceedingProcedure())
				|| mModifiableGlobalVariableManager.containsNonModifiableOldVars(post, ret.getSucceedingProcedure())) {
			return null;
		}
		if (hierPostIndependent(hier, ret, post)
				&& preHierNotFalse(pre, hier, ret.getLocalVarsAssignmentOfCall(), ret.getPrecedingProcedure())
				&& prePostIndependent(pre, ret, post)) {
			mHoareTripleCheckerStatistics.getSDsCounter().incRe();
			return Validity.INVALID;

		}
		return null;
	}

	public Validity sdecReturnToFalse(final IPredicate pre, final IPredicate hier, final IReturnAction ret) {
		if (preHierNotFalse(pre, hier, ret.getLocalVarsAssignmentOfCall(), ret.getPrecedingProcedure())) {
			mHoareTripleCheckerStatistics.getSDtfsCounter().incRe();
			return Validity.INVALID;

		}
		return null;
	}

	public Validity sdLazyEcReturn(final IPredicate pre, final IPredicate hier, final IReturnAction ret,
			final IPredicate post) {
		if (isOrIteFormula(post)) {
			return sdecReturn(pre, hier, ret, post);
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
		final Set<IProgramVar> parameters = ret.getLocalVarsAssignmentOfCall().getAssignedVars();
		if (!varSetDisjoint(parameters, pre.getVars())) {
			return null;
		}

		final String proc = ret.getPrecedingProcedure();
		final Set<IProgramNonOldVar> modifiableGlobals = mModifiableGlobalVariableManager.getModifiedBoogieVars(proc);
		final boolean assignedVarsRestrictedByPre =
				!varSetDisjoint(ret.getAssignmentOfReturn().getInVars().keySet(), pre.getVars());
		final Set<IProgramVar> assignedVars = ret.getAssignmentOfReturn().getAssignedVars();
		for (final IProgramVar bv : post.getVars()) {
			if (!continueSdLazyEcReturnLoop(bv, modifiableGlobals, hier, pre, assignedVars,
					assignedVarsRestrictedByPre)) {
				mHoareTripleCheckerStatistics.getSdLazyCounter().incRe();
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
		final Set<IProgramNonOldVar> modifiableGlobals =
				mModifiableGlobalVariableManager.getModifiedBoogieVars(calledProcedure);
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
		final Validity preImpliesHier = mPredicateCoverageChecker.isCovered(pre, hier);
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

	private static boolean disjointOnNonModifiableGlobals(final IPredicate hier, final IPredicate returnPred,
			final Set<IProgramNonOldVar> modifiableGlobals) {
		for (final IProgramVar pv : returnPred.getVars()) {
			if (pv instanceof IProgramNonOldVar && !modifiableGlobals.contains(pv) && hier.getVars().contains(pv)) {
				return false;
			}
		}
		return true;
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

	private static boolean isConnectedViaLocalVarsAssignment(final IPredicate hier,
			final UnmodifiableTransFormula localVarsAssignment, final IPredicate returnPred) {
		return !varSetDisjoint(localVarsAssignment.getAssignedVars(), returnPred.getVars())
				&& !varsDisjointFromInVars(hier, localVarsAssignment);
	}

	/**
	 * E.g., returnPred: x != 1 localVarsAssignment x := 1
	 */
	private static boolean isSelfConnectedViaLocalVarsAssignment(final IPredicate returnPred,
			final UnmodifiableTransFormula localVarsAssignment) {
		return !varSetDisjoint(localVarsAssignment.getAssignedVars(), returnPred.getVars());
	}

	private static boolean prePostIndependent(final IPredicate pre, final IReturnAction ret, final IPredicate post) {
		final UnmodifiableTransFormula returnAssignTf = ret.getAssignmentOfReturn();
		if (!varSetDisjoint(pre.getVars(), returnAssignTf.getInVars().keySet())
				&& !varSetDisjoint(returnAssignTf.getAssignedVars(), post.getVars())) {
			return false;
		}
		final UnmodifiableTransFormula locVarAssignTf = ret.getLocalVarsAssignmentOfCall();
		if (!varSetDisjoint(post.getVars(), locVarAssignTf.getInVars().keySet())
				&& !varSetDisjoint(locVarAssignTf.getAssignedVars(), pre.getVars())) {
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
		final Set<IProgramVar> assignedVars = ret.getAssignmentOfReturn().getAssignedVars();

		final String proc = ret.getPrecedingProcedure();
		final Set<IProgramNonOldVar> modifiableGlobals = mModifiableGlobalVariableManager.getModifiedBoogieVars(proc);

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

	public Validity sdecReturnSelfloopPre(final IPredicate p, final IReturnAction ret) {
		final Set<IProgramVar> assignedVars = ret.getAssignmentOfReturn().getAssignedVars();
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
		mHoareTripleCheckerStatistics.getSDsluCounter().incRe();
		return Validity.VALID;
	}

	public Validity sdecReturnSelfloopHier(final IPredicate p, final IReturnAction ret) {
		final Set<IProgramVar> assignedVars = ret.getAssignmentOfReturn().getAssignedVars();
		final String proc = ret.getPrecedingProcedure();
		final Set<IProgramNonOldVar> modifiableGlobals = mModifiableGlobalVariableManager.getModifiedBoogieVars(proc);

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

	/**
	 * Returns true if the formula of this predicate is an or-term or an ite-term.
	 */
	@Deprecated
	private static boolean isOrIteFormula(final IPredicate p) {
		final Term formula = p.getFormula();
		if (formula instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) formula;
			final FunctionSymbol symbol = appTerm.getFunction();
			return "or".equals(symbol.getName()) || "ite".equals(symbol.getName());
		}
		return false;
	}
}
