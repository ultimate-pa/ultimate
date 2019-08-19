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

import java.util.Collections;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgForkThreadOtherTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgJoinThreadOtherTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateCoverageChecker;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;

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

	public SdHoareTripleCheckerHelper(final CfgSmtToolkit csToolkit,
			final HoareTripleCheckerStatisticsGenerator edgeCheckerBenchmarkGenerator) {
		this(csToolkit, null, edgeCheckerBenchmarkGenerator);
	}

	public HoareTripleCheckerStatisticsGenerator getEdgeCheckerBenchmark() {
		return mHoareTripleCheckerStatistics;
	}

	private static boolean varSetDisjoint(final Set<IProgramVar> set1, final Set<IProgramVar> set2) {
		if (set1.size() < set2.size()) {
			for (final IProgramVar bv : set1) {
				if (set2.contains(bv)) {
					return false;
				}
			}
		} else {
			for (final IProgramVar bv : set2) {
				if (set1.contains(bv)) {
					return false;
				}
			}
		}
		return true;
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
	public Validity sdecInternalToFalse(final IPredicate pre, final IInternalAction act) {
		final Infeasibility infeasiblity = act.getTransformula().isInfeasible();
		if (infeasiblity == Infeasibility.UNPROVEABLE) {
			if (varsDisjoinedFormInVars(pre, act.getTransformula())) {
				mHoareTripleCheckerStatistics.getSDtfsCounter().incIn();
				return Validity.INVALID;
			}
			return null;
		} else if (infeasiblity == Infeasibility.INFEASIBLE) {
			return Validity.VALID;
		} else if (infeasiblity == Infeasibility.NOT_DETERMINED) {
			return null;
		} else {
			throw new IllegalArgumentException();
		}
	}

	/**
	 * Returns true iff the variables occurring in state are disjoint from the inVars of CodeBlock letter.
	 *
	 * @param state
	 * @param symbol
	 * @return
	 */
	private static boolean varsDisjoinedFormInVars(final IPredicate state, final UnmodifiableTransFormula tf) {
		for (final IProgramVar bv : state.getVars()) {
			if (tf.getInVars().containsKey(bv)) {
				return false;
			}
		}
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
	 * FIXME: Check for preconditions, postcondition? Check at least for infeasibility flag of TransFormula.
	 */
	public Validity sdecInteral(final IPredicate pre, final IInternalAction act, final IPredicate post) {
		if (mPredicateCoverageChecker != null) {
			final Validity sat = mPredicateCoverageChecker.isCovered(pre, post);
			if (sat == Validity.VALID) {
				if (Collections.disjoint(pre.getVars(), act.getTransformula().getAssignedVars())) {
					mHoareTripleCheckerStatistics.getSDsluCounter().incIn();
					return Validity.VALID;
				}
			}
		}
		for (final IProgramVar bv : pre.getVars()) {
			if (act.getTransformula().getInVars().containsKey(bv)) {
				return null;
			}
		}
		for (final IProgramVar bv : post.getVars()) {
			// if (pre.getVars().contains(bv)) {
			// return null;
			// } else
			if (act.getTransformula().getInVars().containsKey(bv)) {
				return null;
			} else if (act.getTransformula().getOutVars().containsKey(bv)) {
				return null;
			}
		}
		// now, we know that vars of pre and post are both disjoint from the
		/// vars of cb. Edge is inductive iff pre implies post
		if (mPredicateCoverageChecker != null) {
			final Validity sat = mPredicateCoverageChecker.isCovered(pre, post);
			if (sat == Validity.VALID) {
				mHoareTripleCheckerStatistics.getSDsluCounter().incIn();
				return Validity.VALID;
			} else if (sat == Validity.UNKNOWN) {
				return null;
			} else if (sat == Validity.NOT_CHECKED) {
				return null;
			} else if (sat == Validity.INVALID) {
				final String proc = act.getPrecedingProcedure();
				assert proc.equals(act.getSucceedingProcedure()) || act instanceof IcfgForkThreadOtherTransition
						|| act instanceof IcfgJoinThreadOtherTransition : "internal statement must not change procedure";
				if (mModifiableGlobalVariableManager.containsNonModifiableOldVars(pre, proc)
						|| mModifiableGlobalVariableManager.containsNonModifiableOldVars(post, proc)) {
					return null;
				}
				// continue and return Validity.INVALID
			}
		} else {
			if (!Collections.disjoint(pre.getVars(), post.getVars())) {
				return null;
			}
		}
		mHoareTripleCheckerStatistics.getSDsCounter().incIn();
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

	// public boolean sdecSatAssured(Predicate pre, CodeBlock cb) {
	// Set<BoogieVar> inVars = cb.getTransitionFormula().getInVars().keySet();
	// if (varSetDisjoint(pre.getVars(), inVars)) {
	// return true;
	// }
	// else return false;
	// }

	public Validity sdLazyEcInteral(final IPredicate pre, final IInternalAction act, final IPredicate post) {
		if (isOrIteFormula(post)) {
			return sdecInteral(pre, act, post);
		}
		for (final IProgramVar bv : post.getVars()) {
			if (!pre.getVars().contains(bv) || !act.getTransformula().getInVars().containsKey(bv)
					|| !act.getTransformula().getOutVars().containsKey(bv)) {
				// occurs neither in pre not in codeBlock, probably unsat
				mHoareTripleCheckerStatistics.getSdLazyCounter().incIn();
				return Validity.INVALID;
			}
		}
		return null;
	}

	public Validity sdecCallToFalse(final IPredicate pre, final ICallAction act) {
		// TODO:
		// there could be a contradiction if the Call is not a simple call
		// but interprocedural sequential composition
		mHoareTripleCheckerStatistics.getSDtfsCounter().incCa();
		return Validity.INVALID;
	}

	public Validity sdecCall(final IPredicate pre, final ICallAction act, final IPredicate post) {
		for (final IProgramVar bv : post.getVars()) {
			if (bv.isOldvar()) {
				// if oldVar occurs this edge might be inductive since
				// old(g)=g is true
				return null;
			} else if (bv.isGlobal()) {
				assert !bv.isOldvar();
				if (pre.getVars().contains(bv)) {
					return null;
				}
			}
		}
		// workaround see preHierIndependent()
		final UnmodifiableTransFormula locVarAssignTf = act.getLocalVarsAssignment();
		if (!varSetDisjoint(locVarAssignTf.getAssignedVars(), pre.getVars())) {
			return null;
		}
		if (preHierIndependent(post, pre, act.getLocalVarsAssignment(), act.getSucceedingProcedure())) {
			mHoareTripleCheckerStatistics.getSDsCounter().incCa();
			return Validity.INVALID;
		}
		return null;
	}

	public Validity sdLazyEcCall(final IPredicate pre, final ICallAction cb, final IPredicate post) {
		if (isOrIteFormula(post)) {
			return sdecCall(pre, cb, post);
		}
		final UnmodifiableTransFormula locVarAssignTf = cb.getLocalVarsAssignment();
		final boolean argumentsRestrictedByPre = !varSetDisjoint(locVarAssignTf.getInVars().keySet(), pre.getVars());
		for (final IProgramVar bv : post.getVars()) {
			if (bv.isGlobal()) {
				continue;
			}
			if (locVarAssignTf.getAssignedVars().contains(bv)) {
				if (argumentsRestrictedByPre) {
					continue;
				}
			}
			mHoareTripleCheckerStatistics.getSdLazyCounter().incCa();
			return Validity.INVALID;
		}
		return null;
	}

	public Validity sdecReturn(final IPredicate pre, final IPredicate hier, final IReturnAction ret,
			final IPredicate post) {
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
		final Set<IProgramVar> assignedVars = ret.getAssignmentOfReturn().getAssignedVars();

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

		} else {
			if (assignedVars.contains(bv)) {
				if (assignedVarsRestrictedByPre) {
					return true;
				}
			} else if (hier.getVars().contains(bv)) {
				return true;
			}
		}
		return false;
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
		if (!varSetDisjoint(localVarsAssignment.getAssignedVars(), pre.getVars())) {
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
				} else {
					if (!modifiableGlobals.contains(bv) && hier.getVars().contains(bv)) {
						return false;
					}
				}
			}
		}
		return true;
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
			if (pv instanceof IProgramNonOldVar) {
				if (!modifiableGlobals.contains(pv)) {
					if (hier.getVars().contains(pv)) {
						return false;
					}
				}
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
				&& !varSetDisjoint(hier.getVars(), localVarsAssignment.getInVars().keySet());
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

	/**
	 * If the assigned vars of cb are disjoint from the variables in p the selfloop (p,cb,p) is trivially inductive.
	 * Returns HTTV.VALID if selfloop is inductive. Returns null if we are not able to determinie inductivity selfloop.
	 */
	public Validity sdecInternalSelfloop(final IPredicate p, final IInternalAction act) {
		final Set<IProgramVar> assignedVars = act.getTransformula().getAssignedVars();
		final Set<IProgramVar> occVars = p.getVars();
		for (final IProgramVar occVar : occVars) {
			if (assignedVars.contains(occVar)) {
				return null;
			}
		}
		mHoareTripleCheckerStatistics.getSDsluCounter().incIn();
		return Validity.VALID;
	}

	/**
	 * Returns UNSAT if p contains only non-old globals.
	 */
	public Validity sdecCallSelfloop(final IPredicate p, final ICallAction call) {
		for (final IProgramVar bv : p.getVars()) {
			if (bv.isGlobal()) {
				if (bv.isOldvar()) {
					return null;
				}
			} else {
				return null;
			}
		}
		mHoareTripleCheckerStatistics.getSDsluCounter().incCa();
		return Validity.VALID;
	}

	public Validity sdecReturnSelfloopPre(final IPredicate p, final IReturnAction ret) {
		final Set<IProgramVar> assignedVars = ret.getAssignmentOfReturn().getAssignedVars();
		for (final IProgramVar bv : p.getVars()) {
			if (bv.isGlobal()) {
				if (bv.isOldvar()) {
					return null;
				} else if (assignedVars.contains(bv)) {
					return null;
				}
			} else {
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
	private static boolean isOrIteFormula(final IPredicate p) {
		final Term formula = p.getFormula();
		if (formula instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) formula;
			final FunctionSymbol symbol = appTerm.getFunction();
			final boolean result = symbol.getName().equals("or") || symbol.getName().equals("ite");
			return result;
		}
		return false;
	}
}
