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

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUtils;
import de.uni_freiburg.informatik.ultimate.logic.ReasonUnknown;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashMap;

public class MonolithicHoareTripleChecker implements IHoareTripleChecker {

	private final CfgSmtToolkit mCsToolkit;
	private final ManagedScript mManagedScript;
	private final ModifiableGlobalsTable mModifiableGlobals;

	private final HoareTripleCheckerStatisticsGenerator mHoareTripleCheckerStatistics;

	private ScopedHashMap<String, Term> mIndexedConstants;

	// TODO: Remove these variables or use them
	private int mTrivialSatQueries = 0;
	private int mNontrivialSatQueries = 0;
	private long mSatCheckSolverTime = 0;

	private final int mTrivialCoverQueries = 0;
	private final int mNontrivialCoverQueries = 0;

	private long mSatCheckTime = 0;

	/**
	 * Whenever you do an edge check with the old method (not edge checker), test if the dataflow checks deliver a
	 * compatible result. Set this only to true if you can guarantee that only an IPredicate whose formula is true is
	 * equivalent to true.
	 */
	private final static boolean DEBUG_TEST_DATAFLOW = false;

	public MonolithicHoareTripleChecker(final CfgSmtToolkit csToolkit) {
		super();
		mCsToolkit = csToolkit;
		mManagedScript = csToolkit.getManagedScript();
		mModifiableGlobals = csToolkit.getModifiableGlobalsTable();
		mHoareTripleCheckerStatistics = new HoareTripleCheckerStatisticsGenerator();
	}

	@Override
	public Validity checkInternal(final IPredicate pre, final IInternalAction act, final IPredicate succ) {
		mHoareTripleCheckerStatistics.continueEdgeCheckerTime();
		final Validity result = IHoareTripleChecker.convertLBool2Validity(isInductive(pre, act, succ));
		mHoareTripleCheckerStatistics.stopEdgeCheckerTime();
		switch (result) {
		case INVALID:
			mHoareTripleCheckerStatistics.getSolverCounterSat().incIn();
			break;
		case UNKNOWN:
			mHoareTripleCheckerStatistics.getSolverCounterUnknown().incIn();
			break;
		case VALID:
			mHoareTripleCheckerStatistics.getSolverCounterUnsat().incIn();
			break;
		default:
			throw new AssertionError("unknown case");
		}
		return result;
	}

	@Override
	public Validity checkCall(final IPredicate pre, final ICallAction act, final IPredicate succ) {
		mHoareTripleCheckerStatistics.continueEdgeCheckerTime();
		final Validity result = IHoareTripleChecker.convertLBool2Validity(isInductiveCall(pre, act, succ));
		mHoareTripleCheckerStatistics.stopEdgeCheckerTime();
		switch (result) {
		case INVALID:
			mHoareTripleCheckerStatistics.getSolverCounterSat().incCa();
			break;
		case UNKNOWN:
			mHoareTripleCheckerStatistics.getSolverCounterUnknown().incCa();
			break;
		case VALID:
			mHoareTripleCheckerStatistics.getSolverCounterUnsat().incCa();
			break;
		default:
			throw new AssertionError("unknown case");
		}
		return result;
	}

	@Override
	public Validity checkReturn(final IPredicate preLin, final IPredicate preHier, final IReturnAction act,
			final IPredicate succ) {
		mHoareTripleCheckerStatistics.continueEdgeCheckerTime();
		final Validity result =
				IHoareTripleChecker.convertLBool2Validity(isInductiveReturn(preLin, preHier, act, succ));
		mHoareTripleCheckerStatistics.stopEdgeCheckerTime();
		switch (result) {
		case INVALID:
			mHoareTripleCheckerStatistics.getSolverCounterSat().incRe();
			break;
		case UNKNOWN:
			mHoareTripleCheckerStatistics.getSolverCounterUnknown().incRe();
			break;
		case VALID:
			mHoareTripleCheckerStatistics.getSolverCounterUnsat().incRe();
			break;
		default:
			throw new AssertionError("unknown case");
		}
		return result;
	}

	@Override
	public HoareTripleCheckerStatisticsGenerator getEdgeCheckerBenchmark() {
		return mHoareTripleCheckerStatistics;
	}

	@Override
	public void releaseLock() {
		// do nothing, since objects of this class do not lock the solver
	}

	public LBool isInductive(final IPredicate ps1, final IInternalAction ta, final IPredicate ps2) {
		return isInductive(ps1, ta, ps2, false);
	}

	// TODO less renaming possible e.g. keep var names in ps1
	/**
	 * Check if post(sf1,tf) is a subset of sf2.
	 *
	 * @param ps1
	 *            a set of states represented by a Predicate
	 * @param tf
	 *            a transition relation represented by a TransFormula
	 * @param ps2
	 *            a set of states represented by a Predicate
	 * @return The result of a theorem prover query, where SMT_UNSAT means yes to our question, SMT_SAT means no to our
	 *         question and SMT_UNKNOWN means that the theorem prover was not able give an answer to our question.
	 */
	public LBool isInductive(final IPredicate ps1, final IInternalAction ta, final IPredicate ps2,
			final boolean expectUnsat) {
		mManagedScript.lock(this);
		final long startTime = System.nanoTime();

		if (isDontCare(ps1) || isDontCare(ps2)) {
			mTrivialSatQueries++;
			mManagedScript.unlock(this);
			return Script.LBool.UNKNOWN;
		}

		if (SmtUtils.isFalseLiteral(ps1.getFormula()) || SmtUtils.isTrueLiteral(ps2.getFormula())) {
			mTrivialSatQueries++;
			mManagedScript.unlock(this);
			return Script.LBool.UNSAT;
		}

		// if (simpleSelfloopCheck(ps1, ta, ps2)) {
		// mTrivialSatQueries = mTrivialSatQueries + 10000000;
		// return Script.LBool.UNSAT;
		// }

		final UnmodifiableTransFormula tf = ta.getTransformula();
		final String procPred = ta.getPrecedingProcedure();
		final String procSucc = ta.getSucceedingProcedure();
		// assert proc.equals(ta.getSucceedingProcedure()) : "different procedure before and after";
		final Set<IProgramNonOldVar> modifiableGlobalsPred = mModifiableGlobals.getModifiedBoogieVars(procPred);
		final Set<IProgramNonOldVar> modifiableGlobalsSucc = mModifiableGlobals.getModifiedBoogieVars(procSucc);

		final LBool result = PredicateUtils.isInductiveHelper(mManagedScript.getScript(), ps1, ps2, tf,
				modifiableGlobalsPred, modifiableGlobalsSucc);

		if (expectUnsat) {
			assert (result == Script.LBool.UNSAT || result == Script.LBool.UNKNOWN) : "From "
					+ ps1.getFormula().toStringDirect() + "Statements " + ta.toString() + "To "
					+ ps2.getFormula().toStringDirect() + "Not inductive!";
		}
		mSatCheckTime += (System.nanoTime() - startTime);
		if (DEBUG_TEST_DATAFLOW) {
			testMyInternalDataflowCheck(ps1, ta, ps2, result);
		}
		mManagedScript.unlock(this);
		return result;
	}

	public LBool isInductiveCall(final IPredicate ps1, final ICallAction ta, final IPredicate ps2) {
		return isInductiveCall(ps1, ta, ps2, false);
	}

	public LBool isInductiveCall(final IPredicate ps1, final ICallAction ta, final IPredicate ps2,
			final boolean expectUnsat) {
		mManagedScript.lock(this);
		final long startTime = System.nanoTime();

		if (isDontCare(ps1) || isDontCare(ps2)) {
			mTrivialSatQueries++;
			mManagedScript.unlock(this);
			return Script.LBool.UNKNOWN;
		}

		if (SmtUtils.isFalseLiteral(ps1.getFormula()) || SmtUtils.isTrueLiteral(ps2.getFormula())) {
			mTrivialSatQueries++;
			mManagedScript.unlock(this);
			return Script.LBool.UNSAT;
		}

		mManagedScript.getScript().push(1);
		mIndexedConstants = new ScopedHashMap<>();
		// OldVars not renamed if modifiable.
		// All variables get index 0.
		final String caller = ta.getPrecedingProcedure();
		final Set<IProgramNonOldVar> modifiableGlobalsCaller = mModifiableGlobals.getModifiedBoogieVars(caller);
		final Term ps1renamed = PredicateUtils.formulaWithIndexedVars(ps1, new HashSet<IProgramVar>(0), 4, 0,
				Integer.MIN_VALUE, null, -5, 0, mIndexedConstants, mManagedScript.getScript(), modifiableGlobalsCaller);

		final UnmodifiableTransFormula tf = ta.getLocalVarsAssignment();
		final Set<IProgramVar> assignedVars = new HashSet<>();
		final Term fTrans = PredicateUtils.formulaWithIndexedVars(tf, 0, 1, assignedVars, mIndexedConstants,
				mManagedScript.getScript());

		// OldVars renamed to index 0
		// GlobalVars renamed to index 0
		// Other vars get index 1
		final String callee = ta.getSucceedingProcedure();
		final Set<IProgramNonOldVar> modifiableGlobalsCallee = mModifiableGlobals.getModifiedBoogieVars(callee);
		final Term ps2renamed = PredicateUtils.formulaWithIndexedVars(ps2, new HashSet<IProgramVar>(0), 4, 1, 0, null,
				23, 0, mIndexedConstants, mManagedScript.getScript(), modifiableGlobalsCallee);

		// We want to return true if (fState1 && fTrans)-> fState2 is valid
		// This is the case if (fState1 && fTrans && !fState2) is unsatisfiable
		Term f = SmtUtils.not(mManagedScript.getScript(), ps2renamed);
		f = SmtUtils.and(mManagedScript.getScript(), fTrans, f);
		f = SmtUtils.and(mManagedScript.getScript(), ps1renamed, f);

		final LBool result = checkSatisfiable(f);
		mIndexedConstants = null;
		mManagedScript.getScript().pop(1);
		if (expectUnsat) {
			assert (result == Script.LBool.UNSAT || result == Script.LBool.UNKNOWN) : "call statement not inductive";
		}
		mSatCheckTime += (System.nanoTime() - startTime);
		if (DEBUG_TEST_DATAFLOW) {
			testMyCallDataflowCheck(ps1, ta, ps2, result);
		}
		mManagedScript.unlock(this);
		return result;
	}

	public LBool isInductiveReturn(final IPredicate ps1, final IPredicate psk, final IReturnAction ta,
			final IPredicate ps2) {
		return isInductiveReturn(ps1, psk, ta, ps2, false);
	}

	public LBool isInductiveReturn(final IPredicate ps1, final IPredicate psk, final IReturnAction ta,
			final IPredicate ps2, final boolean expectUnsat) {
		mManagedScript.lock(this);
		final long startTime = System.nanoTime();

		if (isDontCare(ps1) || isDontCare(ps2) || isDontCare(psk)) {
			mTrivialSatQueries++;
			mManagedScript.unlock(this);
			return Script.LBool.UNKNOWN;
		}

		if (SmtUtils.isFalseLiteral(ps1.getFormula()) || SmtUtils.isFalseLiteral(psk.getFormula())
				|| SmtUtils.isTrueLiteral(ps2.getFormula())) {
			mTrivialSatQueries++;
			mManagedScript.unlock(this);
			return Script.LBool.UNSAT;
		}

		mManagedScript.getScript().push(1);
		mIndexedConstants = new ScopedHashMap<>();

		final UnmodifiableTransFormula tfReturn = ta.getAssignmentOfReturn();
		final Set<IProgramVar> assignedVarsOnReturn = new HashSet<>();
		final Term fReturn = PredicateUtils.formulaWithIndexedVars(tfReturn, 1, 2, assignedVarsOnReturn,
				mIndexedConstants, mManagedScript.getScript());
		// fReturn = (new FormulaUnLet()).unlet(fReturn);

		final UnmodifiableTransFormula tfCall = ta.getLocalVarsAssignmentOfCall();
		final Set<IProgramVar> assignedVarsOnCall = new HashSet<>();
		final Term fCall = PredicateUtils.formulaWithIndexedVars(tfCall, 0, 1, assignedVarsOnCall, mIndexedConstants,
				mManagedScript.getScript());
		// fCall = (new FormulaUnLet()).unlet(fCall);

		final String callee = ta.getPrecedingProcedure();
		final Set<IProgramNonOldVar> modifiableGlobalsCallee = mModifiableGlobals.getModifiedBoogieVars(callee);

		final String caller = ta.getSucceedingProcedure();
		final Set<IProgramNonOldVar> modifiableGlobalsCaller = mModifiableGlobals.getModifiedBoogieVars(caller);

		// oldVars not renamed if modifiable
		// other variables get index 0
		final Term pskrenamed = PredicateUtils.formulaWithIndexedVars(psk, new HashSet<IProgramVar>(0), 23, 0,
				Integer.MIN_VALUE, null, 23, 0, mIndexedConstants, mManagedScript.getScript(), modifiableGlobalsCaller);

		// oldVars get index 0
		// modifiable globals get index 2, unless they are modified on return then they get index 1
		// not modifiable globals get index 0
		// other variables get index 1
		final Set<IProgramVar> modifiableGlobalsAssignedOnReturn = new HashSet<>();
		for (final IProgramVar assignedVar : tfReturn.getAssignedVars()) {
			if (modifiableGlobalsCallee.contains(assignedVar)) {
				modifiableGlobalsAssignedOnReturn.add(assignedVar);
			}
		}
		final Term ps1renamed = PredicateUtils.formulaWithIndexedVars(ps1, modifiableGlobalsAssignedOnReturn, 1, 1, 0,
				modifiableGlobalsCallee, 2, 0, mIndexedConstants, mManagedScript.getScript(), modifiableGlobalsCallee);

		// oldVars not renamed if modifiable
		// modifiable globals get index 2
		// variables assigned on return get index 2
		// other variables get index 0
		final Term ps2renamed = PredicateUtils.formulaWithIndexedVars(ps2, assignedVarsOnReturn, 2, 0,
				Integer.MIN_VALUE, modifiableGlobalsCallee, 2, 0, mIndexedConstants, mManagedScript.getScript(),
				modifiableGlobalsCaller);

		// We want to return true if (fState1 && fTrans)-> fState2 is valid
		// This is the case if (fState1 && fTrans && !fState2) is unsatisfiable
		Term f = SmtUtils.not(mManagedScript.getScript(), ps2renamed);
		f = SmtUtils.and(mManagedScript.getScript(), fReturn, f);
		f = SmtUtils.and(mManagedScript.getScript(), ps1renamed, f);
		f = SmtUtils.and(mManagedScript.getScript(), fCall, f);
		f = SmtUtils.and(mManagedScript.getScript(), pskrenamed, f);

		final LBool result = checkSatisfiable(f);
		mManagedScript.getScript().pop(1);
		mIndexedConstants = null;
		if (expectUnsat) {
			assert (result == Script.LBool.UNSAT
					|| result == Script.LBool.UNKNOWN) : ("From " + ps1.getFormula().toStringDirect())
							+ ("Caller " + psk.getFormula().toStringDirect()) + ("Statements " + ta)
							+ ("To " + ps2.getFormula().toStringDirect()) + ("Not inductive!");

		}
		mSatCheckTime += (System.nanoTime() - startTime);
		if (DEBUG_TEST_DATAFLOW) {
			testMyReturnDataflowCheck(ps1, psk, ta, ps2, result);
		}
		mManagedScript.unlock(this);
		return result;
	}

	public LBool assertTerm(final Term term) {
		final long startTime = System.nanoTime();
		LBool result = null;
		result = mManagedScript.getScript().assertTerm(term);
		mSatCheckSolverTime += (System.nanoTime() - startTime);
		return result;
	}

	LBool checkSatisfiable(final Term f) {
		final long startTime = System.nanoTime();
		LBool result = null;
		try {
			assertTerm(f);
		} catch (final SMTLIBException e) {
			if (e.getMessage().equals("Unsupported non-linear arithmetic")) {
				return LBool.UNKNOWN;
			}
			throw e;
		}
		result = mManagedScript.getScript().checkSat();
		mSatCheckSolverTime += (System.nanoTime() - startTime);
		mNontrivialSatQueries++;
		if (result == LBool.UNKNOWN) {
			final Object info = mManagedScript.getScript().getInfo(":reason-unknown");
			if (!(info instanceof ReasonUnknown)) {
				mManagedScript.getScript().getInfo(":reason-unknown");
			}
			final ReasonUnknown reason = (ReasonUnknown) info;
			switch (reason) {
			case CRASHED:
				throw new AssertionError("Solver crashed");
			case MEMOUT:
				throw new AssertionError("Solver out of memory, " + "solver might be in inconsistent state");
			default:
				break;
			}
		}
		return result;
	}

	private static boolean isDontCare(final IPredicate ps2) {
		// yet I don't know how to check for don't care
		// avoid proper implementation if not needed
		return false;
	}

	// FIXME: remove once enough tested
	private void testMyReturnDataflowCheck(final IPredicate ps1, final IPredicate psk, final IReturnAction ta,
			final IPredicate ps2, final LBool result) {
		if (ps2.getFormula() == mManagedScript.getScript().term("false")) {
			return;
		}
		final SdHoareTripleCheckerHelper sdhtch = new SdHoareTripleCheckerHelper(mCsToolkit, null);
		final Validity testRes = sdhtch.sdecReturn(ps1, psk, ta, ps2);
		if (testRes != null) {
			// assert testRes == result : "my return dataflow check failed";
			if (testRes != IHoareTripleChecker.convertLBool2Validity(result)) {
				sdhtch.sdecReturn(ps1, psk, ta, ps2);
			}
		}
	}

	// FIXME: remove once enough tested
	private void testMyCallDataflowCheck(final IPredicate ps1, final ICallAction ta, final IPredicate ps2,
			final LBool result) {
		if (ps2.getFormula() == mManagedScript.getScript().term("false")) {
			return;
		}
		final SdHoareTripleCheckerHelper sdhtch = new SdHoareTripleCheckerHelper(mCsToolkit, null);
		final Validity testRes = sdhtch.sdecCall(ps1, ta, ps2);
		if (testRes != null) {
			assert testRes == IHoareTripleChecker.convertLBool2Validity(result) : "my call dataflow check failed";
			// if (testRes != result) {
			// sdhtch.sdecReturn(ps1, psk, ta, ps2);
			// }
		}
	}

	// FIXME: remove once enough tested
	private void testMyInternalDataflowCheck(final IPredicate ps1, final IInternalAction ta, final IPredicate ps2,
			final LBool result) {
		if (ps2.getFormula() == mManagedScript.getScript().term("false")) {
			final SdHoareTripleCheckerHelper sdhtch = new SdHoareTripleCheckerHelper(mCsToolkit, null);
			final Validity testRes = sdhtch.sdecInternalToFalse(ps1, ta);
			if (testRes != null) {
				assert testRes == IHoareTripleChecker.convertLBool2Validity(result)
						|| testRes == IHoareTripleChecker.convertLBool2Validity(LBool.UNKNOWN)
								&& result == LBool.SAT : "my internal dataflow check failed";
				// if (testRes != result) {
				// sdhtch.sdecInternalToFalse(ps1, ta);
				// }
			}
			return;
		}
		if (ps1 == ps2) {
			final SdHoareTripleCheckerHelper sdhtch = new SdHoareTripleCheckerHelper(mCsToolkit, null);
			final Validity testRes = sdhtch.sdecInternalSelfloop(ps1, ta);
			if (testRes != null) {
				assert testRes == IHoareTripleChecker
						.convertLBool2Validity(result) : "my internal dataflow check failed";
				// if (testRes != result) {
				// sdhtch.sdecReturn(ps1, psk, ta, ps2);
				// }
			}
		}
		if (ta.getTransformula().isInfeasible() == Infeasibility.INFEASIBLE) {
			return;
		}
		final SdHoareTripleCheckerHelper sdhtch = new SdHoareTripleCheckerHelper(mCsToolkit, null);
		final Validity testRes = sdhtch.sdecInteral(ps1, ta, ps2);
		if (testRes != null) {
			assert testRes == IHoareTripleChecker.convertLBool2Validity(result) : "my internal dataflow check failed";
			// if (testRes != result) {
			// sdhtch.sdecReturn(ps1, psk, ta, ps2);
			// }
		}
	}

}
