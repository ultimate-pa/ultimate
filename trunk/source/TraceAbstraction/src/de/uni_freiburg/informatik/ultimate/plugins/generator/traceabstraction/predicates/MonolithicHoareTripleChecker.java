/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 * 
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.logic.ReasonUnknown;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.VariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.ICallAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IReturnAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.HoareTripleCheckerStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashMap;

public class MonolithicHoareTripleChecker implements IHoareTripleChecker {
	
	private final ManagedScript m_ManagedScript;
	private final ModifiableGlobalVariableManager m_ModifiableGlobals;
	
	private final HoareTripleCheckerStatisticsGenerator m_HoareTripleCheckerStatistics;

	private ScopedHashMap<String, Term> m_IndexedConstants;
	
	private int m_TrivialSatQueries = 0;
	private int m_NontrivialSatQueries = 0;
	private long m_SatCheckSolverTime = 0;

	private int m_TrivialCoverQueries = 0;
	private int m_NontrivialCoverQueries = 0;
	
	private long m_SatCheckTime = 0;
	
	/**
	 * Whenever you do an edge check with the old method (not edge checker),
	 * test if the dataflow checks deliver a compatible result. Set this only to
	 * true if you can guarantee that only an IPredicate whose formula is true
	 * is equivalent to true.
	 */
	private final static boolean m_TestDataflow = false;
	
	
	public MonolithicHoareTripleChecker(SmtManager smtManager) {
		this(smtManager.getManagedScript(), smtManager.getModifiableGlobals());
	}

	public MonolithicHoareTripleChecker(
			final ManagedScript managedScript, 
			final ModifiableGlobalVariableManager modifiableGlobals) {
		super();
		m_ManagedScript = managedScript;
		m_ModifiableGlobals = modifiableGlobals;
		m_HoareTripleCheckerStatistics = new HoareTripleCheckerStatisticsGenerator();
	}

	@Override
	public Validity checkInternal(IPredicate pre, IInternalAction act, IPredicate succ) {
		m_HoareTripleCheckerStatistics.continueEdgeCheckerTime();
		Validity result = IHoareTripleChecker.lbool2validity(isInductive(pre, act, succ));
		m_HoareTripleCheckerStatistics.stopEdgeCheckerTime();
		switch (result) {
		case INVALID:
			m_HoareTripleCheckerStatistics.getSolverCounterSat().incIn();
			break;
		case UNKNOWN:
			m_HoareTripleCheckerStatistics.getSolverCounterUnknown().incIn();
			break;
		case VALID:
			m_HoareTripleCheckerStatistics.getSolverCounterUnsat().incIn();
			break;
		default:
			throw new AssertionError("unknown case");
		}
		return result;
	}

	@Override
	public Validity checkCall(IPredicate pre, ICallAction act, IPredicate succ) {
		m_HoareTripleCheckerStatistics.continueEdgeCheckerTime();
		Validity result =  IHoareTripleChecker.lbool2validity(isInductiveCall(pre, (Call) act, succ));
		m_HoareTripleCheckerStatistics.stopEdgeCheckerTime();
		switch (result) {
		case INVALID:
			m_HoareTripleCheckerStatistics.getSolverCounterSat().incCa();
			break;
		case UNKNOWN:
			m_HoareTripleCheckerStatistics.getSolverCounterUnknown().incCa();
			break;
		case VALID:
			m_HoareTripleCheckerStatistics.getSolverCounterUnsat().incCa();
			break;
		default:
			throw new AssertionError("unknown case");
		}
		return result;
	}

	@Override
	public Validity checkReturn(IPredicate preLin, IPredicate preHier,
			IReturnAction act, IPredicate succ) {
		m_HoareTripleCheckerStatistics.continueEdgeCheckerTime();
		Validity result =  IHoareTripleChecker.lbool2validity(isInductiveReturn(preLin, preHier, (Return) act, succ));
		m_HoareTripleCheckerStatistics.stopEdgeCheckerTime();
		switch (result) {
		case INVALID:
			m_HoareTripleCheckerStatistics.getSolverCounterSat().incRe();
			break;
		case UNKNOWN:
			m_HoareTripleCheckerStatistics.getSolverCounterUnknown().incRe();
			break;
		case VALID:
			m_HoareTripleCheckerStatistics.getSolverCounterUnsat().incRe();
			break;
		default:
			throw new AssertionError("unknown case");
		}
		return result;
	}

	public HoareTripleCheckerStatisticsGenerator getEdgeCheckerBenchmark() {
		return m_HoareTripleCheckerStatistics;
	}

	@Override
	public void releaseLock() {
		// do nothing, since objects of this class do not lock the solver
	}
	
	
	
	
	
	
	public LBool isInductive(IPredicate ps1, IInternalAction ta, IPredicate ps2) {
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
	 * @return The result of a theorem prover query, where SMT_UNSAT means yes
	 *         to our question, SMT_SAT means no to our question and SMT_UNKNOWN
	 *         means that the theorem prover was not able give an answer to our
	 *         question.
	 */
	public LBool isInductive(IPredicate ps1, IInternalAction ta, IPredicate ps2, boolean expectUnsat) {
		m_ManagedScript.lock(this);
		long startTime = System.nanoTime();

		if (isDontCare(ps1) || isDontCare(ps2)) {
			m_TrivialSatQueries++;
			m_ManagedScript.unlock(this);
			return Script.LBool.UNKNOWN;
		}

		if (SmtUtils.isFalse(ps1.getFormula()) || SmtUtils.isTrue(ps2.getFormula())) {
			m_TrivialSatQueries++;
			m_ManagedScript.unlock(this);
			return Script.LBool.UNSAT;
		}

		// if (simpleSelfloopCheck(ps1, ta, ps2)) {
		// m_TrivialSatQueries = m_TrivialSatQueries + 10000000;
		// return Script.LBool.UNSAT;
		// }

		TransFormula tf = ta.getTransformula();
		String procPred = ta.getPreceedingProcedure();
		String procSucc = ta.getSucceedingProcedure();
//		assert proc.equals(ta.getSucceedingProcedure()) : "different procedure before and after";
		Set<BoogieVar> modifiableGlobalsPred = m_ModifiableGlobals.getModifiedBoogieVars(procPred);
		Set<BoogieVar> modifiableGlobalsSucc = m_ModifiableGlobals.getModifiedBoogieVars(procSucc);

		LBool result = PredicateUtils.isInductiveHelper(m_ManagedScript.getScript(), 
				ps1, ps2, tf, modifiableGlobalsPred, modifiableGlobalsSucc);

		if (expectUnsat) {
			assert (result == Script.LBool.UNSAT || result == Script.LBool.UNKNOWN) : 
				"From " + ps1.getFormula().toStringDirect() +
				"Statements " + ta.toString() +
				"To " + ps2.getFormula().toStringDirect() +
				"Not inductive!";
		}
		m_SatCheckTime += (System.nanoTime() - startTime);
		if (m_TestDataflow) {
			testMyInternalDataflowCheck(ps1, ta, ps2, result);
		}
		m_ManagedScript.unlock(this);
		return result;
	}

	public LBool isInductiveCall(IPredicate ps1, Call ta, IPredicate ps2) {
		return isInductiveCall(ps1, ta, ps2, false);
	}

	public LBool isInductiveCall(IPredicate ps1, Call ta, IPredicate ps2, boolean expectUnsat) {
		m_ManagedScript.lock(this);
		long startTime = System.nanoTime();

		if (isDontCare(ps1) || isDontCare(ps2)) {
			m_TrivialSatQueries++;
			m_ManagedScript.unlock(this);
			return Script.LBool.UNKNOWN;
		}

		if (SmtUtils.isFalse(ps1.getFormula()) || SmtUtils.isTrue(ps2.getFormula())) {
			m_TrivialSatQueries++;
			m_ManagedScript.unlock(this);
			return Script.LBool.UNSAT;
		}

		m_ManagedScript.getScript().push(1);
		m_IndexedConstants = new ScopedHashMap<String, Term>();
		// OldVars not renamed if modifiable.
		// All variables get index 0.
		String caller = ta.getPreceedingProcedure();
		Set<BoogieVar> modifiableGlobalsCaller = m_ModifiableGlobals.getModifiedBoogieVars(caller);
		Term ps1renamed = PredicateUtils.formulaWithIndexedVars(ps1, new HashSet<BoogieVar>(0), 4, 0,
				Integer.MIN_VALUE, null, -5, 0, m_IndexedConstants, m_ManagedScript.getScript(), modifiableGlobalsCaller);

		TransFormula tf = ta.getTransitionFormula();
		Set<BoogieVar> assignedVars = new HashSet<BoogieVar>();
		Term fTrans = PredicateUtils.formulaWithIndexedVars(tf, 0, 1, assignedVars, m_IndexedConstants, m_ManagedScript.getScript());

		// OldVars renamed to index 0
		// GlobalVars renamed to index 0
		// Other vars get index 1
		String callee = ta.getSucceedingProcedure();
		Set<BoogieVar> modifiableGlobalsCallee = m_ModifiableGlobals.getModifiedBoogieVars(callee);
		Term ps2renamed = PredicateUtils.formulaWithIndexedVars(ps2, new HashSet<BoogieVar>(0), 4, 1, 0, null, 23, 0,
				m_IndexedConstants, m_ManagedScript.getScript(), modifiableGlobalsCallee);

		// We want to return true if (fState1 && fTrans)-> fState2 is valid
		// This is the case if (fState1 && fTrans && !fState2) is unsatisfiable
		Term f = SmtUtils.not(m_ManagedScript.getScript(), ps2renamed);
		f = Util.and(m_ManagedScript.getScript(), fTrans, f);
		f = Util.and(m_ManagedScript.getScript(), ps1renamed, f);

		LBool result = checkSatisfiable(f);
		m_IndexedConstants = null;
		m_ManagedScript.getScript().pop(1);
		if (expectUnsat) {
			assert (result == Script.LBool.UNSAT || result == Script.LBool.UNKNOWN) : "call statement not inductive";
		}
		m_SatCheckTime += (System.nanoTime() - startTime);
		if (m_TestDataflow) {
			testMyCallDataflowCheck(ps1, ta, ps2, result);
		}
		m_ManagedScript.unlock(this);
		return result;
	}

	public LBool isInductiveReturn(IPredicate ps1, IPredicate psk, Return ta, IPredicate ps2) {
		return isInductiveReturn(ps1, psk, ta, ps2, false);
	}

	public LBool isInductiveReturn(IPredicate ps1, IPredicate psk, Return ta, IPredicate ps2, boolean expectUnsat) {
		m_ManagedScript.lock(this);
		long startTime = System.nanoTime();

		if (isDontCare(ps1) || isDontCare(ps2) || isDontCare(psk)) {
			m_TrivialSatQueries++;
			m_ManagedScript.unlock(this);
			return Script.LBool.UNKNOWN;
		}

		if (SmtUtils.isFalse(ps1.getFormula()) || SmtUtils.isFalse(psk.getFormula()) || SmtUtils.isTrue(ps2.getFormula())) {
			m_TrivialSatQueries++;
			m_ManagedScript.unlock(this);
			return Script.LBool.UNSAT;
		}

		m_ManagedScript.getScript().push(1);
		m_IndexedConstants = new ScopedHashMap<String, Term>();
		Call ca = ta.getCorrespondingCall();

		TransFormula tfReturn = ta.getTransitionFormula();
		Set<BoogieVar> assignedVarsOnReturn = new HashSet<BoogieVar>();
		Term fReturn = PredicateUtils.formulaWithIndexedVars(tfReturn, 1, 2, assignedVarsOnReturn, m_IndexedConstants,
				m_ManagedScript.getScript());
		// fReturn = (new FormulaUnLet()).unlet(fReturn);

		TransFormula tfCall = ca.getTransitionFormula();
		Set<BoogieVar> assignedVarsOnCall = new HashSet<BoogieVar>();
		Term fCall = PredicateUtils.formulaWithIndexedVars(tfCall, 0, 1, assignedVarsOnCall, m_IndexedConstants,
				m_ManagedScript.getScript());
		// fCall = (new FormulaUnLet()).unlet(fCall);

		String callee = ta.getPreceedingProcedure();
		Set<BoogieVar> modifiableGlobalsCallee = m_ModifiableGlobals.getModifiedBoogieVars(callee);

		String caller = ta.getSucceedingProcedure();
		Set<BoogieVar> modifiableGlobalsCaller = m_ModifiableGlobals.getModifiedBoogieVars(caller);

		// oldVars not renamed if modifiable
		// other variables get index 0
		Term pskrenamed = PredicateUtils.formulaWithIndexedVars(psk, new HashSet<BoogieVar>(0), 23, 0,
				Integer.MIN_VALUE, null, 23, 0, m_IndexedConstants, m_ManagedScript.getScript(), modifiableGlobalsCaller);

		// oldVars get index 0
		// modifiable globals get index 2
		// not modifiable globals get index 0
		// other variables get index 1
		Term ps1renamed = PredicateUtils.formulaWithIndexedVars(ps1, new HashSet<BoogieVar>(0), 23, 1, 0,
				modifiableGlobalsCallee, 2, 0, m_IndexedConstants, m_ManagedScript.getScript(), modifiableGlobalsCallee);

		// oldVars not renamed if modifiable
		// modifiable globals get index 2
		// variables assigned on return get index 2
		// other variables get index 0
		Term ps2renamed = PredicateUtils.formulaWithIndexedVars(ps2, assignedVarsOnReturn, 2, 0, Integer.MIN_VALUE,
				modifiableGlobalsCallee, 2, 0, m_IndexedConstants, m_ManagedScript.getScript(), modifiableGlobalsCaller);

		// We want to return true if (fState1 && fTrans)-> fState2 is valid
		// This is the case if (fState1 && fTrans && !fState2) is unsatisfiable
		Term f = SmtUtils.not(m_ManagedScript.getScript(), ps2renamed);
		f = Util.and(m_ManagedScript.getScript(), fReturn, f);
		f = Util.and(m_ManagedScript.getScript(), ps1renamed, f);
		f = Util.and(m_ManagedScript.getScript(), fCall, f);
		f = Util.and(m_ManagedScript.getScript(), pskrenamed, f);

		LBool result = checkSatisfiable(f);
		m_ManagedScript.getScript().pop(1);
		m_IndexedConstants = null;
		if (expectUnsat) {
			if (result == LBool.SAT) {
			}
			assert (result == Script.LBool.UNSAT || result == Script.LBool.UNKNOWN) :
				("From " + ps1.getFormula().toStringDirect()) +
				("Caller " + psk.getFormula().toStringDirect()) +
				("Statements " + ta.getPrettyPrintedStatements()) +
				("To " + ps2.getFormula().toStringDirect()) +
				("Not inductive!");

		}
		m_SatCheckTime += (System.nanoTime() - startTime);
		if (m_TestDataflow) {
			testMyReturnDataflowCheck(ps1, psk, ta, ps2, result);
		}
		m_ManagedScript.unlock(this);
		return result;
	}
	
	public LBool assertTerm(Term term) {
		long startTime = System.nanoTime();
		LBool result = null;
		result = m_ManagedScript.getScript().assertTerm(term);
		m_SatCheckSolverTime += (System.nanoTime() - startTime);
		return result;
	}
	
	
	LBool checkSatisfiable(Term f) {
		long startTime = System.nanoTime();
		LBool result = null;
		try {
			assertTerm(f);
		} catch (SMTLIBException e) {
			if (e.getMessage().equals("Unsupported non-linear arithmetic")) {
				return LBool.UNKNOWN;
			} else {
				throw e;
			}
		}
		result = m_ManagedScript.getScript().checkSat();
		m_SatCheckSolverTime += (System.nanoTime() - startTime);
		m_NontrivialSatQueries++;
		if (result == LBool.UNKNOWN) {
			Object info = m_ManagedScript.getScript().getInfo(":reason-unknown");
			if (!(info instanceof ReasonUnknown)) {
				m_ManagedScript.getScript().getInfo(":reason-unknown");
			}
			ReasonUnknown reason = (ReasonUnknown) info;
			Object test = m_ManagedScript.getScript().getInfo(":reason-unknown");
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
	
	private boolean isDontCare(IPredicate ps2) {
		// yet I don't know how to check for don't care
		// avoid proper implementation if not needed
		return false;
	}

	// FIXME: remove once enough tested
	private void testMyReturnDataflowCheck(IPredicate ps1, IPredicate psk, Return ta, IPredicate ps2, LBool result) {
		if (ps2.getFormula() == m_ManagedScript.getScript().term("false")) {
			return;
		}
		SdHoareTripleCheckerHelper sdhtch = new SdHoareTripleCheckerHelper(m_ModifiableGlobals, null);
		Validity testRes = sdhtch.sdecReturn(ps1, psk, ta, ps2);
		if (testRes != null) {
			// assert testRes == result : "my return dataflow check failed";
			if (testRes != IHoareTripleChecker.lbool2validity(result)) {
				sdhtch.sdecReturn(ps1, psk, ta, ps2);
			}
		}
	}

	// FIXME: remove once enough tested
	private void testMyCallDataflowCheck(IPredicate ps1, Call ta, IPredicate ps2, LBool result) {
		if (ps2.getFormula() == m_ManagedScript.getScript().term("false")) {
			return;
		}
		SdHoareTripleCheckerHelper sdhtch = new SdHoareTripleCheckerHelper(m_ModifiableGlobals, null);
		Validity testRes = sdhtch.sdecCall(ps1, ta, ps2);
		if (testRes != null) {
			assert testRes == IHoareTripleChecker.lbool2validity(result) : "my call dataflow check failed";
			// if (testRes != result) {
			// sdhtch.sdecReturn(ps1, psk, ta, ps2);
			// }
		}
	}

	// FIXME: remove once enough tested
	private void testMyInternalDataflowCheck(IPredicate ps1, IInternalAction ta, IPredicate ps2, LBool result) {
		if (ps2.getFormula() == m_ManagedScript.getScript().term("false")) {
			SdHoareTripleCheckerHelper sdhtch = new SdHoareTripleCheckerHelper(m_ModifiableGlobals, null);
			Validity testRes = sdhtch.sdecInternalToFalse(ps1, ta);
			if (testRes != null) {
				assert testRes == IHoareTripleChecker.lbool2validity(result) || testRes == IHoareTripleChecker.lbool2validity(LBool.UNKNOWN) && result == LBool.SAT : "my internal dataflow check failed";
				// if (testRes != result) {
				// sdhtch.sdecInternalToFalse(ps1, ta);
				// }
			}
			return;
		}
		if (ps1 == ps2) {
			SdHoareTripleCheckerHelper sdhtch = new SdHoareTripleCheckerHelper(m_ModifiableGlobals, null);
			Validity testRes = sdhtch.sdecInternalSelfloop(ps1, ta);
			if (testRes != null) {
				assert testRes == IHoareTripleChecker.lbool2validity(result) : "my internal dataflow check failed";
				// if (testRes != result) {
				// sdhtch.sdecReturn(ps1, psk, ta, ps2);
				// }
			}
		}
		if (ta.getTransformula().isInfeasible() == Infeasibility.INFEASIBLE) {
			return;
		}
		SdHoareTripleCheckerHelper sdhtch = new SdHoareTripleCheckerHelper(m_ModifiableGlobals, null);
		Validity testRes = sdhtch.sdecInteral(ps1, ta, ps2);
		if (testRes != null) {
			assert testRes == IHoareTripleChecker.lbool2validity(result) : "my internal dataflow check failed";
			// if (testRes != result) {
			// sdhtch.sdecReturn(ps1, psk, ta, ps2);
			// }
		}
	}

}
