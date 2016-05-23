/*
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieNonOldVar;
import de.uni_freiburg.informatik.ultimate.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.preferences.RcpPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.ReasonUnknown;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.VariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SafeSubstitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.RCFGBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.RcfgPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.HoareAnnotation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashMap;

public class SmtManager {

	enum Status {
		IDLE, TRACECHECK, CODEBLOCKCHECK1, CODEBLOCKCHECK2, EDGECHECK
	};
	
	private final boolean m_ExtendedDebugOutputInScript = false;

//	private Status m_Status = Status.IDLE;

	private final Boogie2SMT m_Boogie2Smt;
	private final Script m_Script;
	private final ManagedScript m_ManagedScript;
	// private final Map<String,ASTType> m_GlobalVars;
	private final ModifiableGlobalVariableManager m_ModifiableGlobals;
	private int m_satProbNumber;

	private ScopedHashMap<String, Term> m_IndexedConstants;
	Set<BoogieVar> m_AssignedVars;

	private int m_TrivialSatQueries = 0;
	private int m_NontrivialSatQueries = 0;

	private int m_TrivialCoverQueries = 0;
	private int m_NontrivialCoverQueries = 0;

	// int m_LazyEdgeCheckQueries = 0;
	// int m_TrivialEdgeCheckQueries = 0;
	// int m_NontrivialEdgeCheckQueries = 0;

	private int m_VarSetMinimalSolverQueries = 0;
	private long m_VarSetMinimalComputationTime = 0;

	long m_SatCheckTime = 0;
	private long m_SatCheckSolverTime = 0;
	private long m_TraceCheckTime = 0;
	private long m_InterpolQuriesTime = 0;
	private int m_InterpolQueries = 0;

	private int m_FreshVariableCouter = 0;

//	private long m_TraceCheckStartTime = Long.MIN_VALUE;

	private final IUltimateServiceProvider mServices;

	private final ILogger mLogger;
	
	/**
	 * Switch to produce-interpolants mode before each trace check and leave the
	 * produce-interpolants mode afterwards 
	 * (needed for princess it can only deal with quantifiers if not in
	 * produce-interpolants mode)
	 * 
	 */
	private final boolean m_InterpolationModeSwitchNeeded;



	private final PredicateFactory m_PredicateFactory;

	public SmtManager(Script script, Boogie2SMT boogie2smt, ModifiableGlobalVariableManager modifiableGlobals,
			IUltimateServiceProvider services, boolean interpolationModeSwitchNeeded, ManagedScript managedScript) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		m_InterpolationModeSwitchNeeded = interpolationModeSwitchNeeded;
		m_Boogie2Smt = boogie2smt;
		m_Script = script;
		m_ManagedScript = managedScript;
		m_ModifiableGlobals = modifiableGlobals;
		m_PredicateFactory = new PredicateFactory(services, boogie2smt);
	}
	
	

//	public boolean isIdle() {
//		return getStatus() == Status.IDLE;
//	}

	// public Smt2Boogie getSmt2Boogie() {
	// return m_Smt2Boogie;
	// }

	public PredicateFactory getPredicateFactory() {
		return m_PredicateFactory;
	}



	public Boogie2SMT getBoogie2Smt() {
		return m_Boogie2Smt;
	}

	public Script getScript() {
		return m_Script;
	}

	private Term False() {
		return m_Script.term("false");
	}

	private Term True() {
		return m_Script.term("true");
	}

	@Deprecated
	public int getNontrivialSatQueries() {
		return m_NontrivialSatQueries;
	}

	@Deprecated
	public int getTrivialSatQueries() {
		return m_TrivialSatQueries;
	}

	@Deprecated
	public long getSatCheckSolverTime() {
		return m_SatCheckSolverTime;
	}

	@Deprecated
	public long getInterpolQuriesTime() {
		return m_InterpolQuriesTime;
	}

	@Deprecated
	public int getInterpolQueries() {
		return m_InterpolQueries;
	}

	@Deprecated
	public long getTraceCheckTime() {
		return m_TraceCheckTime;
	}

	@Deprecated
	public long getSatCheckTime() {
		return m_SatCheckTime;
	}

	// public int getTrivialEdgeCheckQueries() {
	// return m_TrivialEdgeCheckQueries;
	// }
	//
	// public int getLazyEdgeCheckQueries() {
	// return m_LazyEdgeCheckQueries;
	// }
	//
	// public int getNontrivialEdgeCheckQueries() {
	// return m_NontrivialEdgeCheckQueries;
	// }

	@Deprecated
	public int getTrivialCoverQueries() {
		return m_TrivialCoverQueries;
	}

	@Deprecated
	public int getNontrivialCoverQueries() {
		return m_NontrivialCoverQueries;
	}

	@Deprecated
	public int getVarSetMinimalSolverQueries() {
		return m_VarSetMinimalSolverQueries;
	}

	@Deprecated
	public long getVarSetMinimalComputationTime() {
		return m_VarSetMinimalComputationTime;
	}

	public void setIteration(int iteration) {
		m_satProbNumber = 0;
	}

	public int getSatProbNumber() {
		return m_satProbNumber;
	}

	public VariableManager getVariableManager() {
		return m_Boogie2Smt.getVariableManager();
	}
	


	/**
	 * Returns a predicate which states that old(g)=g for all global variables g
	 * that are modifiable by procedure proc according to
	 * ModifiableGlobalVariableManager modGlobVarManager.
	 */
	public TermVarsProc getOldVarsEquality(String proc, ModifiableGlobalVariableManager modGlobVarManager) {
		Set<BoogieVar> vars = new HashSet<BoogieVar>();
		Term term = getScript().term("true");
		for (BoogieVar bv : modGlobVarManager.getGlobalVarsAssignment(proc).getAssignedVars()) {
			vars.add(bv);
			BoogieVar bvOld = ((BoogieNonOldVar) bv).getOldVar();
			vars.add(bvOld);
			TermVariable tv = bv.getTermVariable();
			TermVariable tvOld = bvOld.getTermVariable();
			Term equality = getScript().term("=", tv, tvOld);
			term = Util.and(getScript(), term, equality);
		}
		String[] procs = new String[0];
		TermVarsProc result = new TermVarsProc(term, vars, procs, PredicateUtils.computeClosedFormula(term, vars,
				getScript()));
		return result;

	}



	// private boolean varSetIsMinimal(Set<BoogieVar> boogieVars,
	// Term formula, Term closedFormula) {
	// assert isIdle();
	// long startTime = System.nanoTime();
	// m_Script.push(1);
	// Term negated = m_Script.term("not", closedFormula);
	// assertTerm(negated);
	// for (BoogieVar bv : boogieVars) {
	// TermVariable[] vars = new TermVariable[1];
	// vars[0] = bv.getTermVariable();
	// Term[] values = new Term[1];
	// values[0] = bv.getPrimedConstant();
	// formula = m_Script.let(vars, values, formula);
	// formula = renameVarsToDefaultConstants(boogieVars, formula);
	//
	// m_Script.push(1);
	// assertTerm(formula);
	// LBool sat = m_Script.checkSat();
	// m_VarSetMinimalSolverQueries++;
	// if (sat == LBool.UNSAT) {
	// // variable was not necessary
	// m_Script.pop(2);
	// m_VarSetMinimalComputationTime += (System.nanoTime() - startTime);
	// return false;
	// } else if (sat == LBool.SAT) {
	// m_Script.pop(1);
	// } else if (sat == LBool.UNKNOWN) {
	// throw new AssertionError("if this case occurs, ask Matthias");
	// } else {
	// throw new AssertionError();
	// }
	// }
	// m_VarSetMinimalComputationTime += (System.nanoTime() - startTime);
	// m_Script.pop(1);
	// return true;
	// }

	public void startTraceCheck(Object lockClaimer) {
		lock(lockClaimer);
		m_Script.echo(new QuotedObject("starting trace check"));
		if (m_InterpolationModeSwitchNeeded) {
			m_Script.setOption(":produce-interpolants", true);
		}
		m_Script.push(1);
	}

	public void endTraceCheck(Object lockOwner) {
		if (m_InterpolationModeSwitchNeeded) {
			m_Script.setOption(":produce-interpolants", false);
		}
		m_Script.echo(new QuotedObject("finished trace check"));
		m_Script.pop(1);
		unlock(lockOwner);
	}
	
	private boolean interpolationModeSwitchNeeded() {
		SolverMode solver = (new RcpPreferenceProvider(RCFGBuilder.s_PLUGIN_ID))
				.getEnum(RcfgPreferenceInitializer.LABEL_Solver, SolverMode.class);
		if (solver == SolverMode.External_PrincessInterpolationMode) {
			return true;
		} else {
			return false;
		}
	}

	// public void push() {
	// if (m_IndexedConstants != null) {
	// throw new
	// AssertionError("During Trace Abstration only one additional level on stack allowed");
	// }
	// else {
	// m_IndexedConstants = new HashMap<String, Term>();
	// m_Script.push(1);
	// }
	// }
	// public void pop() {
	// if (m_IndexedConstants == null) {
	// throw new AssertionError("Smt Manager has not pushed before");
	// }
	// else {
	// m_IndexedConstants = null;
	// m_Script.pop(1);
	// }
	// }

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
		result = m_Script.checkSat();
		m_SatCheckSolverTime += (System.nanoTime() - startTime);
		m_NontrivialSatQueries++;
		if (result == LBool.UNKNOWN) {
			Object info = m_Script.getInfo(":reason-unknown");
			if (!(info instanceof ReasonUnknown)) {
				m_Script.getInfo(":reason-unknown");
			}
			ReasonUnknown reason = (ReasonUnknown) info;
			Object test = m_Script.getInfo(":reason-unknown");
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

	public LBool assertTerm(Term term) {
		long startTime = System.nanoTime();
		LBool result = null;
		result = m_Script.assertTerm(term);
		m_SatCheckSolverTime += (System.nanoTime() - startTime);
		return result;
	}

	public Term[] computeInterpolants(Term[] interpolInput, int[] startOfSubtree) {
		long startTime = System.nanoTime();
		Term[] result = m_Script.getInterpolants(interpolInput, startOfSubtree);
		m_InterpolQuriesTime += (System.nanoTime() - startTime);
		m_InterpolQueries++;
		return result;
	}

	public Term[] computeInterpolants(Term[] interpolInput) {
		long startTime = System.nanoTime();
		Term[] result = m_Script.getInterpolants(interpolInput);
		m_InterpolQuriesTime += (System.nanoTime() - startTime);
		m_InterpolQueries++;
		return result;
	}



	// public Predicate simplify(Predicate ps) {
	// return m_PredicateFactory.newPredicate(ps.getProgramPoint(),
	// simplify(ps.getFormula()),ps.getVars());
	// }

	/**
	 * Check if ps1 is a subset of ps2.
	 * 
	 * @param ps1
	 *            set of states represented as Predicate
	 * @param ps2
	 *            set of states resresented as Predicate
	 * @return SMT_UNSAT if the inclusion holds, 1729 if the inclusion trivially
	 *         holds, SMT_SAT if the inclusion does not hold and SMT_UNKNOWN if
	 *         the theorem prover was not able to give an answer.
	 */
	public LBool isCovered(IPredicate ps1, IPredicate ps2) {
		long startTime = System.nanoTime();

		if (getPredicateFactory().isDontCare(ps1) || getPredicateFactory().isDontCare(ps2)) {
			m_TrivialCoverQueries++;
			return Script.LBool.UNKNOWN;
		}

		Term formula1 = ps1.getFormula();
		Term formula2 = ps2.getFormula();
		LBool result = null;
		// tivial case
		if (formula1 == False() || formula2 == True()) {
			m_TrivialCoverQueries++;
			result = Script.LBool.UNSAT;
		} else {
			m_Script.push(1);
			m_IndexedConstants = new ScopedHashMap<String, Term>();
			Term negImpl = Util.and(m_Script, formula1, SmtUtils.not(m_Script, formula2));

			// replace all vars by constants
			{
				TermVariable[] vars = new TermVariable[ps1.getVars().size()];
				Term[] values = new Term[vars.length];
				int i = 0;
				for (BoogieVar var : ps1.getVars()) {
					vars[i] = var.getTermVariable();
					values[i] = var.getDefaultConstant();
					i++;
				}
				negImpl = m_Script.let(vars, values, negImpl);
			}

			{
				TermVariable[] vars = new TermVariable[ps2.getVars().size()];
				Term[] values = new Term[vars.length];
				int i = 0;
				for (BoogieVar var : ps2.getVars()) {
					vars[i] = var.getTermVariable();
					values[i] = var.getDefaultConstant();
					i++;
				}
				negImpl = m_Script.let(vars, values, negImpl);
			}

			m_NontrivialCoverQueries++;
			result = checkSatisfiable(negImpl);
			m_IndexedConstants = null;
			m_Script.pop(1);
		}
		m_SatCheckTime += (System.nanoTime() - startTime);
		return result;
	}

	public Validity isCovered(Object caller, Term formula1, Term formula2) {
		assert (m_ManagedScript.isLockOwner(caller)) : "only lock owner may call";
		long startTime = System.nanoTime();

		final Validity result;
		// tivial case
		if (formula1 == False() || formula2 == True()) {
			m_TrivialCoverQueries++;
			result = Validity.VALID;
		} else {
			m_Script.push(1);
			assertTerm(formula1);
			Term negFormula2 = m_Script.term("not", formula2);
			assertTerm(negFormula2);
			result = IHoareTripleChecker.lbool2validity(m_Script.checkSat());
			m_NontrivialCoverQueries++;
			m_Script.pop(1);
		}
		m_SatCheckTime += (System.nanoTime() - startTime);
		if (m_ExtendedDebugOutputInScript && result == Validity.UNKNOWN) {
			m_Script.echo(new QuotedObject("Result of preceeding check-sat was UNKNOWN"));
		}
		return result;
	}



	// static Term getConstant(Script theory, String name, Sort sort) {
	// Term result = null;
	// Sort[] emptySorts = {};
	// theory.declareFun(name, emptySorts, sort);
	// Term[] emptyTerms = {};
	// result = theory.term(name, emptyTerms);
	// return result;
	// }

	public Term substituteRepresentants(Set<BoogieVar> boogieVars, Map<BoogieVar, TermVariable> substitution, Term term) {
		ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
		ArrayList<Term> replacers = new ArrayList<Term>();

		for (BoogieVar var : boogieVars) {
			TermVariable representant = var.getTermVariable();
			assert representant != null;
			Term substitute = substitution.get(var);
			assert substitute != null;
			replacees.add(representant);
			replacers.add(substitute);
		}
		TermVariable[] vars = replacees.toArray(new TermVariable[replacees.size()]);
		Term[] values = replacers.toArray(new Term[replacers.size()]);
		Term result = m_Script.let(vars, values, term);
		result = (new FormulaUnLet()).unlet(result);
		return result;
	}

	public Term substituteToRepresentants(Set<BoogieVar> boogieVars, Map<BoogieVar, TermVariable> boogieVar2TermVar,
			Term term) {
		ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
		ArrayList<Term> replacers = new ArrayList<Term>();

		for (BoogieVar var : boogieVars) {
			TermVariable representant = boogieVar2TermVar.get(var);
			assert representant != null;
			Term substitute = var.getTermVariable();
			assert substitute != null;
			replacees.add(representant);
			replacers.add(substitute);
		}
		TermVariable[] vars = replacees.toArray(new TermVariable[replacees.size()]);
		Term[] values = replacers.toArray(new Term[replacers.size()]);
		Term result = m_Script.let(vars, values, term);
		result = (new FormulaUnLet()).unlet(result);
		return result;
	}

	public Term substituteTermVariablesByTerms(Map<TermVariable, Term> substitution, Term term) {
		ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
		ArrayList<Term> replacers = new ArrayList<Term>();

		for (TermVariable tv : substitution.keySet()) {
			Term replacer = substitution.get(tv);
			assert replacer != null;
			replacees.add(tv);
			replacers.add(replacer);
		}
		TermVariable[] vars = replacees.toArray(new TermVariable[replacees.size()]);
		Term[] values = replacers.toArray(new Term[replacers.size()]);
		Term result = m_Script.let(vars, values, term);
		result = (new FormulaUnLet()).unlet(result);
		return result;
	}

	// public Term getConstant(BoogieVar var) {
	// String procString = var.getProcedure() == null ? "" : var.getProcedure();
	// String varString;
	// if (var.isOldvar()) {
	// varString = "old("+var.getIdentifier()+")";
	// } else {
	// varString = var.getIdentifier();
	// }
	// String name = procString+ "_" + varString;
	// Term constant = m_IndexedConstants.get(name);
	// if (constant == null) {
	// Sort resultSort =
	// m_Boogie2Smt.getTypeSortTranslator().getSort(var.getIType(), null);
	// Sort[] emptySorts = {};
	// m_Script.declareFun(name, emptySorts, resultSort);
	// Term[] emptyTerms = {};
	// constant = m_Script.term(name, emptyTerms);
	// m_IndexedConstants.put(name, constant);
	// }
	// return constant;
	// }

	// public Term getFreshConstant(TermVariable tv) {
	// String name = "fresh_" + tv.getName() + m_FreshVariableCouter++;
	// Sort resultSort = tv.getSort();
	// Sort[] emptySorts = {};
	// m_Script.declareFun(name, emptySorts, resultSort);
	// Term[] emptyTerms = {};
	// return m_Script.term(name, emptyTerms);
	// }

	// public TermVariable getFreshTermVariable(String identifier, Sort sort) {
	// String name = "fresh_" + identifier + m_FreshVariableCouter++;
	// TermVariable result = m_Script.variable(name, sort);
	// return result;
	// }

	/**
	 * @param int >=-1
	 * @return String representation of number, where -1 is represented as
	 *         <i>init</i>
	 */
	private static String quoteMinusOne(int index) {
		if (index >= 0) {
			return Integer.toString(index);
		} else if (index == -1) {
			return "init";
		} else {
			throw new IllegalArgumentException();
		}
	}

	// @Deprecated
	// private Term getIndexedConstant(String varName, int index, Sort sort) {
	// String name = "c_"+varName+"_"+index;
	// Term result = m_IndexedConstants.get(name);
	// if (result == null) {
	// Sort[] emptySorts = {};
	// m_Script.declareFun(name, emptySorts, sort);
	// Term[] emptyTerms = {};
	// result = m_Script.term(name, emptyTerms);
	// m_IndexedConstants.put(name, result);
	// }
	// return result;
	// }

	// @Deprecated
	// private Term getOldVarConstant(String varName, Sort sort) {
	// String name = "c_"+varName+"_OLD";
	// Term result = m_IndexedConstants.get(name);
	// if (result == null) {
	// Sort[] emptySorts = {};
	// m_Script.declareFun(name, emptySorts, sort);
	// Term[] emptyTerms = {};
	// result = m_Script.term(name, emptyTerms);
	// m_IndexedConstants.put(name, result);
	// }
	// return result;
	// }

	private Integer quantifiersContainedInFormula(Term formula, Set<TermVariable> quantifiedVariables) {
		Integer quantifier = null;
		if (formula instanceof ApplicationTerm) {
			Term[] parameters = ((ApplicationTerm) formula).getParameters();
			for (int i = 0; i < parameters.length; i++) {
				quantifier = quantifiersContainedInFormula(parameters[i], quantifiedVariables);
			}
		} else if (formula instanceof QuantifiedFormula) {
			quantifier = ((QuantifiedFormula) formula).getQuantifier();
			Collections.addAll(quantifiedVariables, ((QuantifiedFormula) formula).getVariables());
		}
		return quantifier;
	}

	/**
	 * Construct Predicate which represents the same Predicate as ps, but where
	 * all globalVars are renamed to oldGlobalVars.
	 */
	public IPredicate renameGlobalsToOldGlobals(IPredicate ps) {
		if (getPredicateFactory().isDontCare(ps)) {
			throw new UnsupportedOperationException("don't cat not expected");
		}

		Set<BoogieVar> allVars = ps.getVars();
		Set<BoogieVar> varsOfRenamed = new HashSet<BoogieVar>();
		varsOfRenamed.addAll(allVars);
		Set<BoogieVar> globalVars = new HashSet<BoogieVar>();
		for (BoogieVar var : allVars) {
			if (var.isGlobal()) {
				globalVars.add(var);
				varsOfRenamed.remove(var);
			}
		}
		Map<Term, Term> substitutionMapping = new HashMap<Term, Term>();
		for (BoogieVar globalBoogieVar : globalVars) {
			if (!globalBoogieVar.isOldvar()) {
				BoogieVar oldBoogieVar = ((BoogieNonOldVar) globalBoogieVar).getOldVar();
				varsOfRenamed.add(oldBoogieVar);
				substitutionMapping.put(globalBoogieVar.getTermVariable(), oldBoogieVar.getTermVariable());
			}
		}
		Term renamedFormula = (new SafeSubstitution(m_Script, getVariableManager(), substitutionMapping)).transform(ps.getFormula());
		renamedFormula = SmtUtils.simplify(m_Script, renamedFormula, mServices);
		IPredicate result = this.getPredicateFactory().newPredicate(renamedFormula);
		return result;
	}


	// FIXME: does not work im SmtInterpol2

	public static void dumpInterpolProblem(Term[] formulas, int iterationNumber, int interpolProblem, String dumpPath,
			Script theory) {
		// String filename = "Iteration" + iterationNumber + "_InterpolProblem"
		// + interpolProblem + ".smt";
		// File file = new File(dumpPath + "/" +filename);
		// FileWriter fileWriter;
		// try {
		// fileWriter = new FileWriter(file);
		// PrintWriter printWriter = new PrintWriter(fileWriter);
		// fileWriter.close();
		// } catch (IOException e) {
		// e.printStackTrace();
		// }
	}

	// FIXME: does not work im SmtInterpol2
	static protected void dumpSatProblem(Term formula, int iterationNumber, int satProbNumber, String dumpPath,
			Script theory) {
		// String filename = "Iteration" + iterationNumber + "_SatProblem"
		// + satProbNumber + ".smt";
		// File file = new File(dumpPath + "/" +filename);
		// FileWriter fileWriter;
		// try {
		// fileWriter = new FileWriter(file);
		// PrintWriter printWriter = new PrintWriter(fileWriter);
		// fileWriter.close();
		// } catch (IOException e) {
		// e.printStackTrace();
		// }
	}

	public static HoareAnnotation getHoareAnnotation(ProgramPoint programPoint) {
		return HoareAnnotation.getAnnotation(programPoint);
	}

	public LBool checkSatWithFreeVars(Term negation) {
		LBool result = Util.checkSat(m_Script, negation);
		// if (result == LBool.UNKNOWN) {
		// Object[] reason = m_Script.getInfo(":reason-unknown");
		// }
		// de.uni_freiburg.informatik.ultimate.smtinterpol.util.ReasonUnknown
		// reasonUnknown = reason[0];
		return result;
	}

	// public class TermVarsProcs {
	// private final Term mTerm;
	// private final Set<BoogieVar> mVars;
	// private final Set<String> mProcs;
	//
	//
	//
	// }



	// public static Set<String> computeProcedures(Set<BoogieVar> vars) {
	// Set<String> result = new HashSet<String>();
	// for (BoogieVar bv : vars) {
	// if (bv.getProcedure() != null) {
	// result.add(bv.getProcedure());
	// }
	// }
	// return result;
	// }

	// public Predicate newPredicate(ProgramPoint pp, Term term,
	// Set<BoogieVar> vars) {
	// Term closedFormula = computeClosedFormula(term, vars, m_Script);
	// // if (varSetMinimalAssured && !varSetIsMinimal(vars, term,
	// // closedFormula)) {
	// // throw new AssertionError("VarSet not minimal");
	// // }
	// Predicate predicate = new Predicate(pp, term, vars, closedFormula);
	// return predicate;
	// }

	// @Deprecated
	// public Predicate newPredicate(ProgramPoint pp, Term term) {
	// Set<BoogieVar> vars = computeVars(term);
	// Predicate predicate = new Predicate(pp, term, vars, null);
	// return predicate;
	// }

	// public SPredicate newTrueSPredicateWithHistory(ProgramPoint pp) {
	// SPredicate predicate = new PredicateWithHistory(pp, m_SerialNumber++,
	// m_NoProcedure, m_Script.term("true"),
	// new HashSet<BoogieVar>(0), m_Script.term("true"), new
	// HashMap<Integer,Term>());
	// return predicate;
	// }


	// public SPredicate newSPredicate(ProgramPoint pp, String[] procedures,
	// Term term,
	// Set<BoogieVar> vars) {
	// Term closedFormula = computeClosedFormula(term, vars, m_Script);
	// SPredicate predicate = new SPredicate(pp, m_SerialNumber++, procedures,
	// term, vars, closedFormula);
	// return predicate;
	// }

//	public HoareAnnotation getNewHoareAnnotation(ProgramPoint pp) {
//		return new HoareAnnotation(pp, m_SerialNumber++, this, mServices);
//	}

	public ManagedScript getManagedScript() {
		return m_ManagedScript;
	}

//	Status getStatus() {
//		return m_Status;
//	}
//
//	void setStatus(Status status) {
//		m_Status = status;
//	}
	
	public void lock(Object lockOwner) {
		m_ManagedScript.lock(lockOwner);
	}
	
	public void unlock(Object lockOwner) {
		m_ManagedScript.unlock(lockOwner);
	}
	
	public boolean isLocked() {
		return m_ManagedScript.isLocked();
	}
	
	public boolean requestLockRelease() {
		return m_ManagedScript.requestLockRelease();
	}
	
	boolean isLockOwner(Object allegedLockOwner) {
		return m_ManagedScript.isLockOwner(allegedLockOwner);
	}



	public ModifiableGlobalVariableManager getModifiableGlobals() {
		return m_ModifiableGlobals;
	}
	
	


}
