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

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplicationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.RcfgPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.HoareAnnotation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashMap;

public class SmtManager {

	enum Status {
		IDLE, TRACECHECK, CODEBLOCKCHECK1, CODEBLOCKCHECK2, EDGECHECK
	};
	
	private final boolean mExtendedDebugOutputInScript = false;

//	private Status mStatus = Status.IDLE;

	private final Boogie2SMT mBoogie2Smt;
	private final Script mScript;
	private final SimplicationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;
	private final ManagedScript mManagedScript;
	// private final Map<String,ASTType> mGlobalVars;
	private final ModifiableGlobalVariableManager mModifiableGlobals;
	private int msatProbNumber;

	private ScopedHashMap<String, Term> mIndexedConstants;
	Set<IProgramVar> mAssignedVars;

	private final int mTrivialSatQueries = 0;
	private int mNontrivialSatQueries = 0;

	private int mTrivialCoverQueries = 0;
	private int mNontrivialCoverQueries = 0;

	// int mLazyEdgeCheckQueries = 0;
	// int mTrivialEdgeCheckQueries = 0;
	// int mNontrivialEdgeCheckQueries = 0;

	private final int mVarSetMinimalSolverQueries = 0;
	private final long mVarSetMinimalComputationTime = 0;

	long mSatCheckTime = 0;
	private long mSatCheckSolverTime = 0;
	private final long mTraceCheckTime = 0;
	private long mInterpolQuriesTime = 0;
	private int mInterpolQueries = 0;

	private final int mFreshVariableCouter = 0;

//	private long mTraceCheckStartTime = Long.MIN_VALUE;

	private final IUltimateServiceProvider mServices;

	private final ILogger mLogger;
	
	/**
	 * Switch to produce-interpolants mode before each trace check and leave the
	 * produce-interpolants mode afterwards
	 * (needed for princess it can only deal with quantifiers if not in
	 * produce-interpolants mode)
	 * 
	 */
	private final boolean mInterpolationModeSwitchNeeded;



	private final PredicateFactory mPredicateFactory;

	public SmtManager(final Script script, final Boogie2SMT boogie2smt, final ModifiableGlobalVariableManager modifiableGlobals,
			final IUltimateServiceProvider services, final boolean interpolationModeSwitchNeeded, final ManagedScript managedScript,
			final SimplicationTechnique simplificationTechnique, final XnfConversionTechnique xnfConversionTechnique) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;
		mInterpolationModeSwitchNeeded = interpolationModeSwitchNeeded;
		mBoogie2Smt = boogie2smt;
		mScript = script;
		mManagedScript = managedScript;
		mModifiableGlobals = modifiableGlobals;
		mPredicateFactory = new PredicateFactory(services, boogie2smt.getManagedScript(), boogie2smt.getBoogie2SmtSymbolTable(), simplificationTechnique, xnfConversionTechnique);
	}
	
	

//	public boolean isIdle() {
//		return getStatus() == Status.IDLE;
//	}

	// public Smt2Boogie getSmt2Boogie() {
	// return mSmt2Boogie;
	// }

	public PredicateFactory getPredicateFactory() {
		return mPredicateFactory;
	}



	public Boogie2SMT getBoogie2Smt() {
		return mBoogie2Smt;
	}

	public Script getScript() {
		return mScript;
	}

	private Term False() {
		return mScript.term("false");
	}

	private Term True() {
		return mScript.term("true");
	}

	@Deprecated
	private int getNontrivialSatQueries() {
		return mNontrivialSatQueries;
	}

	@Deprecated
	private int getTrivialSatQueries() {
		return mTrivialSatQueries;
	}

	@Deprecated
	private long getSatCheckSolverTime() {
		return mSatCheckSolverTime;
	}

	@Deprecated
	private long getInterpolQuriesTime() {
		return mInterpolQuriesTime;
	}

	@Deprecated
	private int getInterpolQueries() {
		return mInterpolQueries;
	}

	@Deprecated
	private long getTraceCheckTime() {
		return mTraceCheckTime;
	}

	@Deprecated
	private long getSatCheckTime() {
		return mSatCheckTime;
	}

	// public int getTrivialEdgeCheckQueries() {
	// return mTrivialEdgeCheckQueries;
	// }
	//
	// public int getLazyEdgeCheckQueries() {
	// return mLazyEdgeCheckQueries;
	// }
	//
	// public int getNontrivialEdgeCheckQueries() {
	// return mNontrivialEdgeCheckQueries;
	// }

	@Deprecated
	private int getTrivialCoverQueries() {
		return mTrivialCoverQueries;
	}

	@Deprecated
	private int getNontrivialCoverQueries() {
		return mNontrivialCoverQueries;
	}

	@Deprecated
	private int getVarSetMinimalSolverQueries() {
		return mVarSetMinimalSolverQueries;
	}

	@Deprecated
	private long getVarSetMinimalComputationTime() {
		return mVarSetMinimalComputationTime;
	}

	private void setIteration(final int iteration) {
		msatProbNumber = 0;
	}

	private int getSatProbNumber() {
		return msatProbNumber;
	}



	/**
	 * Returns a predicate which states that old(g)=g for all global variables g
	 * that are modifiable by procedure proc according to
	 * ModifiableGlobalVariableManager modGlobVarManager.
	 */
	public TermVarsProc getOldVarsEquality(final String proc, final ModifiableGlobalVariableManager modGlobVarManager) {
		final Set<IProgramVar> vars = new HashSet<IProgramVar>();
		Term term = getScript().term("true");
		for (final IProgramVar bv : modGlobVarManager.getGlobalVarsAssignment(proc).getAssignedVars()) {
			vars.add(bv);
			final IProgramVar bvOld = ((IProgramNonOldVar) bv).getOldVar();
			vars.add(bvOld);
			final TermVariable tv = bv.getTermVariable();
			final TermVariable tvOld = bvOld.getTermVariable();
			final Term equality = getScript().term("=", tv, tvOld);
			term = Util.and(getScript(), term, equality);
		}
		final String[] procs = new String[0];
		final TermVarsProc result = new TermVarsProc(term, vars, procs, PredicateUtils.computeClosedFormula(term, vars,
				getScript()));
		return result;

	}



	// private boolean varSetIsMinimal(Set<BoogieVar> boogieVars,
	// Term formula, Term closedFormula) {
	// assert isIdle();
	// long startTime = System.nanoTime();
	// mScript.push(1);
	// Term negated = mScript.term("not", closedFormula);
	// assertTerm(negated);
	// for (BoogieVar bv : boogieVars) {
	// TermVariable[] vars = new TermVariable[1];
	// vars[0] = bv.getTermVariable();
	// Term[] values = new Term[1];
	// values[0] = bv.getPrimedConstant();
	// formula = mScript.let(vars, values, formula);
	// formula = renameVarsToDefaultConstants(boogieVars, formula);
	//
	// mScript.push(1);
	// assertTerm(formula);
	// LBool sat = mScript.checkSat();
	// mVarSetMinimalSolverQueries++;
	// if (sat == LBool.UNSAT) {
	// // variable was not necessary
	// mScript.pop(2);
	// mVarSetMinimalComputationTime += (System.nanoTime() - startTime);
	// return false;
	// } else if (sat == LBool.SAT) {
	// mScript.pop(1);
	// } else if (sat == LBool.UNKNOWN) {
	// throw new AssertionError("if this case occurs, ask Matthias");
	// } else {
	// throw new AssertionError();
	// }
	// }
	// mVarSetMinimalComputationTime += (System.nanoTime() - startTime);
	// mScript.pop(1);
	// return true;
	// }

	public void startTraceCheck(final Object lockClaimer) {
		lock(lockClaimer);
		mScript.echo(new QuotedObject("starting trace check"));
		if (mInterpolationModeSwitchNeeded) {
			mScript.setOption(":produce-interpolants", true);
		}
		mScript.push(1);
	}

	public void endTraceCheck(final Object lockOwner) {
		if (mInterpolationModeSwitchNeeded) {
			mScript.setOption(":produce-interpolants", false);
		}
		mScript.echo(new QuotedObject("finished trace check"));
		mScript.pop(1);
		unlock(lockOwner);
	}
	
	private boolean interpolationModeSwitchNeeded() {
		final SolverMode solver = (mServices.getPreferenceProvider(Activator.PLUGIN_ID))
				.getEnum(RcfgPreferenceInitializer.LABEL_Solver, SolverMode.class);
		return solver == SolverMode.External_PrincessInterpolationMode;
	}

	// public void push() {
	// if (mIndexedConstants != null) {
	// throw new
	// AssertionError("During Trace Abstration only one additional level on stack allowed");
	// }
	// else {
	// mIndexedConstants = new HashMap<String, Term>();
	// mScript.push(1);
	// }
	// }
	// public void pop() {
	// if (mIndexedConstants == null) {
	// throw new AssertionError("Smt Manager has not pushed before");
	// }
	// else {
	// mIndexedConstants = null;
	// mScript.pop(1);
	// }
	// }

	private LBool checkSatisfiable(final Term f) {
		final long startTime = System.nanoTime();
		LBool result = null;
		try {
			assertTerm(f);
		} catch (final SMTLIBException e) {
			if (e.getMessage().equals("Unsupported non-linear arithmetic")) {
				return LBool.UNKNOWN;
			} else {
				throw e;
			}
		}
		result = mScript.checkSat();
		mSatCheckSolverTime += (System.nanoTime() - startTime);
		mNontrivialSatQueries++;
		if (result == LBool.UNKNOWN) {
			final Object info = mScript.getInfo(":reason-unknown");
			if (!(info instanceof ReasonUnknown)) {
				mScript.getInfo(":reason-unknown");
			}
			final ReasonUnknown reason = (ReasonUnknown) info;
			final Object test = mScript.getInfo(":reason-unknown");
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

	public LBool assertTerm(final Term term) {
		final long startTime = System.nanoTime();
		LBool result = null;
		result = mScript.assertTerm(term);
		mSatCheckSolverTime += (System.nanoTime() - startTime);
		return result;
	}

	public Term[] computeInterpolants(final Term[] interpolInput, final int[] startOfSubtree) {
		final long startTime = System.nanoTime();
		final Term[] result = mScript.getInterpolants(interpolInput, startOfSubtree);
		mInterpolQuriesTime += (System.nanoTime() - startTime);
		mInterpolQueries++;
		return result;
	}

	public Term[] computeInterpolants(final Term[] interpolInput) {
		final long startTime = System.nanoTime();
		final Term[] result = mScript.getInterpolants(interpolInput);
		mInterpolQuriesTime += (System.nanoTime() - startTime);
		mInterpolQueries++;
		return result;
	}



	// public Predicate simplify(Predicate ps) {
	// return mPredicateFactory.newPredicate(ps.getProgramPoint(),
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
	private LBool isCovered(final IPredicate ps1, final IPredicate ps2) {
		final long startTime = System.nanoTime();

		if (getPredicateFactory().isDontCare(ps1) || getPredicateFactory().isDontCare(ps2)) {
			mTrivialCoverQueries++;
			return Script.LBool.UNKNOWN;
		}

		final Term formula1 = ps1.getFormula();
		final Term formula2 = ps2.getFormula();
		LBool result = null;
		// tivial case
		if (formula1 == False() || formula2 == True()) {
			mTrivialCoverQueries++;
			result = Script.LBool.UNSAT;
		} else {
			mScript.push(1);
			mIndexedConstants = new ScopedHashMap<String, Term>();
			Term negImpl = Util.and(mScript, formula1, SmtUtils.not(mScript, formula2));

			// replace all vars by constants
			{
				final TermVariable[] vars = new TermVariable[ps1.getVars().size()];
				final Term[] values = new Term[vars.length];
				int i = 0;
				for (final IProgramVar var : ps1.getVars()) {
					vars[i] = var.getTermVariable();
					values[i] = var.getDefaultConstant();
					i++;
				}
				negImpl = mScript.let(vars, values, negImpl);
			}

			{
				final TermVariable[] vars = new TermVariable[ps2.getVars().size()];
				final Term[] values = new Term[vars.length];
				int i = 0;
				for (final IProgramVar var : ps2.getVars()) {
					vars[i] = var.getTermVariable();
					values[i] = var.getDefaultConstant();
					i++;
				}
				negImpl = mScript.let(vars, values, negImpl);
			}

			mNontrivialCoverQueries++;
			result = checkSatisfiable(negImpl);
			mIndexedConstants = null;
			mScript.pop(1);
		}
		mSatCheckTime += (System.nanoTime() - startTime);
		return result;
	}

	private Validity isCovered(final Object caller, final Term formula1, final Term formula2) {
		assert (mManagedScript.isLockOwner(caller)) : "only lock owner may call";
		final long startTime = System.nanoTime();

		final Validity result;
		// tivial case
		if (formula1 == False() || formula2 == True()) {
			mTrivialCoverQueries++;
			result = Validity.VALID;
		} else {
			mScript.push(1);
			assertTerm(formula1);
			final Term negFormula2 = mScript.term("not", formula2);
			assertTerm(negFormula2);
			result = IHoareTripleChecker.lbool2validity(mScript.checkSat());
			mNontrivialCoverQueries++;
			mScript.pop(1);
		}
		mSatCheckTime += (System.nanoTime() - startTime);
		if (mExtendedDebugOutputInScript && result == Validity.UNKNOWN) {
			mScript.echo(new QuotedObject("Result of preceeding check-sat was UNKNOWN"));
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

	private Term substituteRepresentants(final Set<IProgramVar> boogieVars, final Map<IProgramVar, TermVariable> substitution, final Term term) {
		final ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
		final ArrayList<Term> replacers = new ArrayList<Term>();

		for (final IProgramVar var : boogieVars) {
			final TermVariable representant = var.getTermVariable();
			assert representant != null;
			final Term substitute = substitution.get(var);
			assert substitute != null;
			replacees.add(representant);
			replacers.add(substitute);
		}
		final TermVariable[] vars = replacees.toArray(new TermVariable[replacees.size()]);
		final Term[] values = replacers.toArray(new Term[replacers.size()]);
		Term result = mScript.let(vars, values, term);
		result = (new FormulaUnLet()).unlet(result);
		return result;
	}

	private Term substituteToRepresentants(final Set<IProgramVar> boogieVars, final Map<IProgramVar, TermVariable> boogieVar2TermVar,
			final Term term) {
		final ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
		final ArrayList<Term> replacers = new ArrayList<Term>();

		for (final IProgramVar var : boogieVars) {
			final TermVariable representant = boogieVar2TermVar.get(var);
			assert representant != null;
			final Term substitute = var.getTermVariable();
			assert substitute != null;
			replacees.add(representant);
			replacers.add(substitute);
		}
		final TermVariable[] vars = replacees.toArray(new TermVariable[replacees.size()]);
		final Term[] values = replacers.toArray(new Term[replacers.size()]);
		Term result = mScript.let(vars, values, term);
		result = (new FormulaUnLet()).unlet(result);
		return result;
	}

	private Term substituteTermVariablesByTerms(final Map<TermVariable, Term> substitution, final Term term) {
		final ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
		final ArrayList<Term> replacers = new ArrayList<Term>();

		for (final TermVariable tv : substitution.keySet()) {
			final Term replacer = substitution.get(tv);
			assert replacer != null;
			replacees.add(tv);
			replacers.add(replacer);
		}
		final TermVariable[] vars = replacees.toArray(new TermVariable[replacees.size()]);
		final Term[] values = replacers.toArray(new Term[replacers.size()]);
		Term result = mScript.let(vars, values, term);
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
	// Term constant = mIndexedConstants.get(name);
	// if (constant == null) {
	// Sort resultSort =
	// mBoogie2Smt.getTypeSortTranslator().getSort(var.getIType(), null);
	// Sort[] emptySorts = {};
	// mScript.declareFun(name, emptySorts, resultSort);
	// Term[] emptyTerms = {};
	// constant = mScript.term(name, emptyTerms);
	// mIndexedConstants.put(name, constant);
	// }
	// return constant;
	// }

	// public Term getFreshConstant(TermVariable tv) {
	// String name = "fresh_" + tv.getName() + mFreshVariableCouter++;
	// Sort resultSort = tv.getSort();
	// Sort[] emptySorts = {};
	// mScript.declareFun(name, emptySorts, resultSort);
	// Term[] emptyTerms = {};
	// return mScript.term(name, emptyTerms);
	// }

	// public TermVariable getFreshTermVariable(String identifier, Sort sort) {
	// String name = "fresh_" + identifier + mFreshVariableCouter++;
	// TermVariable result = mScript.variable(name, sort);
	// return result;
	// }

	/**
	 * @param int >=-1
	 * @return String representation of number, where -1 is represented as
	 *         <i>init</i>
	 */
	private static String quoteMinusOne(final int index) {
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
	// Term result = mIndexedConstants.get(name);
	// if (result == null) {
	// Sort[] emptySorts = {};
	// mScript.declareFun(name, emptySorts, sort);
	// Term[] emptyTerms = {};
	// result = mScript.term(name, emptyTerms);
	// mIndexedConstants.put(name, result);
	// }
	// return result;
	// }

	// @Deprecated
	// private Term getOldVarConstant(String varName, Sort sort) {
	// String name = "c_"+varName+"_OLD";
	// Term result = mIndexedConstants.get(name);
	// if (result == null) {
	// Sort[] emptySorts = {};
	// mScript.declareFun(name, emptySorts, sort);
	// Term[] emptyTerms = {};
	// result = mScript.term(name, emptyTerms);
	// mIndexedConstants.put(name, result);
	// }
	// return result;
	// }

	private Integer quantifiersContainedInFormula(final Term formula, final Set<TermVariable> quantifiedVariables) {
		Integer quantifier = null;
		if (formula instanceof ApplicationTerm) {
			final Term[] parameters = ((ApplicationTerm) formula).getParameters();
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
	public IPredicate renameGlobalsToOldGlobals(final IPredicate ps) {
		if (getPredicateFactory().isDontCare(ps)) {
			throw new UnsupportedOperationException("don't cat not expected");
		}

		final Set<IProgramVar> allVars = ps.getVars();
		final Set<IProgramVar> varsOfRenamed = new HashSet<IProgramVar>();
		varsOfRenamed.addAll(allVars);
		final Set<IProgramVar> globalVars = new HashSet<IProgramVar>();
		for (final IProgramVar var : allVars) {
			if (var.isGlobal()) {
				globalVars.add(var);
				varsOfRenamed.remove(var);
			}
		}
		final Map<Term, Term> substitutionMapping = new HashMap<Term, Term>();
		for (final IProgramVar globalBoogieVar : globalVars) {
			if (!globalBoogieVar.isOldvar()) {
				final IProgramVar oldBoogieVar = ((IProgramNonOldVar) globalBoogieVar).getOldVar();
				varsOfRenamed.add(oldBoogieVar);
				substitutionMapping.put(globalBoogieVar.getTermVariable(), oldBoogieVar.getTermVariable());
			}
		}
		Term renamedFormula = (new Substitution(getManagedScript(), substitutionMapping)).transform(ps.getFormula());
		renamedFormula = SmtUtils.simplify(getManagedScript(), renamedFormula, mServices, mSimplificationTechnique);
		final IPredicate result = getPredicateFactory().newPredicate(renamedFormula);
		return result;
	}


	// FIXME: does not work im SmtInterpol2

	private static void dumpInterpolProblem(final Term[] formulas, final int iterationNumber, final int interpolProblem, final String dumpPath,
			final Script theory) {
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
	static private void dumpSatProblem(final Term formula, final int iterationNumber, final int satProbNumber, final String dumpPath,
			final Script theory) {
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

	private static HoareAnnotation getHoareAnnotation(final ProgramPoint programPoint) {
		return HoareAnnotation.getAnnotation(programPoint);
	}

	private LBool checkSatWithFreeVars(final Term negation) {
		final LBool result = Util.checkSat(mScript, negation);
		// if (result == LBool.UNKNOWN) {
		// Object[] reason = mScript.getInfo(":reason-unknown");
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
	// Term closedFormula = computeClosedFormula(term, vars, mScript);
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
	// SPredicate predicate = new PredicateWithHistory(pp, mSerialNumber++,
	// mNoProcedure, mScript.term("true"),
	// new HashSet<BoogieVar>(0), mScript.term("true"), new
	// HashMap<Integer,Term>());
	// return predicate;
	// }


	// public SPredicate newSPredicate(ProgramPoint pp, String[] procedures,
	// Term term,
	// Set<BoogieVar> vars) {
	// Term closedFormula = computeClosedFormula(term, vars, mScript);
	// SPredicate predicate = new SPredicate(pp, mSerialNumber++, procedures,
	// term, vars, closedFormula);
	// return predicate;
	// }

//	public HoareAnnotation getNewHoareAnnotation(ProgramPoint pp) {
//		return new HoareAnnotation(pp, mSerialNumber++, this, mServices);
//	}

	public ManagedScript getManagedScript() {
		return mManagedScript;
	}

//	Status getStatus() {
//		return mStatus;
//	}
//
//	void setStatus(Status status) {
//		mStatus = status;
//	}
	
	public void lock(final Object lockOwner) {
		mManagedScript.lock(lockOwner);
	}
	
	public void unlock(final Object lockOwner) {
		mManagedScript.unlock(lockOwner);
	}
	
	public boolean isLocked() {
		return mManagedScript.isLocked();
	}
	
	public boolean requestLockRelease() {
		return mManagedScript.requestLockRelease();
	}
	
	boolean isLockOwner(final Object allegedLockOwner) {
		return mManagedScript.isLockOwner(allegedLockOwner);
	}



	public ModifiableGlobalVariableManager getModifiableGlobals() {
		return mModifiableGlobals;
	}
	
	


}
