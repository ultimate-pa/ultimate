/*
 * Copyright (C) 2013-2015 Jochen Hoenicke (hoenicke@informatik.uni-freiburg.de)
 * Copyright (C) 2017-2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2018 University of Freiburg
 *
 * This file is part of the ULTIMATE PEAtoBoogie plug-in.
 *
 * The ULTIMATE PEAtoBoogie plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE PEAtoBoogie plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE PEAtoBoogie plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PEAtoBoogie plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE PEAtoBoogie plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.pea2boogie.generator;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger.LogLevel;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.BoogieConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.BoogieDeclarations;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.QuantifierPusher;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.pea.Phase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.Transition;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType.ReqPeas;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.pea2boogie.CddToSmt;
import de.uni_freiburg.informatik.ultimate.pea2boogie.IReqSymbolTable;
import de.uni_freiburg.informatik.ultimate.pea2boogie.PeaResultUtil;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.DAGSize;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.util.datastructures.CrossProducts;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class RtInconcistencyConditionGenerator {

	private static final boolean ONLY_CONJUNCTIVE_INVARIANTS = false;

	private static final boolean SIMPLIFY_BEFORE_QELIM = false;
	private static final boolean TRY_SOLVER_BEFORE_QELIM = false;
	private static final boolean PRINT_STATS = true;
	private static final boolean PRINT_QUANTIFIED_FORMULAS = false;

	private static final String SOLVER_LOG_DIR = null;
	// private static final String SOLVER_LOG_DIR = "C:\\Users\\firefox\\Desktop\\dump\\";

	private static final boolean PRINT_NON_TRIVIAL_CHECKS = false;

	private final IReqSymbolTable mReqSymboltable;
	private final Term mPrimedInvariant;
	private final Script mScript;
	private final Term mTrue;
	private final Term mFalse;
	private final ManagedScript mManagedScript;
	private final Boogie2SMT mBoogie2Smt;
	private final Map<String, IProgramNonOldVar> mVars;
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final boolean mSeparateInvariantHandling;
	private final CddToSmt mCddToSmt;

	private final Map<Term, Term> mProjectionCache;
	private final Map<Phase, Term> mPhaseTermCache;

	private int mQuantified;
	private int mPlain;
	private int mAfterSize;
	private int mBeforeSize;
	private int mTrivialConsistent;
	private int mGeneratedChecks;
	private int mQuantifiedQuery;
	private int mQelimQuery;

	private final Substitution mConstInliner;

	private final ILogger mPQELogger;

	public RtInconcistencyConditionGenerator(final ILogger logger, final IUltimateServiceProvider services,
			final PeaResultUtil peaResultUtil, final IReqSymbolTable symboltable, final List<ReqPeas> reqPeas,
			final BoogieDeclarations boogieDeclarations, final boolean separateInvariantHandling)
			throws InvariantInfeasibleException {
		mReqSymboltable = symboltable;
		mServices = services;
		mLogger = logger;
		mPQELogger =
				mServices.getLoggingService().getLogger(RtInconcistencyConditionGenerator.class.getName() + ".PQE");
		// manually disable log flood
		mPQELogger.setLevel(LogLevel.WARN);
		mServices.getLoggingService().setLogLevel(QuantifierPusher.class, LogLevel.WARN);

		mScript = buildSolver(services);
		mManagedScript = new ManagedScript(services, mScript);
		mTrue = mScript.term("true");
		mFalse = mScript.term("false");

		mBoogie2Smt = new Boogie2SMT(mManagedScript, boogieDeclarations, false, services, false);
		mVars = mBoogie2Smt.getBoogie2SmtSymbolTable().getGlobalsMap();
		mSeparateInvariantHandling = separateInvariantHandling;
		mPhaseTermCache = new HashMap<>();
		mProjectionCache = new HashMap<>();
		mQuantified = 0;
		mPlain = 0;
		mBeforeSize = 0;
		mAfterSize = 0;
		mTrivialConsistent = 0;
		mGeneratedChecks = 0;
		mQuantifiedQuery = 0;
		mQelimQuery = 0;
		mCddToSmt = new CddToSmt(services, peaResultUtil, mScript, mBoogie2Smt, boogieDeclarations, mReqSymboltable);
		final Map<Term, Term> constToValue = createConst2Value(mScript, mReqSymboltable, mBoogie2Smt);
		mConstInliner = new Substitution(mScript, constToValue);

		if (mSeparateInvariantHandling) {
			mPrimedInvariant = constructPrimedStateInvariant(reqPeas);
			mLogger.info("Finished generating primed state invariant of size " + new DAGSize().size(mPrimedInvariant));
		} else {
			mPrimedInvariant = mTrue;
		}
	}

	private static Map<Term, Term> createConst2Value(final Script script, final IReqSymbolTable reqSymboltable,
			final Boogie2SMT boogieToSmt) {
		final Map<String, Expression> constToValue = reqSymboltable.getConstToValue();
		final Map<String, BoogieConst> boogieConsts = boogieToSmt.getBoogie2SmtSymbolTable().getConstsMap();

		final Map<Term, Term> rtr = new HashMap<>();
		for (final Entry<String, Expression> constEntry : constToValue.entrySet()) {
			final BoogieConst programConst = boogieConsts.get(constEntry.getKey());
			final Term value = literalToTerm(script, constEntry.getValue());
			rtr.put(programConst.getTerm(), value);
		}

		return rtr;
	}

	private static Term literalToTerm(final Script script, final Expression expr) {
		if (expr instanceof RealLiteral) {
			return SmtUtils.toRational(((RealLiteral) expr).getValue()).toTerm(SmtSortUtils.getRealSort(script));
		} else if (expr instanceof IntegerLiteral) {
			return SmtUtils.toRational(((IntegerLiteral) expr).getValue()).toTerm(SmtSortUtils.getIntSort(script));
		} else if (expr instanceof BooleanLiteral) {
			if (((BooleanLiteral) expr).getValue()) {
				return script.term("true");
			}
			return script.term("false");
		} else if (expr instanceof UnaryExpression) {
			final UnaryExpression uexpr = (UnaryExpression) expr;
			if (uexpr.getOperator() == Operator.ARITHNEGATIVE) {
				return SmtUtils.neg(script, literalToTerm(script, uexpr.getExpr()));
			}
		}
		throw new IllegalArgumentException(BoogiePrettyPrinter.print(expr) + " is no literal");
	}

	/**
	 * Return a subset of requirements that should be used for generating rt-inconsistency checks.
	 */
	public List<Entry<PatternType<?>, PhaseEventAutomata>> getRelevantRequirements(final List<ReqPeas> reqPeas) {
		// we only consider automata that do not represent invariants or which have a disjunctive invariant
		final List<Entry<PatternType<?>, PhaseEventAutomata>> rtr = new ArrayList<>();
		for (final ReqPeas reqPea : reqPeas) {
			final PatternType<?> pattern = reqPea.getPattern();
			for (final Entry<CounterTrace, PhaseEventAutomata> pea : reqPea.getCounterTrace2Pea()) {
				rtr.add(new Pair<>(pattern, pea.getValue()));
			}
		}

		if (mSeparateInvariantHandling) {
			return rtr.stream().filter(a -> filterReqs(a.getValue())).collect(Collectors.toList());
		}
		return rtr;
	}

	/**
	 * Return true for this entry if it should not be considered for rt-inconsistency checks (i.e., if it does not
	 * represent an invariant)
	 *
	 * @param entry
	 * @return
	 */
	private boolean filterReqs(final PhaseEventAutomata pea) {
		final Phase[] phases = pea.getPhases();
		if (phases.length != 1) {
			// this is not an invariant, filter it out
			return true;
		}
		if (!ONLY_CONJUNCTIVE_INVARIANTS) {
			// if we take all invariants, we are finished here
			return false;
		}
		assert phases.length == 1;
		final Term stateInv = mCddToSmt.toSmt(phases[0].getStateInvariant());
		// this is an invariant with a top-level disjunction, filter it out
		return SmtUtils.getDisjuncts(stateInv).length != 1;
	}

	private static Script buildSolver(final IUltimateServiceProvider services) throws AssertionError {

		SolverSettings settings =
				SolverBuilder.constructSolverSettings().setSolverMode(SolverMode.External_ModelsAndUnsatCoreMode)
						.setUseExternalSolver(true, SolverBuilder.COMMAND_Z3_NO_TIMEOUT, Logics.ALL);
		// SolverSettings settings =
		// SolverBuilder.constructSolverSettings().setSolverMode(SolverMode.Internal_SMTInterpol)
		// .setSolverLogics(Logics.ALL);
		if (SOLVER_LOG_DIR != null) {
			settings = settings.setDumpSmtScriptToFile(true, SOLVER_LOG_DIR,
					RtInconcistencyConditionGenerator.class.getSimpleName(), false);
		}
		return SolverBuilder.buildAndInitializeSolver(services, settings, "RtInconsistencySolver");
	}

	public Expression nonDLCGenerator(final PhaseEventAutomata[] automata) {
		final int[][] phases = createPhasePairs(automata);

		final List<int[]> phasePermutations = CrossProducts.crossProduct(phases);
		final List<Term> rtInconsistencyChecks = new ArrayList<>();
		for (final int[] vector : phasePermutations) {
			assert vector.length == automata.length;
			final List<Term> outer = new ArrayList<>();
			final List<Term> impliesLHS = new ArrayList<>();
			for (int j = 0; j < vector.length; j++) {
				final PhaseEventAutomata automaton = automata[j];
				final int phaseIndex = vector[j];
				final String pcName = mReqSymboltable.getPcName(automaton);
				impliesLHS.add(genPCCompEQ(pcName, phaseIndex));
				final Phase phase = automaton.getPhases()[phaseIndex];
				final Term phaseDisjunction = getPhaseTerm(phase);
				outer.add(phaseDisjunction);
			}

			// first, compute rhs without primed invariant
			final Term checkPrimedRhs = SmtUtils.and(mScript, outer);
			final Term checkPrimedRhsAndPrimedInvariant = SmtUtils.and(mScript, checkPrimedRhs, mPrimedInvariant);
			final Term checkRhsAndInvariant = existentiallyProjectEventsAndPrimedVars(checkPrimedRhsAndPrimedInvariant);
			if (checkRhsAndInvariant instanceof QuantifiedFormula) {
				mQuantified++;
			} else {
				mPlain++;
			}
			if (checkRhsAndInvariant == mTrue) {
				continue;
			}

			final Term rtInconsistencyCheckLhs = SmtUtils.and(mScript, impliesLHS);
			final Term rtInconsistencyCheck = SmtUtils.implies(mScript, rtInconsistencyCheckLhs, checkRhsAndInvariant);
			rtInconsistencyChecks.add(rtInconsistencyCheck);
		}
		if (rtInconsistencyChecks.isEmpty()) {
			mTrivialConsistent++;
			return null;
		}
		mGeneratedChecks++;
		final Term finalCheck = SmtUtils.and(mScript, rtInconsistencyChecks);
		if (PRINT_NON_TRIVIAL_CHECKS) {
			mLogger.info("Adding non-trivial check: %s", finalCheck.toStringDirect());
		}
		return mBoogie2Smt.getTerm2Expression().translate(finalCheck);
	}

	private void printQuantifiedFormula(final String prefix, final Supplier<QuantifiedFormula> formulaSuppl) {
		if (!PRINT_QUANTIFIED_FORMULAS) {
			return;
		}
		final QuantifiedFormula formula = formulaSuppl.get();
		final TermVariable[] quantVars = formula.getVariables();
		final TermVariable[] newQuantVars = new TermVariable[quantVars.length];
		final Map<Term, Term> subst = new HashMap<>();
		final Set<Term> oldVars = new HashSet<>();
		for (int i = 0; i < quantVars.length; ++i) {
			final TermVariable var = quantVars[i];
			final TermVariable newVar = mScript.variable(CoreUtil.alphabeticalSequence(i), var.getSort());
			newQuantVars[i] = newVar;
			oldVars.add(var);
			subst.put(var, newVar);
		}
		assert subst.values().stream().anyMatch(oldVars::contains) : "Var with same name already exists";
		final Term subForm = new Substitution(mScript, subst).transform(formula.getSubformula());
		final Term renamedQuantifiedFormula =
				mScript.quantifier(formula.getQuantifier(), newQuantVars, subForm, new Term[0]);
		mLogger.info(prefix + ": Renamed quantified formula: " + renamedQuantifiedFormula.toStringDirect());
	}

	public void logStats() {
		mLogger.info(String.format("%s checks, %s trivial consistent, %s non-trivial",
				mGeneratedChecks + mTrivialConsistent, mTrivialConsistent, mGeneratedChecks));
		if (!PRINT_STATS) {
			return;
		}
		mLogger.info(String.format(
				"Of %s formulas, %s were quantified, %s were plain. Needed %s quantifier elimination runs, %s quantified solver queries.",
				mQuantified + mPlain, mQuantified, mPlain, mQelimQuery, mQuantifiedQuery));
		if (SIMPLIFY_BEFORE_QELIM) {
			mLogger.info(String.format("Terms of DAG size %s were simplified to DAG size %s (%s percent reduction)",
					mBeforeSize, mAfterSize, 100.0 - mAfterSize * 1.0 / (mBeforeSize * 1.0) * 100.0));
		}
	}

	private Term getPhaseTerm(final Phase phase) {
		Term phaseTerm = mPhaseTermCache.get(phase);
		if (phaseTerm == null) {
			phaseTerm = generatePhaseLeaveTerm(phase);
			final Term old = mPhaseTermCache.put(phase, phaseTerm);
			assert old == null;
		} else {
			assert isCacheWorking(phase, phaseTerm) : "Cache fails";
		}
		return phaseTerm;
	}

	private boolean isCacheWorking(final Phase phase, final Term cachedPhaseTerm) {
		final Term gPhaseTerm = generatePhaseLeaveTerm(phase);
		if (gPhaseTerm != cachedPhaseTerm) {
			mLogger.fatal("Cache failed");
			mLogger.fatal("Cached term:    " + cachedPhaseTerm.toStringDirect());
			mLogger.fatal("Generated term: " + gPhaseTerm.toStringDirect());
		}
		return gPhaseTerm == cachedPhaseTerm;
	}

	private Term generatePhaseLeaveTerm(final Phase phase) {
		final List<Term> inner = new ArrayList<>();
		for (final Transition trans : phase.getTransitions()) {
			final Term guardTerm = mCddToSmt.toSmt(trans.getGuard());
			final CDD cddPrimedStInv = trans.getDest().getStateInvariant().prime(mReqSymboltable.getConstVars());
			final CDD cddStrictInv =
					new StrictInvariant().genStrictInv(trans.getDest().getClockInvariant(), trans.getResets());
			final Term primedStInv = mCddToSmt.toSmt(cddPrimedStInv);
			final Term strictInv = mCddToSmt.toSmt(cddStrictInv);
			inner.add(SmtUtils.and(mScript, guardTerm, primedStInv, strictInv));
		}
		return SmtUtils.or(mScript, inner);
	}

	private Term simplifyAndLog(final Term term) {
		if (!SIMPLIFY_BEFORE_QELIM) {
			return term;
		}

		mBeforeSize = mBeforeSize + new DAGSize().size(term);
		final Term simplified = simplify(term);
		mAfterSize = mAfterSize + new DAGSize().size(simplified);
		return simplified;
	}

	private Term simplify(final Term term) {
		return SmtUtils.simplify(mManagedScript, term, mServices, SimplificationTechnique.SIMPLIFY_DDA);
	}

	private Term constructPrimedStateInvariant(final List<ReqPeas> reqPeas) throws InvariantInfeasibleException {

		final Map<PatternType<?>, CDD> primedStateInvariants = new HashMap<>();
		for (final ReqPeas reqpea : reqPeas) {
			for (final Entry<CounterTrace, PhaseEventAutomata> pea : reqpea.getCounterTrace2Pea()) {
				if (filterReqs(pea.getValue())) {
					// this is not an invariant we want to consider
					continue;
				}
				primedStateInvariants.put(reqpea.getPattern(),
						pea.getValue().getPhases()[0].getStateInvariant().prime(mReqSymboltable.getConstVars()));
			}
		}

		final Term result;
		final Map<PatternType<?>, Term> terms;
		if (primedStateInvariants.isEmpty()) {
			return mTrue;
		} else if (primedStateInvariants.size() == 1) {
			final Entry<PatternType<?>, CDD> entry = primedStateInvariants.entrySet().iterator().next();
			result = mCddToSmt.toSmt(entry.getValue());
			terms = Collections.singletonMap(entry.getKey(), result);
		} else {
			terms = primedStateInvariants.entrySet().stream()
					.collect(Collectors.toMap(Entry::getKey, a -> mCddToSmt.toSmt(a.getValue())));
			result = SmtUtils.and(mScript, terms.values());
		}
		return handleInconsistentStateInvariant(terms, simplify(handleInconsistentStateInvariant(terms, result)));
	}

	private Term handleInconsistentStateInvariant(final Map<PatternType<?>, Term> terms, final Term invariant)
			throws InvariantInfeasibleException {
		if (mFalse != invariant) {
			return invariant;
		}

		final Function<TermVariable, IProgramVar> funTermVar2ProgVar = a -> mVars.get(a.getName());
		final SimplePredicateFactory pfac = new SimplePredicateFactory(mManagedScript, funTermVar2ProgVar);
		mScript.push(1);
		final Map<Term, PatternType<?>> name2Req = new HashMap<>();
		for (final Entry<PatternType<?>, Term> entry : terms.entrySet()) {
			final Term term = entry.getValue();
			final BasicPredicate pred = pfac.newPredicate(term);
			final Term namedTerm = SmtUtils.annotateAndAssert(mScript, pred.getClosedFormula(), entry.getKey().getId());
			name2Req.put(namedTerm, entry.getKey());
		}
		final LBool result = mScript.checkSat();
		assert result == LBool.UNSAT;
		final Collection<PatternType<?>> responsibleRequirements = new HashSet<>();
		final Term[] unsatCore = mScript.getUnsatCore();
		Arrays.stream(unsatCore).map(a -> name2Req.get(a)).forEach(responsibleRequirements::add);
		mScript.pop(1);
		throw new InvariantInfeasibleException(responsibleRequirements);
	}

	private Term getTermVarTerm(final String name) {
		final IProgramNonOldVar termVar = mVars.get(name);
		return termVar.getTerm();
	}

	private Term existentiallyProjectEventsAndPrimedVars(final Term term) {
		final Term cachedResult = mProjectionCache.get(term);
		if (cachedResult != null) {
			return cachedResult;
		}
		final Term rtr = computeExistentialProjection(term);
		mProjectionCache.put(term, rtr);
		return rtr;
	}

	private Term computeExistentialProjection(final Term term) {
		final Term inlinedConstsTerm = inlineConsts(term);
		final Term simplifiedTerm = simplifyAndLog(inlinedConstsTerm);
		final Set<TermVariable> varsToRemove = getPrimedAndEventVars(simplifiedTerm.getFreeVars());
		if (varsToRemove.isEmpty()) {
			return term;
		}
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Removing " + varsToRemove.size() + " variables");
		}
		final QuantifiedFormula quantifiedFormula = (QuantifiedFormula) SmtUtils.quantifier(mScript,
				QuantifiedFormula.EXISTS, varsToRemove, simplifiedTerm);
		if (TRY_SOLVER_BEFORE_QELIM && querySolverIsTrue(quantifiedFormula)) {
			return mTrue;
		}
		mQelimQuery++;
		final Term afterQelimFormula;
		try {
			afterQelimFormula = PartialQuantifierElimination.tryToEliminate(mServices, mPQELogger, mManagedScript,
					quantifiedFormula, SimplificationTechnique.NONE,
					XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
		} catch (final SMTLIBException ex) {
			mLogger.fatal("Exception occured during PQE of " + term);
			throw ex;
		}

		if (afterQelimFormula instanceof QuantifiedFormula) {
			// qelim failed to eliminate all quantifiers, perhaps the solver is better?
			printQuantifiedFormula("Before qelim", () -> quantifiedFormula);
			printQuantifiedFormula("After qelim", () -> (QuantifiedFormula) afterQelimFormula);

			if (querySolverIsTrue(afterQelimFormula)) {
				return mTrue;
			}
			printQuantifiedFormula("After solver", () -> (QuantifiedFormula) afterQelimFormula);
		}
		return afterQelimFormula;
	}

	private Term inlineConsts(final Term term) {
		return mConstInliner.transform(term);
	}

	private boolean querySolverIsTrue(final Term term) {
		final Term isTrueTerm = mScript.term("distinct", mTrue, term);
		if (term instanceof QuantifiedFormula) {
			mQuantifiedQuery++;
		}
		final LBool result = SmtUtils.checkSatTerm(mScript, isTrueTerm);
		return result == LBool.UNSAT;
	}

	private Set<TermVariable> getPrimedAndEventVars(final TermVariable[] freeVars) {
		final Set<TermVariable> rtr = new HashSet<>();
		final Set<String> primedVars = mReqSymboltable.getPrimedVars();
		final Set<String> eventVars = mReqSymboltable.getEventVars();
		final Set<String> stateVars = (Set<String>) mReqSymboltable.getStateVars();
		for (final TermVariable var : freeVars) {
			final Expression expr = mBoogie2Smt.getTerm2Expression().translate(var);
			if (expr instanceof IdentifierExpression) {
				final String name = ((IdentifierExpression) expr).getIdentifier();
				if (primedVars.contains(name) || eventVars.contains(name) || stateVars.contains(name)) {
					rtr.add(var);
				}
			} else {
				throw new AssertionError();
			}
		}

		return rtr;
	}

	private static int[][] createPhasePairs(final PhaseEventAutomata[] automata) {
		final int[][] phases = new int[automata.length][];
		for (int i = 0; i < automata.length; i++) {
			final PhaseEventAutomata automaton = automata[i];
			final int phaseCount = automaton.getPhases().length;
			phases[i] = new int[phaseCount];
			for (int j = 0; j < phaseCount; j++) {
				phases[i][j] = j;
			}
		}
		return phases;
	}

	private Term genPCCompEQ(final String pcName, final int phaseIndex) {
		return SmtUtils.binaryEquality(mScript, getTermVarTerm(pcName), mScript.numeral(Integer.toString(phaseIndex)));
	}

	public static final class InvariantInfeasibleException extends Exception {

		private static final long serialVersionUID = 1L;
		private final Collection<PatternType<?>> mResponsibleRequirements;

		private InvariantInfeasibleException(final Collection<PatternType<?>> responsibleRequirements) {
			super("Some invariants are already infeasible. Responsible requirements: "
					+ responsibleRequirements.stream().map(a -> a.getId()).collect(Collectors.joining(", ")));
			mResponsibleRequirements = responsibleRequirements;
		}

		public Collection<PatternType<?>> getResponsibleRequirements() {
			return mResponsibleRequirements;
		}

	}

}
