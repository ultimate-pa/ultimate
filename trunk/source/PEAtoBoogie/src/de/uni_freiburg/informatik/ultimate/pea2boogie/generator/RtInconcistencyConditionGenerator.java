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

import java.io.FileNotFoundException;
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
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.GeneratedBoogieAstTransformer;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.pea.BoogieBooleanExpressionDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.BooleanDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.Decision;
import de.uni_freiburg.informatik.ultimate.lib.pea.EventDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.Phase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.pea.RangeDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.Transition;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieDeclarations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Expression2Term.IIdentifierTranslator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Expression2Term.SingleTermResult;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.QuantifierPusher.PqeTechniques;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.pea2boogie.translator.ReqSymboltable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.DAGSize;
import de.uni_freiburg.informatik.ultimate.util.datastructures.CrossProducts;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class RtInconcistencyConditionGenerator {

	private static final boolean SIMPLIFY_BEFORE_QELIM = false;
	private static final boolean TRY_SOLVER_BEFORE_QELIM = true;
	private static final boolean PRINT_STATS = false;
	private static final String SOLVER_LOGFILE = null;

	private final ReqSymboltable mBoogieSymboltable;
	private final Term mPrimedInvariant;
	private final Script mScript;
	private final Term mTrue;
	private final Term mFalse;
	private final ManagedScript mManagedScript;
	private final Boogie2SMT mBoogie2Smt;
	private final Map<String, IProgramNonOldVar> mVars;
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final IIdentifierTranslator[] mIdentifierTranslators;
	private final boolean mSeparateInvariantHandling;

	private final Map<Phase, Term> mPhaseTermCache;
	private int mQuantified;
	private int mPlain;
	private int mAfterSize;
	private int mBeforeSize;
	private int mTrivialConsistent;
	private int mGeneratedChecks;
	private int mNoQelim;
	private int mQelim;

	public RtInconcistencyConditionGenerator(final ILogger logger, final IUltimateServiceProvider services,
			final IToolchainStorage storage, final ReqSymboltable symboltable,
			final Map<PatternType, PhaseEventAutomata> req2Automata, final BoogieDeclarations boogieDeclarations,
			final boolean separateInvariantHandling) throws InvariantInfeasibleException {
		mBoogieSymboltable = symboltable;
		mServices = services;
		mLogger = logger;
		mScript = buildSolver(services, storage);
		mManagedScript = new ManagedScript(services, mScript);
		mTrue = mScript.term("true");
		mFalse = mScript.term("false");
		mBoogie2Smt = new Boogie2SMT(mManagedScript, boogieDeclarations, false, services, false);
		mVars = mBoogie2Smt.getBoogie2SmtSymbolTable().getGlobalsMap();
		mIdentifierTranslators = new IIdentifierTranslator[] { this::getSmtIdentifier };
		mSeparateInvariantHandling = separateInvariantHandling;
		mPhaseTermCache = new HashMap<>();
		mQuantified = 0;
		mPlain = 0;
		mBeforeSize = 0;
		mAfterSize = 0;
		mTrivialConsistent = 0;
		mGeneratedChecks = 0;
		mNoQelim = 0;
		mQelim = 0;

		if (mSeparateInvariantHandling) {
			mPrimedInvariant = constructPrimedStateInvariant(req2Automata);
			mLogger.info("Finished generating primed state invariant of size " + new DAGSize().size(mPrimedInvariant));
		} else {
			mPrimedInvariant = mTrue;
		}

	}

	private Script buildSolver(final IUltimateServiceProvider services, final IToolchainStorage storage)
			throws AssertionError {
		final SolverSettings settings = SolverBuilder.constructSolverSettings("",
				SolverMode.External_ModelsAndUnsatCoreMode, false, SolverBuilder.COMMAND_Z3_NO_TIMEOUT, false, null);
		final Script solver =
				SolverBuilder.buildAndInitializeSolver(services, storage, SolverMode.External_ModelsAndUnsatCoreMode,
						settings, false, false, Logics.ALL.toString(), "RtInconsistencySolver");
		if (SOLVER_LOGFILE == null) {
			return solver;
		}
		try {
			return new LoggingScript(solver, SOLVER_LOGFILE, false);
		} catch (final FileNotFoundException e) {
			mLogger.error("Could not create log file for solver, disabling logging. ");
			return solver;
		}
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
				final String pcName = ReqSymboltable.getPcName(automaton);
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
		return mBoogie2Smt.getTerm2Expression().translate(finalCheck);
	}

	public void logStats() {
		if (mTrivialConsistent > 0) {
			mLogger.info(String.format("%s checks, %s trivial consistent, %s non-trivial",
					mGeneratedChecks + mTrivialConsistent, mTrivialConsistent, mGeneratedChecks));
		}
		if (!PRINT_STATS) {
			return;
		}
		mLogger.info(String.format(
				"Of %s formulas, %s were quantified, %s were plain. Needed %s quantifier elimination runs, %s solver decisions.",
				mQuantified + mPlain, mQuantified, mPlain, mQelim, mNoQelim));
		if (SIMPLIFY_BEFORE_QELIM) {
			mLogger.info(String.format("Terms of DAG size %s were simplified to DAG size %s (%s percent reduction)",
					mBeforeSize, mAfterSize, 100.0 - ((mAfterSize * 1.0) / (mBeforeSize * 1.0)) * 100.0));
		}
	}

	private Term getPhaseTerm(final Phase phase) {
		Term phaseTerm = mPhaseTermCache.get(phase);
		if (phaseTerm == null) {
			final List<Term> inner = new ArrayList<>();
			for (final Transition trans : phase.getTransitions()) {
				inner.add(SmtUtils.and(mScript, genGuardANDPrimedStInv(trans), genStrictInv(trans)));
			}
			phaseTerm = SmtUtils.or(mScript, inner);
			mPhaseTermCache.put(phase, phaseTerm);
		}
		return phaseTerm;
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

	private Term constructPrimedStateInvariant(final Map<PatternType, PhaseEventAutomata> req2Automata)
			throws InvariantInfeasibleException {

		final Map<PatternType, CDD> primedStateInvariants = new HashMap<>();
		for (final Entry<PatternType, PhaseEventAutomata> entry : req2Automata.entrySet()) {
			if (entry.getValue().getPhases().length != 1) {
				continue;
			}
			primedStateInvariants.put(entry.getKey(), entry.getValue().getPhases()[0].getStateInvariant().prime());
		}

		final Term result;
		final Map<PatternType, Term> terms;
		if (primedStateInvariants.isEmpty()) {
			return mTrue;
		} else if (primedStateInvariants.size() == 1) {
			final Entry<PatternType, CDD> entry = primedStateInvariants.entrySet().iterator().next();
			result = toSmt(entry.getValue());
			terms = Collections.singletonMap(entry.getKey(), result);
		} else {
			terms = primedStateInvariants.entrySet().stream()
					.collect(Collectors.toMap(Entry::getKey, a -> toSmt(a.getValue())));
			result = SmtUtils.and(mScript, terms.values());
		}
		return handleInconsistentStateInvariant(terms, simplify(handleInconsistentStateInvariant(terms, result)));
	}

	private Term handleInconsistentStateInvariant(final Map<PatternType, Term> terms, final Term invariant)
			throws InvariantInfeasibleException {
		if (mFalse != invariant) {
			return invariant;
		}

		final Function<TermVariable, IProgramVar> funTermVar2ProgVar = a -> mVars.get(a.getName());
		final SimplePredicateFactory pfac = new SimplePredicateFactory(mManagedScript, funTermVar2ProgVar);
		mScript.push(1);
		final Map<Term, PatternType> name2Req = new HashMap<>();
		for (final Entry<PatternType, Term> entry : terms.entrySet()) {
			final Term term = entry.getValue();
			final BasicPredicate pred = pfac.newPredicate(term);
			final Term namedTerm = SmtUtils.annotateAndAssert(mScript, pred.getClosedFormula(), entry.getKey().getId());
			name2Req.put(namedTerm, entry.getKey());
		}
		final LBool result = mScript.checkSat();
		assert result == LBool.UNSAT;
		final Collection<PatternType> responsibleRequirements = new HashSet<>();
		final Term[] unsatCore = mScript.getUnsatCore();
		Arrays.stream(unsatCore).map(a -> name2Req.get(a)).forEach(responsibleRequirements::add);
		mScript.pop(1);
		throw new InvariantInfeasibleException(responsibleRequirements);
	}

	private Term toSmt(final CDD cdd) {
		if (cdd == CDD.TRUE) {
			return mTrue;
		}
		if (cdd == CDD.FALSE) {
			return mFalse;
		}
		final CDD simplifiedCdd = cdd.getDecision().simplify(cdd.getChilds());
		if (simplifiedCdd == CDD.TRUE) {
			return mTrue;
		}
		if (simplifiedCdd == CDD.FALSE) {
			return mFalse;
		}
		final CDD[] childs = simplifiedCdd.getChilds();
		final Decision<?> decision = simplifiedCdd.getDecision();

		Term rtr = null;
		for (int i = 0; i < childs.length; i++) {
			if (childs[i] == CDD.FALSE) {
				continue;
			}
			Term childTerm = toSmt(childs[i]);
			if (!simplifiedCdd.childDominates(i)) {
				Term decisionTerm;

				if (decision instanceof RangeDecision) {
					// TODO: I added negation by restructuring, is this wrong?
					decisionTerm = toSmtForRange(i, decision.getVar(), ((RangeDecision) decision).getLimits());
				} else if (decision instanceof BoogieBooleanExpressionDecision) {
					// rewrite expression s.t. identifier expressions have declarations
					final Expression expr = ((BoogieBooleanExpressionDecision) decision).getExpression();
					final AddDeclarationInformationToIdentifiers visitor = new AddDeclarationInformationToIdentifiers();
					final Expression transformedExpr = expr.accept(visitor);
					decisionTerm = toSmt(transformedExpr);
				} else if (decision instanceof BooleanDecision) {
					// TODO: This also covers RelationDecisions, is this intended?
					decisionTerm = getTermVarTerm(((BooleanDecision) decision).getVar());
				} else if (decision instanceof EventDecision) {
					decisionTerm = getTermVarTerm(((EventDecision) decision).getVar());
				} else {
					throw new UnsupportedOperationException("Unknown decision type: " + decision.getClass());
				}

				if (i == 1 && !(decision instanceof RangeDecision)) {
					// negate if right child
					decisionTerm = SmtUtils.not(mScript, decisionTerm);
				}

				if (childTerm == mTrue) {
					childTerm = decisionTerm;
				} else {
					childTerm = SmtUtils.and(mScript, decisionTerm, childTerm);
				}
			}
			if (rtr == null) {
				rtr = childTerm;
			} else {
				rtr = SmtUtils.or(mScript, childTerm, rtr);
			}
		}

		if (rtr == null) {
			return mFalse;
		}
		return rtr;
	}

	private Term toSmt(final Expression expr) {
		final SingleTermResult result = mBoogie2Smt.getExpression2Term().translateToTerm(mIdentifierTranslators, expr);
		return result.getTerm();
	}

	private Term getSmtIdentifier(final String id, final DeclarationInformation declInfo, final boolean isOldContext,
			final BoogieASTNode boogieASTNode) {
		if (isOldContext || declInfo != DeclarationInformation.DECLARATIONINFO_GLOBAL) {
			throw new UnsupportedOperationException();
		}
		return getTermVarTerm(id);
	}

	private Term toSmtForRange(final int childIdx, final String varname, final int[] limits) {
		final Term var = getTermVarTerm(varname);

		if (childIdx == 0) {
			// only upper bound
			final Term rhs = mScript.decimal(Double.toString(limits[0] / 2));
			if ((limits[0] & 1) == 0) {
				// strict because of first bit encoding
				return SmtUtils.less(mScript, var, rhs);
			}
			// not strict
			return SmtUtils.leq(mScript, var, rhs);
		}

		// TODO: Why can the limit be one larger than the array?
		if (childIdx == limits.length) {
			// only lower bound
			final Term rhs = mScript.decimal(Double.toString(limits[limits.length - 1] / 2));
			if ((limits[limits.length - 1] & 1) == 1) {
				return SmtUtils.greater(mScript, var, rhs);
			}
			return SmtUtils.geq(mScript, var, rhs);
		}

		if ((limits[childIdx - 1] / 2) == (limits[childIdx] / 2)) {
			// we have upper and lower, but they are identical, so its EQ
			// and they differ in the first bit because first bit encoding and sortedness
			final Term rhs = mScript.decimal(Double.toString(limits[childIdx] / 2));
			return SmtUtils.binaryEquality(mScript, var, rhs);
		}

		// we have upper and lower bounds
		final Term lb = mScript.decimal(Double.toString(limits[childIdx - 1] / 2));
		final Term ub = mScript.decimal(Double.toString(limits[childIdx] / 2));

		final Term lbTerm;
		final Term ubTerm;
		if ((limits[childIdx - 1] & 1) == 1) {
			// strict lb
			lbTerm = SmtUtils.less(mScript, lb, var);
		} else {
			lbTerm = SmtUtils.leq(mScript, lb, var);
		}

		if ((limits[childIdx] & 1) == 0) {
			// strict ub
			ubTerm = SmtUtils.less(mScript, var, ub);
		} else {
			ubTerm = SmtUtils.leq(mScript, var, ub);
		}
		return SmtUtils.and(mScript, lbTerm, ubTerm);
	}

	private Term getTermVarTerm(final String name) {
		final IProgramNonOldVar termVar = mVars.get(name);
		return termVar.getTerm();
	}

	private Term existentiallyProjectEventsAndPrimedVars(final Term term) {
		final Term simplifiedTerm = simplifyAndLog(term);

		final Set<TermVariable> varsToRemove = getPrimedAndEventVars(simplifiedTerm.getFreeVars());
		if (varsToRemove.isEmpty()) {
			return term;
		}
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Removing " + varsToRemove.size() + " variables");
		}
		if (TRY_SOLVER_BEFORE_QELIM) {
			final Term quantifiedFormula = SmtUtils.quantifier(mScript, QuantifiedFormula.EXISTS, varsToRemove, term);
			final Term isTrueTerm = mScript.term("distinct", mTrue, quantifiedFormula);
			final LBool result = SmtUtils.checkSatTerm(mScript, isTrueTerm);
			if (result == LBool.UNSAT) {
				mNoQelim++;
				return mTrue;
			}
		}
		mQelim++;
		final Term quantifierFreeFormula =
				PartialQuantifierElimination.quantifierCustom(mServices, mLogger, mManagedScript,
						PqeTechniques.ALL_LOCAL, QuantifiedFormula.EXISTS, varsToRemove, simplifiedTerm, new Term[0]);

		// final Term quantifierFreeFormula =
		// PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mManagedScript, quantifiedFormula,
		// SimplificationTechnique.NONE, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
		return quantifierFreeFormula;
	}

	private Set<TermVariable> getPrimedAndEventVars(final TermVariable[] freeVars) {
		final Set<TermVariable> rtr = new HashSet<>();
		final Set<String> primedVars = mBoogieSymboltable.getPrimedVars();
		final Set<String> eventVars = mBoogieSymboltable.getEventVars();
		for (final TermVariable var : freeVars) {
			final Expression expr = mBoogie2Smt.getTerm2Expression().translate(var);
			if (expr instanceof IdentifierExpression) {
				final String name = ((IdentifierExpression) expr).getIdentifier();
				if (primedVars.contains(name) || eventVars.contains(name)) {
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

	private Term genStrictInv(final Transition transition) {
		final Phase phase = transition.getDest();
		final String[] resetVars = transition.getResets();
		final List<String> resetList = Arrays.asList(resetVars);
		return toSmt(new StrictInvariant().genStrictInv(phase.getClockInvariant(), resetList));
	}

	private Term genGuardANDPrimedStInv(final Transition transition) {
		final Term guard = toSmt(transition.getGuard());
		final Phase phase = transition.getDest();
		final Term primedStInv = toSmt(phase.getStateInvariant().prime());
		return SmtUtils.and(mScript, guard, primedStInv);
	}

	private Term genPCCompEQ(final String pcName, final int phaseIndex) {
		return SmtUtils.binaryEquality(mScript, getTermVarTerm(pcName), mScript.numeral(Integer.toString(phaseIndex)));
	}

	private final class AddDeclarationInformationToIdentifiers extends GeneratedBoogieAstTransformer {

		@Override
		public Expression transform(final IdentifierExpression node) {
			return mBoogieSymboltable.getIdentifierExpression(node.getIdentifier());
		}

	}

	public static final class InvariantInfeasibleException extends Exception {

		private static final long serialVersionUID = 1L;
		private final Collection<PatternType> mResponsibleRequirements;

		private InvariantInfeasibleException(final Collection<PatternType> responsibleRequirements) {
			super("Some invariants are already infeasible. Responsible requirements: "
					+ responsibleRequirements.stream().map(a -> a.getId()).collect(Collectors.joining(", ")));
			mResponsibleRequirements = responsibleRequirements;
		}

		public Collection<PatternType> getResponsibleRequirements() {
			return mResponsibleRequirements;
		}

	}

}
