/*
 * Copyright (C) 2023 Marcel Ebbinghaus
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023-2024 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.conditional;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Objects;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation.Dependence;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.ISymbolicIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.QualifiedTracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.TracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.AutomatonFreeRefinementEngine;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult.BasicRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierUtils;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.SleepSetStateFactoryForRefinement.SleepPredicate;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.abstraction.ICopyActionFactory;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.conditional.ConditionalCommutativityStatisticsGenerator.ConditionalCommutativityStopwatches;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.util.Lazy;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * Conditional commutativity checker, which checks for conditional commutativity of two given letters (letter1,letter2),
 * i.e. whether there is a condition Phi such that those letters commute under Phi and Phi holds after the given
 * currentRun. Also provides a proof, if this is the case.
 *
 * @author Marcel Ebbinghaus
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of letters.
 */
public class ConditionalCommutativityChecker<L extends IAction> {
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final ManagedScript mManagedScript;

	private final IIndependenceRelation<IPredicate, L> mIndependenceRelation;
	private final ISymbolicIndependenceRelation<L, IPredicate> mSymbolicRelation;
	private final boolean mPassContextToSymbolicRelation;

	private final PredicateFactory mPredicateFactory;
	private final ICopyActionFactory<L> mCopyFactory;
	private final Function<IRun<L, IPredicate>, IRefinementStrategy<L>> mBuildStrategy;

	private final ConditionalCommutativityStatisticsGenerator mStatistics;

	/**
	 * Constructs a new instance of ConditionalCommutativityChecker.
	 *
	 * @param services
	 *            Ultimate services.
	 * @param mgdScript
	 *            Script to which the computed conditions belong.
	 * @param independenceRelation
	 *            Independence relation used for commutativity checks. The corresponding symbolic relation (see
	 *            {@link IIndependenceRelation#getSymbolicRelation()}) is used to compute commutativity conditions.
	 * @param buildStrategy
	 *            Factory for strategies used to check whether a computed commutativity condition holds after some
	 *            trace.
	 * @param predicateFactory
	 *            The predicate factory used by {@code independenceRelation} to build conditions.
	 * @param copyFactory
	 *            A factory that can be used to create new edges of type {@code L}.
	 * @param statistics
	 *            An {@link ConditionalCommutativityStatisticsGenerator} used to collect statistics
	 */
	public ConditionalCommutativityChecker(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final IIndependenceRelation<IPredicate, L> independenceRelation,
			final Function<IRun<L, IPredicate>, IRefinementStrategy<L>> buildStrategy,
			final PredicateFactory predicateFactory, final ICopyActionFactory<L> copyFactory,
			final ConditionalCommutativityStatisticsGenerator statistics) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(getClass());
		mManagedScript = mgdScript;

		mIndependenceRelation = independenceRelation;
		mSymbolicRelation = mIndependenceRelation.getSymbolicRelation();
		if (mSymbolicRelation == null) {
			throw new UnsupportedOperationException(
					"Given independence relation does not offer a symbolic counterpart");
		}
		mPassContextToSymbolicRelation = mSymbolicRelation.isConditional();

		mBuildStrategy = buildStrategy;
		mPredicateFactory = predicateFactory;
		mCopyFactory = copyFactory;

		mStatistics = statistics;
	}

	/**
	 * Checks for conditional commutativity of two given letters ({@code letter1} and {@code letter2}), i.e. whether there is a condition
	 * Phi such that those letters commute under Phi, and Phi holds after the given {@code currentRun}.
	 * If this is the case, returns a proof that this Phi holds after executing {@code currentRun}.
	 *
	 * @param currentRun
	 *            A run after which the given letters should be independent
	 * @param letter1
	 *            A letter of an outgoing transition of state
	 * @param letter2
	 *            A letter of another outgoing transition of state
	 * @return A refinement result proving a sufficient condition for commutativity, or {@code null} if no such condition or proof was found.
	 */
	public Result<L> checkConditionalCommutativity(
			final NestedRun<L, IPredicate> currentRun, final L letter1, final L letter2) {

		mStatistics.startStopwatch(ConditionalCommutativityStopwatches.CHECKER);
		try {
			return checkConditionalCommutativityInternal(currentRun, letter1, letter2);
		} finally {
			mStatistics.stopStopwatch(ConditionalCommutativityStopwatches.CHECKER);
		}
	}

	private Result<L> checkConditionalCommutativityInternal(final NestedRun<L, IPredicate> currentRun, final L letter1, final L letter2) {
		final IPredicate state = currentRun.getStateAtPosition(currentRun.getLength() - 1);

		// TODO this is brittle, let caller decide how one extracts a sleep set from the states
		// TODO is this actually still needed?
		if (state instanceof SleepPredicate) {
			final ImmutableSet<?> sleepSet = ((SleepPredicate<L>) state).getSleepSet();
			if (sleepSet.contains(letter1) && sleepSet.contains(letter2)) {
				return null;
			}
		}

		final Dependence dependence = mIndependenceRelation.isIndependent(state, letter1, letter2);
		if (dependence == Dependence.INDEPENDENT) {
			return new Result<>(ResultType.ALREADY_INDEPENDENT);
		}

		final IPredicate condition = generateCondition(state, letter1, letter2);
		if (condition == null) {
			return new Result<>(ResultType.NO_CONDITION_FOUND);
		}

		return proveCommutativityCondition(currentRun, letter1, condition);
	}

	private IPredicate generateCondition(final IPredicate state, final L letter1, final L letter2) {
		final IPredicate condition = generateRawCondition(letter1, letter2, state);
		if (condition == null) {
			return null;
		}

		// TODO consider moving these checks to the appropriate symbolic independence relation.
		if (SmtUtils.isTrueLiteral(condition.getFormula())) {
			throw new AssertionError("Letters did not commute, but generated condition was 'true'");
		}
		if (SmtUtils.checkSatTerm(mManagedScript.getScript(), condition.getFormula()).equals(LBool.UNSAT)) {
			mStatistics.addFalseCondition();
			mLogger.warn("Unsatisfiable commutativity condition generated: %s", condition);
			return null;
		}

		return condition;
	}

	private IPredicate generateRawCondition(final L letter1, final L letter2, final IPredicate context) {
		mStatistics.startStopwatch(ConditionalCommutativityStopwatches.CONDITION);
		try {
			mStatistics.addConditionCalculation();
			if (mPassContextToSymbolicRelation && context != null) {
				return mSymbolicRelation.getCommutativityCondition(context, letter1, letter2);
			}
			return mSymbolicRelation.getCommutativityCondition(null, letter1, letter2);
		} finally {
			mStatistics.stopStopwatch(ConditionalCommutativityStopwatches.CONDITION);
		}
	}

	private Result<L> proveCommutativityCondition(final NestedRun<L, IPredicate> currentRun, final L templateLetter, final IPredicate condition) {
		// construct a transformula which represents the negation of the condition
		final IPredicate notCondition = mPredicateFactory.not(condition);
		final UnmodifiableTransFormula tf =
				TransFormulaBuilder.constructTransFormulaFromPredicate(notCondition, mManagedScript);

		if (!QuantifierUtils.isQuantifierFree(tf.getFormula())) {
			mStatistics.addQuantifiedCondition();
			mLogger.warn("Quantified commutativity condition: %s", tf.getFormula());
		}

		// create a transition with the new transformula
		// TODO as workaround, we create a copy of an existing letter
		final L notConditionLetter = mCopyFactory.copy(templateLetter, tf, null);

		// create a dummy state for the end of the run
		final IPredicate dummyPredicate = mPredicateFactory.newDebugPredicate("dummy");

		// add both to the currentRun
		final NestedRun<L, IPredicate> conditionRun =
				new NestedRun<>(currentRun.getStateAtPosition(currentRun.getLength() - 1), notConditionLetter,
						NestedWord.INTERNAL_POSITION, dummyPredicate);
		final NestedRun<L, IPredicate> currentRunWithCondition = currentRun.concatenate(conditionRun);

		final var strategy = mBuildStrategy.apply(currentRunWithCondition);
		final var afe = new AutomatonFreeRefinementEngine<>(mServices, mLogger, strategy);
		final var result = afe.getResult();

		mStatistics.addTraceCheck();
		if (result.getCounterexampleFeasibility() == LBool.UNKNOWN) {
			mStatistics.addUnknownTraceCheck();
			return new Result<>(ResultType.UNKNOWN_CHECK);
		}

		if (result.getCounterexampleFeasibility() == LBool.SAT) {
			return new Result<>(ResultType.CONDTION_NOT_SATISFIED);
		}
		if (!result.somePerfectSequenceFound()) {
			mStatistics.addImperfectProof();
			return new Result<>(ResultType.PROOF_IMPERFECT);
		}
		return new Result<>(postProcessRefinementResult(result));
	}

	// Post-processes the refinement result's trace predicates such that the usage of an additional non-commutativity
	// assumption remains hidden to the caller.
	private IRefinementEngineResult<L, Collection<QualifiedTracePredicates>> postProcessRefinementResult(
			final IRefinementEngineResult<L, Collection<QualifiedTracePredicates>> original) {
		final var tpMap = new HashMap<QualifiedTracePredicates, QualifiedTracePredicates>();

		final var tracePredicates = new ArrayList<QualifiedTracePredicates>();
		for (final var qtp : original.getInfeasibilityProof()) {
			final var newQtp = tpMap.computeIfAbsent(qtp, ConditionalCommutativityChecker::postProcessPredicates);
			tracePredicates.add(newQtp);
		}

		final var usedTracePredicates = new ArrayList<QualifiedTracePredicates>();
		for (final var qtp : original.getUsedTracePredicates()) {
			final var newQtp = tpMap.computeIfAbsent(qtp, ConditionalCommutativityChecker::postProcessPredicates);
			usedTracePredicates.add(newQtp);
		}

		return new BasicRefinementEngineResult<>(original.getCounterexampleFeasibility(), tracePredicates, null,
				original.somePerfectSequenceFound(), usedTracePredicates, new Lazy<>(original::getHoareTripleChecker),
				new Lazy<>(original::getPredicateUnifier));
	}

	private static QualifiedTracePredicates postProcessPredicates(final QualifiedTracePredicates qtp) {
		final int numOfPreds = qtp.getPredicates().size();
		final IPredicate newPost = qtp.getPredicates().get(numOfPreds - 1);
		final List<IPredicate> newPredicates = new ArrayList<>(qtp.getPredicates().subList(0, numOfPreds - 1));
		final TracePredicates tp =
				new TracePredicates(qtp.getTracePredicates().getPrecondition(), newPost, newPredicates);
		return new QualifiedTracePredicates(tp, qtp.getOrigin(), qtp.isPerfect());
	}

	public static final class Result<L extends IAction> {
		private final ResultType mType;
		private final IRefinementEngineResult<L, Collection<QualifiedTracePredicates>> mRefinementResult;

		private Result(ResultType type) {
			mType = type;
			mRefinementResult = null;
			assert !isSuccess() : "successful result must have refinement result";
		}

		private Result(IRefinementEngineResult<L, Collection<QualifiedTracePredicates>> refinementResult) {
			mType = ResultType.SUCCESS;
			mRefinementResult = Objects.requireNonNull(refinementResult);
		}

		public boolean isSuccess() {
			return mType == ResultType.SUCCESS;
		}

		public ResultType getType() {
			return mType;
		}

		public IRefinementEngineResult<L, Collection<QualifiedTracePredicates>> getRefinementResult() {
			assert mRefinementResult != null : "No proof of commutativity found";
			return mRefinementResult;
		}
	}

	public enum ResultType {
		ALREADY_INDEPENDENT,
		NO_CONDITION_FOUND,
		CONDTION_NOT_SATISFIED,
		UNKNOWN_CHECK,
		PROOF_IMPERFECT,
		SUCCESS
	}
}
