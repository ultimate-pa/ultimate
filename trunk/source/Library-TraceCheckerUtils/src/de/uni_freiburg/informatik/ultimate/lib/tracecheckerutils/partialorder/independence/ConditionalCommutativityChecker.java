/*
 * Copyright (C) 2023 Marcel Ebbinghaus
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
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence;

import java.util.Collection;
import java.util.List;
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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateWithConjuncts;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.AutomatonFreeRefinementEngine;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierUtils;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.SleepSetStateFactoryForRefinement.SleepPredicate;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.IConditionalCommutativityCheckerStatisticsUtils.ConditionalCommutativityStopwatches;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.abstraction.ICopyActionFactory;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableList;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * Conditional commutativity checker.
 *
 * @author Marcel Ebbinghaus
 *
 * @param <L>
 *            The type of letters.
 */
public class ConditionalCommutativityChecker<L extends IAction> {
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;

	private final IConditionalCommutativityCriterion<L> mCriterion;
	private final IIndependenceRelation<IPredicate, L> mIndependenceRelation;
	private final IIndependenceConditionGenerator mGenerator;
	private final ManagedScript mManagedScript;
	private final IConditionalCommutativityCheckerStatisticsUtils mStatisticsUtils;
	private final ConComTraceCheckMode mTraceCheckMode;
	private final PredicateFactory mPredicateFactory;
	private final ICopyActionFactory<L> mCopyFactory;
	private final Function<IRun<L, IPredicate>, IRefinementStrategy<L>> mBuildStrategy;

	/**
	 * Constructs a new instance of ConditionalCommutativityChecker.
	 *
	 * @author Marcel Ebbinghaus
	 *
	 * @param criterion
	 *            An {@link IConditionalCommutativityCriterion} to decide when to check for conditional commutativity
	 * @param independenceRelation
	 *            Independence relation for commutativity
	 * @param script
	 *            Script for conjunction handling
	 * @param generator
	 *            Generator for constructing commutativity conditions
	 * @param traceChecker
	 *            An {@link ITraceChecker} responsible for proving that a condition holds after the run given in
	 *            checkConditionalCommutativity
	 * @param statisticsUtils
	 *            An {@link IConditionalCommutativityCheckerStatisticsUtils} used for statistics
	 */
	public ConditionalCommutativityChecker(final IUltimateServiceProvider services,
			final IConditionalCommutativityCriterion<L> criterion,
			final IIndependenceRelation<IPredicate, L> independenceRelation, final ManagedScript script,
			final IIndependenceConditionGenerator generator,
			final Function<IRun<L, IPredicate>, IRefinementStrategy<L>> buildStrategy,
			final IConditionalCommutativityCheckerStatisticsUtils statisticsUtils,
			final PredicateFactory predicateFactory, final ICopyActionFactory<L> copyFactory,
			final ConComTraceCheckMode traceCheckMode) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(getClass());

		mCriterion = criterion;
		mIndependenceRelation = independenceRelation;
		mManagedScript = script;
		mGenerator = generator;
		mStatisticsUtils = statisticsUtils;
		mPredicateFactory = predicateFactory;
		mCopyFactory = copyFactory;
		mTraceCheckMode = traceCheckMode;
		mBuildStrategy = buildStrategy;
	}

	/**
	 * Checks for conditional commutativity.
	 *
	 * @author Marcel Ebbinghaus
	 *
	 * @param currentRun
	 *            The run to state
	 * @param predicates
	 *            Predicates used as context for condition generation
	 * @param state
	 *            The state
	 * @param letter1
	 *            A letter of an outgoing transition of state
	 * @param letter2
	 *            A letter of another outgoing transition of state
	 * @return A list of predicates which serves as a proof for conditional commutativity.
	 */
	// TODO method description is very vague (not more helpful than the method name)
	public IRefinementEngineResult<L, Collection<QualifiedTracePredicates>> checkConditionalCommutativity(
			final NestedRun<L, IPredicate> currentRun, final List<IPredicate> predicates, final IPredicate state,
			final L letter1, final L letter2) {

		mStatisticsUtils.startStopwatch(ConditionalCommutativityStopwatches.CHECKER);
		try {
			return checkConditionalCommutativityInternal(currentRun, predicates, state, letter1, letter2);
		} finally {
			mStatisticsUtils.stopStopwatch(ConditionalCommutativityStopwatches.CHECKER);
			// mStatisticsUtils.stopStopwatch(ConditionalCommutativityStopwatches.CONDITION);
		}
	}

	private IRefinementEngineResult<L, Collection<QualifiedTracePredicates>> checkConditionalCommutativityInternal(
			final NestedRun<L, IPredicate> currentRun, final List<IPredicate> predicates, final IPredicate state,
			final L letter1, final L letter2) {

		// TODO (Why) is this still needed? Unlocking the script used by interpolant automata can be very expensive.
		if (mManagedScript.isLocked()) {
			mManagedScript.requestLockRelease();
		}

		// TODO remove this once we have completely switched to symbolic independence relations
		if (((IAction) letter1).getPrecedingProcedure().equals(((IAction) letter2).getPrecedingProcedure())) {
			return null;
		}

		// TODO this is brittle, let caller decide how one extracts a sleep set from the states
		if (state instanceof SleepPredicate) {
			final ImmutableSet<?> sleepSet = ((SleepPredicate<L>) state).getSleepSet();
			if (sleepSet.contains(letter1) && sleepSet.contains(letter2)) {
				return null;
			}
		}

		final IPredicate pred;
		if (predicates.isEmpty()) {
			pred = null;
		} else {
			// TODO why not make "predicates" an ImmutableList directly?
			final var conjPred = mPredicateFactory.construct(
					id -> new PredicateWithConjuncts(id, new ImmutableList<>(predicates), mManagedScript.getScript()));
			pred = mPredicateFactory.construct(id -> new BasicPredicate(id, conjPred.getFormula(), conjPred.getVars(),
					conjPred.getFuns(), conjPred.getClosedFormula()));
		}

		// TODO This does not accurately reflect how independence is checked in most configurations.
		// TODO There, each conjunct is considered separately.
		// TODO By passing the given context as predicate directly, this mismatch can be avoided.
		if (mIndependenceRelation.isIndependent(pred, letter1, letter2).equals(Dependence.INDEPENDENT)) {
			return null;
		}

		if (mCriterion.decide(state, letter1, letter2)) {
			// TODO This is already done at the top of the method. Why here again?
			if (mManagedScript.isLocked()) {
				mManagedScript.requestLockRelease();
			}
			IPredicate condition = null;

			final ISymbolicIndependenceRelation<L, IPredicate> relation = mIndependenceRelation.getSymbolicRelation();

			mStatisticsUtils.startStopwatch(ConditionalCommutativityStopwatches.CONDITION);
			try {
				switch (mTraceCheckMode) {
				case GENERATOR:
					condition = mGenerator.generateCondition(letter1.getTransformula(), letter2.getTransformula());
					break;
				case GENERATOR_WITH_CONTEXT:
					if (pred != null) {
						condition = mGenerator.generateCondition(
								// TODO Why is pred not used here? Again, conditions with fixed ID are dangerous!
								new PredicateWithConjuncts(0, new ImmutableList<>(predicates),
										mManagedScript.getScript()),
								letter1.getTransformula(), letter2.getTransformula());
					} else {
						condition = mGenerator.generateCondition(letter1.getTransformula(), letter2.getTransformula());
					}
					break;
				case SYMBOLIC_RELATION:
					// TODO What if the relation is conditional? (we do not need to distinguish these cases here)
					// TODO Why the null-check on relation? Either it cannot be null here, or we should fail if it is.
					if (relation != null && !relation.isConditional()) {
						condition = relation.getCommutativityCondition(null, letter1, letter2);
					}
					break;
				default:
					throw new UnsupportedOperationException(
							"PartialOrderCegarLoop currently does not support " + mTraceCheckMode);
				}
			} finally {
				mStatisticsUtils.stopStopwatch(ConditionalCommutativityStopwatches.CONDITION);
			}

			mStatisticsUtils.addConditionCalculation();
			mCriterion.updateCriterion(state, letter1, letter2);

			if (condition == null) {
				return null;
			} else if (SmtUtils.isTrueLiteral(condition.getFormula())) {
				throw new IllegalArgumentException("condition is not allowed to be true");
			} else if (mCriterion.decide(condition)) {
				if (SmtUtils.checkSatTerm(mManagedScript.getScript(), condition.getFormula()).equals(LBool.UNSAT)) {
					mStatisticsUtils.addFalseCondition();
					mLogger.warn("Unsatisfiable commutativity condition generated: %s", condition);
					return null;
				}
				// TODO split this large method into smaller ones. E.g. everything up to there to calculate the
				// condition, the rest to prove it.

				// construct a transformula which represents the negation of the condition
				final IPredicate notCondition = mPredicateFactory.not(condition);
				final UnmodifiableTransFormula tf =
						TransFormulaBuilder.constructTransFormulaFromPredicate(notCondition, mManagedScript);
				if (!QuantifierUtils.isQuantifierFree(tf.getFormula())) {
					mStatisticsUtils.addQuantifiedCondition();
					mLogger.warn("Quantified commutativity condition: %s", tf.getFormula());
				}

				// copy a transition with the new transformula with IcfgCopyFactory from
				// CegarLoopFactory.mCopyFactory (needs to be passed to the CEGAR-Loop)
				final L notConditionLetter = mCopyFactory.copy(letter1, tf, tf);
				// create a MLPredicate and a SleepSetPredicate as dummy state
				final SleepPredicate<L> dummySleepPredicate =
						new SleepPredicate<>(mPredicateFactory.newMLDontCarePredicate(null), null);
				// add both to the currentRun
				final NestedRun<L, IPredicate> conditionRun =
						new NestedRun<>(currentRun.getStateAtPosition(currentRun.getLength() - 1), notConditionLetter,
								NestedWord.INTERNAL_POSITION, dummySleepPredicate);
				final NestedRun<L, IPredicate> currentRunWithCondition = currentRun.concatenate(conditionRun);

				final var strategy = mBuildStrategy.apply(currentRunWithCondition);
				final var afe = new AutomatonFreeRefinementEngine<>(mServices, mLogger, strategy);
				final var result = afe.getResult();

				mStatisticsUtils.addTraceCheck();
				if (result.getCounterexampleFeasibility() == LBool.UNKNOWN) {
					mStatisticsUtils.addUnknownTraceCheck();
				}
				if (!result.somePerfectSequenceFound()) {
					mStatisticsUtils.addImperfectProof();
				}
				if (result.getCounterexampleFeasibility() != LBool.UNSAT) {
					return null;
				}
				return result;
			}
		}
		return null;
	}

	public IConditionalCommutativityCriterion<L> getCriterion() {
		return mCriterion;
	}

	public enum ConComTraceCheckMode {
		GENERATOR, GENERATOR_WITH_CONTEXT, SYMBOLIC_RELATION
	}
}
