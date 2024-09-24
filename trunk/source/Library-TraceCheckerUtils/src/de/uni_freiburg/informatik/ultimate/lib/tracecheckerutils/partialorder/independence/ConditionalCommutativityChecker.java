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
import java.util.function.BiFunction;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation.Dependence;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.QualifiedTracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateWithConjuncts;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.AutomatonFreeRefinementEngine;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.SleepSetStateFactoryForRefinement.SleepPredicate;
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
	private final BiFunction<IRun<L, IPredicate>, IPredicate, IRefinementStrategy<L>> mBuildStrategy;

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
	 * @param statisticsUtils
	 *            An {@link IConditionalCommutativityCheckerStatisticsUtils} used for statistics
	 */
	// TODO What does it mean that a condition is "feasible"?
	public ConditionalCommutativityChecker(final IUltimateServiceProvider services,
			final IConditionalCommutativityCriterion<L> criterion,
			final IIndependenceRelation<IPredicate, L> independenceRelation, final ManagedScript script,
			final IIndependenceConditionGenerator generator,
			final BiFunction<IRun<L, IPredicate>, IPredicate, IRefinementStrategy<L>> buildStrategy,
			final IConditionalCommutativityCheckerStatisticsUtils statisticsUtils) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(getClass());

		mCriterion = criterion;
		mIndependenceRelation = independenceRelation;
		mManagedScript = script;
		mGenerator = generator;
		mStatisticsUtils = statisticsUtils;
		mBuildStrategy = buildStrategy;
	}

	/**
	 * Checks for conditional commutativity.
	 *
	 * @author Marcel Ebbinghaus
	 *
	 * @param run
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
			final IRun<L, IPredicate> currentRun, final List<IPredicate> predicates, final IPredicate state,
			final L letter1, final L letter2) {
		try {
			mStatisticsUtils.startStopwatch();
			return checkConditionalCommutativityInternal(currentRun, predicates, state, letter1, letter2);
		} finally {
			mStatisticsUtils.stopStopwatch();
		}
	}

	private IRefinementEngineResult<L, Collection<QualifiedTracePredicates>> checkConditionalCommutativityInternal(
			final IRun<L, IPredicate> currentRun, final List<IPredicate> predicates, final IPredicate state,
			final L letter1, final L letter2) {
		if (mManagedScript.isLocked()) {
			mManagedScript.requestLockRelease();
		}

		// TODO use ThreadSeparatingIndependenceRelation (possibly make this a parameter)
		if (letter1.getSucceedingProcedure().equals(letter2.getSucceedingProcedure())) {
			return null;
		}

		// TODO this is brittle, let caller decide how one extracts a sleep set from the states
		if (state instanceof SleepPredicate) {
			final ImmutableSet<?> sleepSet = ((SleepPredicate<L>) state).getSleepSet();
			if (sleepSet.contains(letter1) && sleepSet.contains(letter2)) {
				return null;
			}
		}

		IPredicate pred = null;
		if (!predicates.isEmpty()) {
			// TODO why not pass an ImmutableList directly?
			// TODO avoid re-assigning local variables
			// TODO avoid creating BasicPredicate instances with a fixed ID, this can lead to unsoundness
			// (use a predicate factory instead, or let the caller pass a predicate rather than a list)
			pred = new PredicateWithConjuncts(0, new ImmutableList<>(predicates), mManagedScript.getScript());
			pred = new BasicPredicate(0, pred.getFormula(), pred.getVars(), pred.getFuns(), pred.getClosedFormula());
		}

		// TODO This does not accurately reflect how independence is checked in most configurations.
		// TODO There, each conjunct is considered separately.
		// TODO By passing the given context as predicate directly, this mismatch can be avoided.
		if (mIndependenceRelation.isIndependent(pred, letter1, letter2).equals(Dependence.INDEPENDENT)) {
			return null;
		}

		if (mCriterion.decide(state, letter1, letter2)) {
			// TODO When is this needed? Unlocking the script used by interpolant automata can be very expensive.
			if (mManagedScript.isLocked()) {
				mManagedScript.requestLockRelease();
			}
			IPredicate condition;
			if (pred != null) {
				// TODO Why is pred not reused here?
				condition = mGenerator.generateCondition(
						new PredicateWithConjuncts(0, new ImmutableList<>(predicates), mManagedScript.getScript()),
						letter1.getTransformula(), letter2.getTransformula());
			} else {
				condition = mGenerator.generateCondition(letter1.getTransformula(), letter2.getTransformula());
			}
			mStatisticsUtils.addConditionCalculation();
			mCriterion.updateCriterion(state, letter1, letter2);

			if (condition != null && !SmtUtils.isTrueLiteral(condition.getFormula()) && mCriterion.decide(condition)) {
				final var strategy = mBuildStrategy.apply(currentRun, condition);
				final var afe = new AutomatonFreeRefinementEngine<>(mServices, mLogger, strategy);
				return afe.getResult();
			}
		}
		return null;
	}

	public IConditionalCommutativityCriterion<L> getCriterion() {
		return mCriterion;
	}
}
