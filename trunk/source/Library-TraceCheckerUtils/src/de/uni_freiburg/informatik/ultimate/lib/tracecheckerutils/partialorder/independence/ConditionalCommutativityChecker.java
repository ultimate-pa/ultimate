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

import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation.Dependence;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.ISymbolicIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.TracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.MLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateWithConjuncts;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.ITraceChecker;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.SleepSetStateFactoryForRefinement.SleepPredicate;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.IConditionalCommutativityCheckerStatisticsUtils.ConditionalCommutativityStopwatches;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.abstraction.ICopyActionFactory;
import de.uni_freiburg.informatik.ultimate.logic.Term;
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

	private final IConditionalCommutativityCriterion<L> mCriterion;
	private final IIndependenceRelation<IPredicate, L> mIndependenceRelation;
	private final IIndependenceConditionGenerator mGenerator;
	private final ITraceChecker<L> mTraceChecker;
	private final ManagedScript mManagedScript;
	private final IConditionalCommutativityCheckerStatisticsUtils mStatisticsUtils;
	private ConComTraceCheckMode mTraceCheckMode;
	private PredicateFactory mPredicateFactory;
	private ICopyActionFactory<L> mCopyFactory;

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
	public ConditionalCommutativityChecker(final IConditionalCommutativityCriterion<L> criterion,
			final IIndependenceRelation<IPredicate, L> independenceRelation, final ManagedScript script,
			final IIndependenceConditionGenerator generator, final ITraceChecker<L> traceChecker,
			final IConditionalCommutativityCheckerStatisticsUtils statisticsUtils, PredicateFactory predicateFactory,
			ICopyActionFactory<L> copyFactory, ConComTraceCheckMode traceCheckMode) {
		mCriterion = criterion;
		mIndependenceRelation = independenceRelation;
		mManagedScript = script;
		mGenerator = generator;
		mTraceChecker = traceChecker;
		mStatisticsUtils = statisticsUtils;
		mPredicateFactory = predicateFactory;
		mCopyFactory = copyFactory;
		mTraceCheckMode = traceCheckMode;
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
	public TracePredicates checkConditionalCommutativity(final NestedRun<L, IPredicate> currentRun,
			final List<IPredicate> predicates, final IPredicate state, final L letter1, final L letter2) {

		try {
			mStatisticsUtils.startStopwatch(ConditionalCommutativityStopwatches.CHECKER);
			if (mManagedScript.isLocked()) {
				mManagedScript.requestLockRelease();
			}

			if (((IAction) letter1).getSucceedingProcedure().equals(((IAction) letter2).getSucceedingProcedure())) {
				return null;
			}

			if (state instanceof SleepPredicate) {
				final ImmutableSet<?> sleepSet = ((SleepPredicate<L>) state).getSleepSet();
				if (sleepSet.contains(letter1) && sleepSet.contains(letter2)) {
					return null;
				}
			}

			IPredicate pred = null;
			if (!predicates.isEmpty()) {
				pred = new PredicateWithConjuncts(0, new ImmutableList<>(predicates), mManagedScript.getScript());
				pred = new BasicPredicate(0, pred.getFormula(), pred.getVars(), pred.getFuns(),
						pred.getClosedFormula());
			}

			if (mIndependenceRelation.isIndependent(pred, letter1, letter2).equals(Dependence.INDEPENDENT)) {
				return null;
			}

			if (mCriterion.decide(state, letter1, letter2)) {

				if (mManagedScript.isLocked()) {
					mManagedScript.requestLockRelease();
				}
				IPredicate condition = null;

				ISymbolicIndependenceRelation<L, IPredicate> relation = mIndependenceRelation.getSymbolicRelation();

				switch (mTraceCheckMode) {
				case GENERATOR:
					condition = mGenerator.generateCondition(letter1.getTransformula(), letter2.getTransformula());
					break;
				case GENERATOR_WITH_CONTEXT:
					if (pred != null) {
						condition = mGenerator.generateCondition(
								new PredicateWithConjuncts(0, new ImmutableList<>(predicates),
										mManagedScript.getScript()),
								letter1.getTransformula(), letter2.getTransformula());
					} else {
						condition = mGenerator.generateCondition(letter1.getTransformula(), letter2.getTransformula());
					}
					break;
				case SYMBOLIC_RELATION:
					if (relation != null) {
						condition = relation.getCommutativityCondition(letter1, letter2);
					}
					break;
				default:
					throw new UnsupportedOperationException(
							"PartialOrderCegarLoop currently does not support " + mTraceCheckMode);
				}

				/*
				 * if (relation != null) { condition = relation.getCommutativityCondition(letter1, letter2); } // TODO:
				 * integrate setting s.t. we can try both versions: with and without context if (pred != null) {
				 * condition = mGenerator.generateCondition( new PredicateWithConjuncts(0, new
				 * ImmutableList<>(predicates), mManagedScript.getScript()), letter1.getTransformula(),
				 * letter2.getTransformula()); } else { condition =
				 * mGenerator.generateCondition(letter1.getTransformula(), letter2.getTransformula()); }
				 */
				mStatisticsUtils.addConditionCalculation();
				mCriterion.updateCriterion(state, letter1, letter2);

				if ((condition != null) && (!condition.getFormula().toString().equals("true"))
						&& mCriterion.decide(condition)) {

					BasicPredicate notCondition = mPredicateFactory
							.newPredicate(SmtUtils.not(mManagedScript.getScript(), condition.getFormula()));
					// construct a transformula which represents the negation of the condition
					// via TransFormulaBuilder.constructTransFormulaFromPredicate
					UnmodifiableTransFormula tf =
							TransFormulaBuilder.constructTransFormulaFromPredicate(notCondition, mManagedScript);
					// copy a transition with the new transformula with IcfgCopyFactory from
					// CegarLoopFactory.mCopyFactory (needs to be passed to the CEGAR-Loop)
					L notConditionLetter = mCopyFactory.copy(letter1, tf, tf);
					// create a MLPredicate and a SleepSetPredicate as dummy state
					SleepPredicate<L> dummySleepPredicate =
							new SleepPredicate<L>(mPredicateFactory.newMLDontCarePredicate(null), null);
					// add both to the currentRun
					NestedRun<L, IPredicate> conditionRun =
							new NestedRun<>(currentRun.getStateAtPosition(currentRun.getLength() - 1),
									notConditionLetter, -2, dummySleepPredicate);
					NestedRun<L, IPredicate> currentRunWithCondition = currentRun.concatenate(conditionRun);

					final TracePredicates trace = mTraceChecker.checkTrace(currentRunWithCondition, null, null);
					// final TracePredicates trace = mTraceChecker.checkTrace(currentRun, null, condition);
					mStatisticsUtils.addTraceCheck();
					if (mTraceChecker.wasImperfectProof()) {
						mStatisticsUtils.addImperfectProof();
					}
					return trace;
				}
			}
			return null;
		} finally {
			mStatisticsUtils.stopStopwatch(ConditionalCommutativityStopwatches.CHECKER);
		}
	}

	public IConditionalCommutativityCriterion<L> getCriterion() {
		return mCriterion;
	}

	public ITraceChecker<L> getTraceChecker() {
		return mTraceChecker;
	}

	public enum ConComTraceCheckMode {
		GENERATOR, GENERATOR_WITH_CONTEXT, SYMBOLIC_RELATION
	}
}
