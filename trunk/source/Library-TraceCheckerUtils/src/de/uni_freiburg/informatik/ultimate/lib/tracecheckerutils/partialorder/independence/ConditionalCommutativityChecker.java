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

import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation.Dependence;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.TracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateWithConjuncts;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.ITraceChecker;
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
public class ConditionalCommutativityChecker<L extends IAction> implements IConditionalCommutativityChecker<L> {

	private final IConditionalCommutativityCriterion<L> mCriterion;
	private IIndependenceRelation<IPredicate, L> mIndependenceRelation;
	private final IIndependenceConditionGenerator mGenerator;
	private final ITraceChecker<L> mTraceChecker;
	private ManagedScript mManagedScript;
	private IConditionalCommutativityCheckerStatisticsUtils mStatisticsUtils;

	/**
	 * Constructs a new instance of ConditionalCommutativityChecker.
	 *
	 * @author Marcel Ebbinghaus
	 *
	 * @param criterion
	 *            An IConditionalCommutativityCriterion to decide when to check for conditional commutativity
	 * @param independenceRelation
	 *            Independence relation for commutativity
	 * @param script
	 *            Script for conjunction handling           
	 * @param generator
	 *            Generator for constructing commutativity conditions
	 * @param traceChecker
	 *            An ITraceChecker responsible for checking whether a condition is feasible
	 * @param statisticsUtils
	 *            An IConditionalCommutativityCheckerStatisticsUtils used for statistics
	 */
	public ConditionalCommutativityChecker(final IConditionalCommutativityCriterion<L> criterion,
			final IIndependenceRelation<IPredicate, L> independenceRelation, ManagedScript script,
			final IIndependenceConditionGenerator generator, final ITraceChecker<L> traceChecker,
			final IConditionalCommutativityCheckerStatisticsUtils statisticsUtils) {
		mCriterion = criterion;
		mIndependenceRelation = independenceRelation;
		mManagedScript = script;
		mGenerator = generator;
		mTraceChecker = traceChecker;
		mStatisticsUtils = statisticsUtils;
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
	 * @return
	 *            A list of predicates which servers as a proof for conditional commutativity.
	 */
	@Override
	public TracePredicates checkConditionalCommutativity(final IRun<L, IPredicate> currentRun,
			List<IPredicate> predicates, final IPredicate state, final L letter1, final L letter2) {
		
		mStatisticsUtils.startStopwatch();
		if (mManagedScript.isLocked()) {
			mManagedScript.requestLockRelease();
		}
		
		if (((IAction) letter1).getSucceedingProcedure().equals(((IAction) letter2).getSucceedingProcedure())) {
			mStatisticsUtils.stopStopwatch();
			return null;
		}
		
		if (state instanceof SleepPredicate) {
			ImmutableSet<?> sleepSet = ((SleepPredicate<L>) state).getSleepSet();
			if (sleepSet.contains(letter1) && sleepSet.contains(letter2)) {
				mStatisticsUtils.stopStopwatch();
				return null;
			}
		}
		
		IPredicate pred = null;
		if (!predicates.isEmpty()) {
			pred  = new PredicateWithConjuncts(0, new ImmutableList<>(predicates), mManagedScript.getScript());
			pred = new BasicPredicate(0, pred.getProcedures(), pred.getFormula(), pred.getVars(),
					pred.getFuns(), pred.getClosedFormula());
		}
				
		if (mIndependenceRelation.isIndependent(pred, letter1, letter2).equals(Dependence.INDEPENDENT)) {
			mStatisticsUtils.stopStopwatch();
			return null;
		}
		
		if (mCriterion.decide(state, letter1, letter2)) {
			
			if (mManagedScript.isLocked()) {
				mManagedScript.requestLockRelease();
			}
			IPredicate condition;
			if (pred != null) {
				condition = mGenerator.generateCondition(
						new PredicateWithConjuncts(0, new ImmutableList<>(predicates), mManagedScript.getScript()),
						letter1.getTransformula(), letter2.getTransformula());
			} else {
				condition = mGenerator.generateCondition(letter1.getTransformula(), letter2.getTransformula());
			}
			mCriterion.updateCriterion(state, letter1, letter2);
			
			if ((condition != null) && (!condition.getFormula().toString().equals("true")) && mCriterion.decide(condition)) {
				
				TracePredicates trace = mTraceChecker.checkTrace(currentRun, null, condition);
				if (trace != null) {
						//mCriterion.updateCondition(condition);
				} else if (mTraceChecker.wasImperfectProof()) {
					mStatisticsUtils.addImperfectProof();
				}
				mStatisticsUtils.stopStopwatch();
				return trace;
			}
		}
		mStatisticsUtils.stopStopwatch();
		return null;
	}
	
	public IConditionalCommutativityCriterion<L> getCriterion() {
		return mCriterion;
	}
	
	public ITraceChecker<L> getTraceChecker() {
		return mTraceChecker;
	}

	public IConditionalCommutativityCheckerStatisticsUtils getStatisticsUtils() {
		return mStatisticsUtils;
	}
}
