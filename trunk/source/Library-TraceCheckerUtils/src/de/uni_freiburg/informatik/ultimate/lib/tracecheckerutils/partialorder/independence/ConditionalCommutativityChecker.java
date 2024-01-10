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

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.TracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.ITraceChecker;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.SleepSetStateFactoryForRefinement.SleepPredicate;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Conditional commutativity checker.
 *
 * @author Marcel Ebbinghaus
 *
 * @param <L>
 *            The type of letters.
 */
public class ConditionalCommutativityChecker<L extends IAction> implements IConditionalCommutativityChecker<L> {

	private final IConditionalCommutativityCriterion<L, IPredicate> mCriterion;
	private final IIndependenceConditionGenerator mGenerator;
	private final ITraceChecker<L> mTraceChecker;
	private Map<Pair<L,L>,Integer> mStatementMap;

	/**
	 * Constructs a new instance of ConditionalCommutativityChecker.
	 *
	 * @author Marcel Ebbinghaus
	 *
	 * @param criterion
	 *            An IConditionalCommutativityCriterion to decide when to check for conditional commutativity
	 * @param generator
	 *            Generator for constructing commutativity conditions
	 * @param traceChecker
	 *            An ITraceChecker responsible for checking whether a condition is feasible
	 */
	public ConditionalCommutativityChecker(final IConditionalCommutativityCriterion<L, IPredicate> criterion,
			final IIndependenceConditionGenerator generator, final ITraceChecker<L> traceChecker) {
		mCriterion = criterion;
		mGenerator = generator;
		mTraceChecker = traceChecker;
		mStatementMap = new HashMap<>();
	}

	/**
	 * Checks for conditional commutativity.
	 *
	 * @author Marcel Ebbinghaus
	 *
	 * @param run
	 *            The run to state
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
	public TracePredicates checkConditionalCommutativity(final IRun<L, IPredicate> run, final IPredicate state,
			final L letter1, final L letter2) {
		
		//ensures that each pair is checked at most two times
		Pair<L,L> pair = new Pair<>(letter1,letter2);
		if (!mStatementMap.containsKey(pair)) {
			mStatementMap.put(pair, 1);
		} else if (mStatementMap.get(pair) == 1) {
			mStatementMap.replace(pair, 2);
		}	else {
			return null;
		}
		
		if (mCriterion.decide(state, letter1, letter2)) {
			IPredicate condition;
			if (true) {
				condition = mGenerator.generateCondition(letter1.getTransformula(), letter2.getTransformula());
			} else {
				condition = mGenerator.generateCondition(state, letter1.getTransformula(), letter2.getTransformula());
			}
			
			if (mCriterion.decide(condition)) {
				return mTraceChecker.checkTrace(run, null, condition);
			}
		}
		return null;
	}
}
