/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 * 
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission 
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Class for {@link IfThenElseExpression} evaluators in the {@link IntervalDomain}.
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class IntervalConditionalEvaluator
        implements IEvaluator<IntervalDomainValue, IntervalDomainState, CodeBlock> {

	private final Set<IBoogieVar> mVariables;

	private IEvaluator<IntervalDomainValue, IntervalDomainState, CodeBlock> mConditionEvaluator;
	private IEvaluator<IntervalDomainValue, IntervalDomainState, CodeBlock> mNegatedConditionEvaluator;
	private IEvaluator<IntervalDomainValue, IntervalDomainState, CodeBlock> mIfEvaluator;
	private IEvaluator<IntervalDomainValue, IntervalDomainState, CodeBlock> mElseEvaluator;

	protected IntervalConditionalEvaluator() {
		mVariables = new HashSet<>();
	}

	@Override
	public List<IEvaluationResult<IntervalDomainValue>> evaluate(final IntervalDomainState currentState) {
		final List<IEvaluationResult<IntervalDomainValue>> returnList = new ArrayList<>();

		final List<IEvaluationResult<IntervalDomainValue>> conditionResult = mConditionEvaluator.evaluate(currentState);
		final List<IEvaluationResult<IntervalDomainValue>> negatedConditionResult = mNegatedConditionEvaluator
		        .evaluate(currentState);

		for (final IEvaluationResult<IntervalDomainValue> cond : conditionResult) {
			final List<IntervalDomainState> conditionStates = mConditionEvaluator.inverseEvaluate(cond, currentState);

			for (final IntervalDomainState conditionState : conditionStates) {

				switch (cond.getBooleanValue().getValue()) {
				case TRUE:
				case TOP:
					final List<IEvaluationResult<IntervalDomainValue>> trueResult = mIfEvaluator
					        .evaluate(conditionState);

					for (final IEvaluationResult<IntervalDomainValue> ifRes : trueResult) {
						if (!ifRes.getValue().isBottom() && !ifRes.getBooleanValue().isBottom()) {
							returnList
							        .add(new IntervalDomainEvaluationResult(ifRes.getValue(), ifRes.getBooleanValue()));
						}
					}

					mVariables.addAll(mIfEvaluator.getVarIdentifiers());
					break;
				default:
					break;
				}
			}
		}

		for (final IEvaluationResult<IntervalDomainValue> cond : negatedConditionResult) {
			final List<IntervalDomainState> conditionStates = mNegatedConditionEvaluator.inverseEvaluate(cond,
			        currentState);

			for (final IntervalDomainState conditionState : conditionStates) {
				switch (cond.getBooleanValue().getValue()) {
				case TRUE:
				case TOP:
					final List<IEvaluationResult<IntervalDomainValue>> falseResult = mElseEvaluator
					        .evaluate(conditionState);

					for (final IEvaluationResult<IntervalDomainValue> elseRes : falseResult) {
						if (!elseRes.getValue().isBottom() && !elseRes.getBooleanValue().isBottom()) {
							returnList.add(
							        new IntervalDomainEvaluationResult(elseRes.getValue(), elseRes.getBooleanValue()));
						}
					}

					mVariables.addAll(mElseEvaluator.getVarIdentifiers());
					break;
				default:
					break;
				}
			}
		}

		if (returnList.isEmpty()) {
			returnList.add(new IntervalDomainEvaluationResult(new IntervalDomainValue(),
			        new BooleanValue(BooleanValue.Value.FALSE)));
		}

		return IntervalUtils.mergeIfNecessary(returnList, 1);
	}

	@Override
	public void addSubEvaluator(
	        final IEvaluator<IntervalDomainValue, IntervalDomainState, CodeBlock> evaluator) {
		if (mNegatedConditionEvaluator == null) {
			mNegatedConditionEvaluator = evaluator;
		} else if (mConditionEvaluator == null) {
			mConditionEvaluator = evaluator;
		} else if (mIfEvaluator == null) {
			mIfEvaluator = evaluator;
		} else if (mElseEvaluator == null) {
			mElseEvaluator = evaluator;
		} else {
			throw new UnsupportedOperationException("No sub evaluators left to fill.");
		}

	}

	@Override
	public Set<IBoogieVar> getVarIdentifiers() {
		return mVariables;
	}

	@Override
	public boolean hasFreeOperands() {
		return mConditionEvaluator == null || mIfEvaluator == null || mElseEvaluator == null;
	}

	@Override
	public boolean containsBool() {
		return mIfEvaluator.containsBool() || mElseEvaluator.containsBool();
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder(50);

		sb.append("if ").append(mConditionEvaluator).append(" [[ ").append(mNegatedConditionEvaluator).append(" ]]")
		        .append(" then ").append(mIfEvaluator).append(" else ").append(mElseEvaluator);

		return sb.toString();
	}

	@Override
	public List<IntervalDomainState> inverseEvaluate(final IEvaluationResult<IntervalDomainValue> computedValue,
	        final IntervalDomainState currentState) {

		final List<IntervalDomainState> returnList = new ArrayList<>();

		final List<IEvaluationResult<IntervalDomainValue>> conditionResult = mConditionEvaluator.evaluate(currentState);
		final List<IEvaluationResult<IntervalDomainValue>> negatedConditionResult = mNegatedConditionEvaluator
		        .evaluate(currentState);

		for (final IEvaluationResult<IntervalDomainValue> cond : conditionResult) {
			final List<IntervalDomainState> conditionStates = mConditionEvaluator.inverseEvaluate(cond, currentState);

			for (final IntervalDomainState conditionState : conditionStates) {
				switch (cond.getBooleanValue().getValue()) {
				case TRUE:
				case TOP:
					final List<IEvaluationResult<IntervalDomainValue>> trueResult = mIfEvaluator
					        .evaluate(conditionState);

					for (final IEvaluationResult<IntervalDomainValue> t : trueResult) {
						final List<IntervalDomainState> ifStates = mIfEvaluator.inverseEvaluate(t, conditionState);

						for (final IntervalDomainState ifState : ifStates) {
							if (!ifState.isBottom()) {
								returnList.add(ifState);
							}
						}
					}

					break;
				default:
					break;
				}
			}
		}

		for (final IEvaluationResult<IntervalDomainValue> cond : negatedConditionResult) {
			final List<IntervalDomainState> conditionStates = mNegatedConditionEvaluator.inverseEvaluate(cond,
			        currentState);

			for (final IntervalDomainState conditionState : conditionStates) {
				switch (cond.getBooleanValue().getValue()) {
				case TRUE:
				case TOP:
					final List<IEvaluationResult<IntervalDomainValue>> falseResult = mElseEvaluator
					        .evaluate(conditionState);

					for (final IEvaluationResult<IntervalDomainValue> f : falseResult) {
						final List<IntervalDomainState> elseStates = mElseEvaluator.inverseEvaluate(f, conditionState);

						for (final IntervalDomainState elseState : elseStates) {
							if (!elseState.isBottom()) {
								returnList.add(elseState);
							}
						}
					}
					break;
				default:
					break;
				}
			}
		}

		if (returnList.isEmpty()) {
			returnList.add(currentState.bottomState());
		}

		return IntervalUtils.mergeStatesIfNecessary(returnList, 1);
	}
}
