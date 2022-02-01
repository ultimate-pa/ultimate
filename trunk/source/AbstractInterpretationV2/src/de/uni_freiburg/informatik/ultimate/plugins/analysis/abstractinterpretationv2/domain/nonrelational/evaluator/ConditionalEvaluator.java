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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator;

import java.util.ArrayList;
import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.INonrelationalValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.INonrelationalValueFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.NonrelationalEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.NonrelationalState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.NonrelationalUtils;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.EvaluatorUtils.EvaluatorType;

/**
 * Evaluator for conditional expressions for nonrelational abstract domains.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 * @param <VALUE>
 *            The type of values of the abstract domain.
 * @param <STATE>
 *            The type of states of the abstract domain.
 */
public class ConditionalEvaluator<VALUE extends INonrelationalValue<VALUE>, STATE extends NonrelationalState<STATE, VALUE>>
		extends Evaluator<VALUE, STATE> {

	private final VALUE mTopValue;

	// SubEvaluator order:
	// SubEvaluator(0) = negated condition evaluator
	// SubEvaluator(1) = condition evaluator
	// SubEvaluator(2) = if evaluator
	// SubEvaluator(3) = else evaluator

	public ConditionalEvaluator(final int maxRecursionDepth,
			final INonrelationalValueFactory<VALUE> nonrelationalValueFactory, final EvaluatorLogger logger) {
		super(maxRecursionDepth, nonrelationalValueFactory, logger);
		mTopValue = nonrelationalValueFactory.createTopValue();
	}

	@Override
	public Collection<IEvaluationResult<VALUE>> evaluate(final STATE currentState) {
		assert currentState != null;

		final Collection<IEvaluationResult<VALUE>> returnList = new ArrayList<>();

		final Collection<IEvaluationResult<VALUE>> conditionResult =
				getSubEvaluator(1).evaluate(currentState, getCurrentEvaluationRecursion() + 1);
		final Collection<IEvaluationResult<VALUE>> negatedConditionResult =
				getSubEvaluator(0).evaluate(currentState, getCurrentEvaluationRecursion() + 1);

		for (final IEvaluationResult<VALUE> cond : conditionResult) {
			final Collection<STATE> conditionStates =
					getSubEvaluator(1).inverseEvaluate(cond, currentState, getCurrentEvaluationRecursion() + 1);

			for (final STATE conditionState : conditionStates) {
				switch (cond.getBooleanValue()) {
				case TRUE:
				case TOP:
					final Collection<IEvaluationResult<VALUE>> trueResult =
							getSubEvaluator(2).evaluate(conditionState, getCurrentEvaluationRecursion() + 1);

					for (final IEvaluationResult<VALUE> ifRes : trueResult) {
						if (!ifRes.getValue().isBottom() && !ifRes.getBooleanValue().isBottom()) {
							returnList.add(
									new NonrelationalEvaluationResult<>(ifRes.getValue(), ifRes.getBooleanValue()));
						}
					}

					break;
				default:
					break;
				}
			}
		}

		for (final IEvaluationResult<VALUE> cond : negatedConditionResult) {
			final Collection<STATE> conditionStates =
					getSubEvaluator(0).inverseEvaluate(cond, currentState, getCurrentEvaluationRecursion() + 1);

			for (final STATE conditionState : conditionStates) {
				switch (cond.getBooleanValue()) {
				case TRUE:
				case TOP:
					final Collection<IEvaluationResult<VALUE>> falseResult =
							getSubEvaluator(3).evaluate(conditionState, getCurrentEvaluationRecursion() + 1);

					for (final IEvaluationResult<VALUE> elseRes : falseResult) {
						if (!elseRes.getValue().isBottom() && !elseRes.getBooleanValue().isBottom()) {
							returnList.add(
									new NonrelationalEvaluationResult<>(elseRes.getValue(), elseRes.getBooleanValue()));
						}
					}

					break;
				default:
					break;
				}
			}
		}

		if (returnList.isEmpty()) {
			returnList.add(new NonrelationalEvaluationResult<>(mTopValue, BooleanValue.FALSE));
		}

		return NonrelationalUtils.mergeIfNecessary(returnList, 1);
	}

	@Override
	public Collection<STATE> inverseEvaluate(final IEvaluationResult<VALUE> computedValue, final STATE currentState) {

		final Collection<STATE> returnList = new ArrayList<>();

		final Collection<IEvaluationResult<VALUE>> conditionResult =
				getSubEvaluator(1).evaluate(currentState, getCurrentEvaluationRecursion() + 1);
		final Collection<IEvaluationResult<VALUE>> negatedConditionResult =
				getSubEvaluator(0).evaluate(currentState, getCurrentEvaluationRecursion() + 1);

		for (final IEvaluationResult<VALUE> cond : conditionResult) {
			final Collection<STATE> conditionStates =
					getSubEvaluator(1).inverseEvaluate(cond, currentState, getCurrentEvaluationRecursion() + 1);

			for (final STATE conditionState : conditionStates) {
				switch (cond.getBooleanValue()) {
				case TRUE:
				case TOP:
					final Collection<IEvaluationResult<VALUE>> trueResult =
							getSubEvaluator(2).evaluate(conditionState, getCurrentEvaluationRecursion() + 1);

					for (final IEvaluationResult<VALUE> t : trueResult) {
						final Collection<STATE> ifStates = getSubEvaluator(2).inverseEvaluate(t, conditionState,
								getCurrentEvaluationRecursion() + 1);

						for (final STATE ifState : ifStates) {
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

		for (final IEvaluationResult<VALUE> cond : negatedConditionResult) {
			final Collection<STATE> conditionStates =
					getSubEvaluator(0).inverseEvaluate(cond, currentState, getCurrentEvaluationRecursion() + 1);

			for (final STATE conditionState : conditionStates) {
				switch (cond.getBooleanValue()) {
				case TRUE:
				case TOP:
					final Collection<IEvaluationResult<VALUE>> falseResult =
							getSubEvaluator(3).evaluate(conditionState, getCurrentEvaluationRecursion() + 1);

					for (final IEvaluationResult<VALUE> f : falseResult) {
						final Collection<STATE> elseStates = getSubEvaluator(3).inverseEvaluate(f, conditionState,
								getCurrentEvaluationRecursion() + 1);

						for (final STATE elseState : elseStates) {
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

		return NonrelationalUtils.mergeStatesIfNecessary(returnList, 1);
	}

	@Override
	public boolean hasFreeOperands() {
		return getNumberOfSubEvaluators() < 4;
	}

	@Override
	public boolean containsBool() {
		return getSubEvaluator(2).containsBool() || getSubEvaluator(3).containsBool();
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();

		sb.append("if ").append(getSubEvaluator(1)).append(" [[ ").append(getSubEvaluator(0)).append(" ]]")
				.append(" then ").append(getSubEvaluator(2)).append(" else ").append(getSubEvaluator(3));

		return sb.toString();
	}

	@Override
	public EvaluatorType getType() {
		assert getSubEvaluator(2).getType() == getSubEvaluator(3).getType();
		return getSubEvaluator(2).getType();
	}

}
