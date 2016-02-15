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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.congruence;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Class for {@link IfThenElseExpression} evaluators in the {@link CongruenceDomain}.
 * 
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */

public class CongruenceConditionalEvaluator
        implements IEvaluator<CongruenceDomainValue, CongruenceDomainState, CodeBlock, IBoogieVar> {

	private final Set<String> mVariables;

	private IEvaluator<CongruenceDomainValue, CongruenceDomainState, CodeBlock, IBoogieVar> mConditionEvaluator;
	private IEvaluator<CongruenceDomainValue, CongruenceDomainState, CodeBlock, IBoogieVar> mNegatedConditionEvaluator;
	private IEvaluator<CongruenceDomainValue, CongruenceDomainState, CodeBlock, IBoogieVar> mIfEvaluator;
	private IEvaluator<CongruenceDomainValue, CongruenceDomainState, CodeBlock, IBoogieVar> mElseEvaluator;

	protected CongruenceConditionalEvaluator() {
		mVariables = new HashSet<>();
	}

	@Override
	public List<IEvaluationResult<CongruenceDomainValue>> evaluate(CongruenceDomainState currentState) {
		final List<IEvaluationResult<CongruenceDomainValue>> returnList = new ArrayList<>();

		final List<IEvaluationResult<CongruenceDomainValue>> conditionResult = mConditionEvaluator.evaluate(currentState);
		final List<IEvaluationResult<CongruenceDomainValue>> negatedConditionResult = mNegatedConditionEvaluator
		        .evaluate(currentState);

		for (final IEvaluationResult<CongruenceDomainValue> cond : conditionResult) {
			final List<CongruenceDomainState> conditionStates = mConditionEvaluator.inverseEvaluate(cond, currentState);

			for (final CongruenceDomainState conditionState : conditionStates) {

				switch (cond.getBooleanValue().getValue()) {
				case TRUE:
				case TOP:
					final List<IEvaluationResult<CongruenceDomainValue>> trueResult = mIfEvaluator
					        .evaluate(conditionState);

					for (final IEvaluationResult<CongruenceDomainValue> ifRes : trueResult) {
						if (!ifRes.getValue().isBottom() && !ifRes.getBooleanValue().isBottom()) {
							returnList
							        .add(new CongruenceDomainEvaluationResult(ifRes.getValue(), ifRes.getBooleanValue()));
						}
					}

					mVariables.addAll(mIfEvaluator.getVarIdentifiers());
					break;
				default:
					break;
				}
			}
		}

		for (final IEvaluationResult<CongruenceDomainValue> cond : negatedConditionResult) {
			final List<CongruenceDomainState> conditionStates = mNegatedConditionEvaluator.inverseEvaluate(cond,
			        currentState);

			for (final CongruenceDomainState conditionState : conditionStates) {
				switch (cond.getBooleanValue().getValue()) {
				case TRUE:
				case TOP:
					final List<IEvaluationResult<CongruenceDomainValue>> falseResult = mElseEvaluator
					        .evaluate(conditionState);

					for (final IEvaluationResult<CongruenceDomainValue> elseRes : falseResult) {
						if (!elseRes.getValue().isBottom() && !elseRes.getBooleanValue().isBottom()) {
							returnList.add(
							        new CongruenceDomainEvaluationResult(elseRes.getValue(), elseRes.getBooleanValue()));
						}
					}

					mVariables.addAll(mElseEvaluator.getVarIdentifiers());
					break;
				default:
					break;
				}
			}
		}

		if (returnList.size() == 0) {
			returnList.add(new CongruenceDomainEvaluationResult(new CongruenceDomainValue(),
			        new BooleanValue(BooleanValue.Value.FALSE)));
		}

		return CongruenceUtils.mergeIfNecessary(returnList, 1);
	}

	@Override
	public void addSubEvaluator(IEvaluator<CongruenceDomainValue, CongruenceDomainState, CodeBlock, IBoogieVar> evaluator) {
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
	public Set<String> getVarIdentifiers() {
		return mVariables;
	}

	@Override
	public boolean hasFreeOperands() {
		return mConditionEvaluator == null || mIfEvaluator == null || mElseEvaluator == null;
	}

	@Override
	public boolean containsBool() {
		return true;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();

		sb.append("if ");
		sb.append(mConditionEvaluator);
		sb.append(" [[ ");
		sb.append(mNegatedConditionEvaluator);
		sb.append(" ]]");
		sb.append(" then ");
		sb.append(mIfEvaluator);
		sb.append(" else ");
		sb.append(mElseEvaluator);

		return sb.toString();
	}

	@Override
	public List<CongruenceDomainState> inverseEvaluate(IEvaluationResult<CongruenceDomainValue> computedValue,
	        CongruenceDomainState currentState) {

		final List<CongruenceDomainState> returnList = new ArrayList<>();

		final List<IEvaluationResult<CongruenceDomainValue>> conditionResult = mConditionEvaluator.evaluate(currentState);
		final List<IEvaluationResult<CongruenceDomainValue>> negatedConditionResult = mNegatedConditionEvaluator
		        .evaluate(currentState);

		for (final IEvaluationResult<CongruenceDomainValue> cond : conditionResult) {
			final List<CongruenceDomainState> conditionStates = mConditionEvaluator.inverseEvaluate(cond, currentState);

			for (final CongruenceDomainState conditionState : conditionStates) {
				switch (cond.getBooleanValue().getValue()) {
				case TRUE:
				case TOP:
					final List<IEvaluationResult<CongruenceDomainValue>> trueResult = mIfEvaluator
					        .evaluate(conditionState);

					for (final IEvaluationResult<CongruenceDomainValue> t : trueResult) {
						final List<CongruenceDomainState> ifStates = mIfEvaluator.inverseEvaluate(t, conditionState);

						for (final CongruenceDomainState ifState : ifStates) {
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

		for (final IEvaluationResult<CongruenceDomainValue> cond : negatedConditionResult) {
			final List<CongruenceDomainState> conditionStates = mNegatedConditionEvaluator.inverseEvaluate(cond,
			        currentState);

			for (final CongruenceDomainState conditionState : conditionStates) {
				switch (cond.getBooleanValue().getValue()) {
				case TRUE:
				case TOP:
					final List<IEvaluationResult<CongruenceDomainValue>> falseResult = mElseEvaluator
					        .evaluate(conditionState);

					for (final IEvaluationResult<CongruenceDomainValue> f : falseResult) {
						final List<CongruenceDomainState> elseStates = mElseEvaluator.inverseEvaluate(f, conditionState);

						for (final CongruenceDomainState elseState : elseStates) {
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

		if (returnList.size() == 0) {
			returnList.add(currentState.bottomState());
		}

		return CongruenceUtils.mergeStatesIfNecessary(returnList, 1);
	}
}
