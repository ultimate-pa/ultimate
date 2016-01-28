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
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public class IntervalConditionalEvaluator
        implements IEvaluator<IntervalDomainEvaluationResult, IntervalDomainState, CodeBlock, IBoogieVar> {

	private final Set<String> mVariables;

	private IEvaluator<IntervalDomainEvaluationResult, IntervalDomainState, CodeBlock, IBoogieVar> mConditionEvaluator;
	private IEvaluator<IntervalDomainEvaluationResult, IntervalDomainState, CodeBlock, IBoogieVar> mNegatedConditionEvaluator;
	private IEvaluator<IntervalDomainEvaluationResult, IntervalDomainState, CodeBlock, IBoogieVar> mIfEvaluator;
	private IEvaluator<IntervalDomainEvaluationResult, IntervalDomainState, CodeBlock, IBoogieVar> mElseEvaluator;

	protected IntervalConditionalEvaluator() {
		mVariables = new HashSet<>();
	}

	@Override
	public List<IEvaluationResult<IntervalDomainEvaluationResult>> evaluate(IntervalDomainState currentState) {
		final List<IEvaluationResult<IntervalDomainEvaluationResult>> returnList = new ArrayList<>();

		final List<IEvaluationResult<IntervalDomainEvaluationResult>> conditionResult = mConditionEvaluator
		        .evaluate(currentState);
		final List<IEvaluationResult<IntervalDomainEvaluationResult>> negatedConditionResult = mNegatedConditionEvaluator
		        .evaluate(currentState);

		for (final IEvaluationResult<IntervalDomainEvaluationResult> cond : conditionResult) {
			final IntervalDomainState conditionState = cond.getResult().getEvaluatedState();

			switch (cond.getBooleanValue().getValue()) {
			case TRUE:
			case TOP:
				final List<IEvaluationResult<IntervalDomainEvaluationResult>> trueResult = mIfEvaluator
				        .evaluate(conditionState);

				for (final IEvaluationResult<IntervalDomainEvaluationResult> ifRes : trueResult) {
					if (!ifRes.getResult().getEvaluatedState().isBottom()) {
						returnList.add(new IntervalDomainEvaluationResult(ifRes.getResult().getEvaluatedValue(),
						        ifRes.getResult().getEvaluatedState(), ifRes.getBooleanValue()));
					}
				}

				mVariables.addAll(mIfEvaluator.getVarIdentifiers());
				break;
			default:
				break;
			}
		}

		for (final IEvaluationResult<IntervalDomainEvaluationResult> cond : negatedConditionResult) {
			final IntervalDomainState conditionState = cond.getResult().getEvaluatedState();

			switch (cond.getBooleanValue().getValue()) {
			case TRUE:
			case TOP:
				final List<IEvaluationResult<IntervalDomainEvaluationResult>> falseResult = mElseEvaluator
				        .evaluate(conditionState);

				for (final IEvaluationResult<IntervalDomainEvaluationResult> elseRes : falseResult) {
					if (!elseRes.getResult().getEvaluatedState().isBottom()) {
						returnList.add(new IntervalDomainEvaluationResult(elseRes.getResult().getEvaluatedValue(),
						        elseRes.getResult().getEvaluatedState(), elseRes.getBooleanValue()));
					}
				}

				mVariables.addAll(mElseEvaluator.getVarIdentifiers());
				break;
			default:
				break;
			}
		}

		if (returnList.size() == 0) {
			returnList.add(new IntervalDomainEvaluationResult(new IntervalDomainValue(), currentState,
			        new BooleanValue(BooleanValue.Value.FALSE)));
		}
		List<IEvaluationResult<IntervalDomainEvaluationResult>> ret = mergeList(returnList);
		return ret;
	}

	private List<IEvaluationResult<IntervalDomainEvaluationResult>> mergeList(
	        List<IEvaluationResult<IntervalDomainEvaluationResult>> results) {
		return Collections.singletonList(results.stream().reduce(this::merge).get());
	}

	private IEvaluationResult<IntervalDomainEvaluationResult> merge(
	        final IEvaluationResult<IntervalDomainEvaluationResult> a,
	        IEvaluationResult<IntervalDomainEvaluationResult> b) {
		final IntervalDomainEvaluationResult left = a.getResult();
		final IntervalDomainEvaluationResult right = b.getResult();
		return new IntervalDomainEvaluationResult(left.getEvaluatedValue().merge(right.getEvaluatedValue()),
		        left.getEvaluatedState().merge(right.getEvaluatedState()),
		        left.getBooleanValue().merge(right.getBooleanValue()));
	}

	@Override
	public void addSubEvaluator(
	        IEvaluator<IntervalDomainEvaluationResult, IntervalDomainState, CodeBlock, IBoogieVar> evaluator) {
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
	public List<IEvaluationResult<IntervalDomainEvaluationResult>> inverseEvaluate(
	        IEvaluationResult<IntervalDomainEvaluationResult> computedState) {

		final IntervalDomainState currentState = computedState.getResult().getEvaluatedState();

		final List<IEvaluationResult<IntervalDomainEvaluationResult>> returnList = new ArrayList<>();

		final List<IEvaluationResult<IntervalDomainEvaluationResult>> conditionResult = mConditionEvaluator
		        .evaluate(currentState);
		final List<IEvaluationResult<IntervalDomainEvaluationResult>> negatedConditionResult = mNegatedConditionEvaluator
		        .evaluate(currentState);

		for (final IEvaluationResult<IntervalDomainEvaluationResult> cond : conditionResult) {
			final IntervalDomainState conditionState = cond.getResult().getEvaluatedState();

			switch (cond.getBooleanValue().getValue()) {
			case TRUE:
			case TOP:
				final List<IEvaluationResult<IntervalDomainEvaluationResult>> trueResult = mIfEvaluator
				        .evaluate(conditionState);

				for (final IEvaluationResult<IntervalDomainEvaluationResult> t : trueResult) {
					if (!t.getResult().getEvaluatedState().isBottom()) {
						final IntervalDomainEvaluationResult trueInverse = new IntervalDomainEvaluationResult(
						        t.getResult().getEvaluatedValue(), t.getResult().getEvaluatedState(),
						        t.getBooleanValue());
						final List<IEvaluationResult<IntervalDomainEvaluationResult>> trueInverseResult = mIfEvaluator
						        .inverseEvaluate(trueInverse);

						for (final IEvaluationResult<IntervalDomainEvaluationResult> ifRes : trueInverseResult) {
							returnList.add(new IntervalDomainEvaluationResult(ifRes.getResult().getEvaluatedValue(),
							        ifRes.getResult().getEvaluatedState(), t.getBooleanValue()));
						}
					}
				}

				break;
			default:
				break;
			}
		}

		for (final IEvaluationResult<IntervalDomainEvaluationResult> cond : negatedConditionResult) {
			final IntervalDomainState conditionState = cond.getResult().getEvaluatedState();

			switch (cond.getBooleanValue().getValue()) {
			case TRUE:
			case TOP:
				final List<IEvaluationResult<IntervalDomainEvaluationResult>> falseResult = mElseEvaluator
				        .evaluate(conditionState);

				for (final IEvaluationResult<IntervalDomainEvaluationResult> f : falseResult) {
					if (!f.getResult().getEvaluatedState().isBottom()) {
						final IntervalDomainEvaluationResult falseInverse = new IntervalDomainEvaluationResult(
						        f.getResult().getEvaluatedValue(), f.getResult().getEvaluatedState(),
						        f.getBooleanValue());
						final List<IEvaluationResult<IntervalDomainEvaluationResult>> falseInverseResult = mElseEvaluator
						        .inverseEvaluate(falseInverse);

						for (final IEvaluationResult<IntervalDomainEvaluationResult> elseRes : falseInverseResult) {
							returnList.add(new IntervalDomainEvaluationResult(elseRes.getResult().getEvaluatedValue(),
							        elseRes.getResult().getEvaluatedState(), f.getBooleanValue()));
						}
					}
				}
				break;
			default:
				break;
			}
		}

		if (returnList.size() == 0) {
			returnList.add(new IntervalDomainEvaluationResult(new IntervalDomainValue(), currentState,
			        new BooleanValue(BooleanValue.Value.FALSE)));
		}

		return mergeList(returnList);
	}
}
