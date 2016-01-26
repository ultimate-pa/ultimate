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
import java.util.List;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue.Value;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.EvaluatorUtils.EvaluatorType;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.INAryEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Class that handles unary logical expression evaluators in the {@link IntervalDomain}.
 * 
 * @author Marius Greitschus <greitsch@informatik.uni-freiburg.de>
 *
 */
public class IntervalUnaryExpressionEvaluator
        implements INAryEvaluator<IntervalDomainEvaluationResult, IntervalDomainState, CodeBlock, IBoogieVar> {

	private final Logger mLogger;
	private final EvaluatorType mEvaluatorType;

	protected IEvaluator<IntervalDomainEvaluationResult, IntervalDomainState, CodeBlock, IBoogieVar> mSubEvaluator;
	protected Operator mOperator;

	protected IntervalUnaryExpressionEvaluator(Logger logger, EvaluatorType type) {
		mLogger = logger;
		mEvaluatorType = type;
	}

	@Override
	public List<IEvaluationResult<IntervalDomainEvaluationResult>> evaluate(IntervalDomainState currentState) {

		final List<IEvaluationResult<IntervalDomainEvaluationResult>> subEvaluatorResult = mSubEvaluator
		        .evaluate(currentState);

		final List<IEvaluationResult<IntervalDomainEvaluationResult>> returnEvaluationResults = new ArrayList<>();

		for (final IEvaluationResult<IntervalDomainEvaluationResult> result : subEvaluatorResult) {
			IntervalDomainState returnState = currentState.copy();
			IntervalDomainValue returnValue = new IntervalDomainValue();
			BooleanValue returnBool;

			boolean setToBottom = false;

			switch (mOperator) {
			case ARITHNEGATIVE:
				returnBool = new BooleanValue(false);
				returnValue = result.getResult().getEvaluatedValue().negate();
				break;
			case LOGICNEG:
				returnBool = result.getBooleanValue().neg();
				if (returnBool.getValue() == Value.FALSE || returnBool.getValue() == Value.BOTTOM) {
					setToBottom = true;
				}
				break;
			default:
				mLogger.warn(
				        "Operator " + mOperator + " not implemented. Assuming logical interpretation to be false.");
				returnBool = new BooleanValue(false);
				mLogger.warn("Possible loss of precision: cannot handle operator " + mOperator
				        + ". Returning current state. Returned value is top.");
				returnValue = new IntervalDomainValue();
			}

			if (setToBottom) {
				returnState = returnState.bottomState();
			}

			returnEvaluationResults.add(new IntervalDomainEvaluationResult(returnValue, returnState, returnBool));
		}

		return returnEvaluationResults;
	}

	@Override
	public void addSubEvaluator(
	        IEvaluator<IntervalDomainEvaluationResult, IntervalDomainState, CodeBlock, IBoogieVar> evaluator) {
		assert mSubEvaluator == null;
		assert evaluator != null;

		mSubEvaluator = evaluator;
	}

	@Override
	public Set<String> getVarIdentifiers() {
		return mSubEvaluator.getVarIdentifiers();
	}

	@Override
	public boolean hasFreeOperands() {
		return mSubEvaluator == null;
	}

	@Override
	public boolean containsBool() {
		return mSubEvaluator.containsBool();
	}

	@Override
	public void setOperator(Object operator) {
		assert operator != null;
		assert operator instanceof Operator;
		mOperator = (Operator) operator;
	}

	@Override
	public int getArity() {
		return 1;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();

		switch (mOperator) {
		case LOGICNEG:
			sb.append("!");
			break;
		case OLD:
			sb.append("old(");
			break;
		case ARITHNEGATIVE:
			sb.append("-");
			break;
		default:
		}

		sb.append(mSubEvaluator);

		if (mOperator == Operator.OLD) {
			sb.append(")");
		}

		return sb.toString();
	}

	@Override
	public EvaluatorType getEvaluatorType() {
		return mEvaluatorType;
	}
}
