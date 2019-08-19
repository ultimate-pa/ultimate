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

import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.INonrelationalValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.INonrelationalValueFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.NonrelationalEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.NonrelationalUtils;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.EvaluatorUtils.EvaluatorType;

/**
 * An evaluator for unary expressions in a nonrelational abstract domain.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 * @param <VALUE>
 *            The type of values of the abstract domain.
 * @param <STATE>
 *            The type of states of the abstract domain.
 */
public class UnaryExpressionEvaluator<VALUE extends INonrelationalValue<VALUE>, STATE extends IAbstractState<STATE>>
		extends NAryEvaluator<VALUE, STATE> {

	private final EvaluatorLogger mLogger;

	private Operator mOperator;
	private final VALUE mTopValue;

	public UnaryExpressionEvaluator(final EvaluatorLogger logger, final int maxRecursionDepth,
			final INonrelationalValueFactory<VALUE> nonrelationalValueFactory) {
		super(maxRecursionDepth, nonrelationalValueFactory, logger);
		mLogger = logger;
		mTopValue = nonrelationalValueFactory.createTopValue();
	}

	@Override
	public Collection<IEvaluationResult<VALUE>> evaluate(final STATE currentState) {
		assert currentState != null;

		final Collection<IEvaluationResult<VALUE>> returnList = new ArrayList<>();

		final Collection<IEvaluationResult<VALUE>> subResults =
				getSubEvaluator(0).evaluate(currentState, getCurrentEvaluationRecursion() + 1);

		for (final IEvaluationResult<VALUE> subResult : subResults) {
			final VALUE returnValue;
			final BooleanValue returnBool;

			switch (mOperator) {
			case ARITHNEGATIVE:
				returnBool = BooleanValue.INVALID;
				returnValue = subResult.getValue().negate();
				break;
			case LOGICNEG:
				returnBool = subResult.getBooleanValue().neg();
				returnValue = mTopValue;
				break;
			default:
				mLogger.warnUnknownOperator(mOperator);
				returnBool = BooleanValue.TOP;
				returnValue = mTopValue;
				break;
			}

			final NonrelationalEvaluationResult<VALUE> result =
					new NonrelationalEvaluationResult<>(returnValue, returnBool);
			mLogger.logEvaluation(mOperator, result, subResult);
			returnList.add(result);
		}

		assert !returnList.isEmpty();
		return NonrelationalUtils.mergeIfNecessary(returnList, 2);
	}

	@Override
	public Collection<STATE> inverseEvaluate(final IEvaluationResult<VALUE> computedValue, final STATE currentState) {

		VALUE evalValue = computedValue.getValue();
		BooleanValue evalBool = computedValue.getBooleanValue();

		switch (mOperator) {
		case ARITHNEGATIVE:
			evalValue = computedValue.getValue().negate();
			break;
		case LOGICNEG:
			evalBool = computedValue.getBooleanValue().neg();
			break;
		default:
			throw new UnsupportedOperationException(
					new StringBuilder().append("Operator ").append(mOperator).append(" not supported.").toString());
		}

		final NonrelationalEvaluationResult<VALUE> evalResult =
				new NonrelationalEvaluationResult<>(evalValue, evalBool);
		mLogger.logInverseEvaluation(mOperator, evalResult, computedValue);
		return getSubEvaluator(0).inverseEvaluate(evalResult, currentState, getCurrentInverseEvaluationRecursion() + 1);
	}

	@Override
	public boolean hasFreeOperands() {
		return getNumberOfSubEvaluators() == 0;
	}

	@Override
	public boolean containsBool() {
		return getSubEvaluator(0).containsBool();
	}

	@Override
	public void setOperator(final Object operator) {
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
			sb.append('!');
			break;
		case OLD:
			sb.append("old(");
			break;
		case ARITHNEGATIVE:
			sb.append('-');
			break;
		default:
		}

		sb.append(getSubEvaluator(0));

		if (mOperator == Operator.OLD) {
			sb.append(')');
		}

		return sb.toString();
	}

	@Override
	public EvaluatorType getType() {
		return getSubEvaluator(0).getType();
	}
}
