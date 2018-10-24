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
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
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
		implements INAryEvaluator<VALUE, STATE> {

	private final EvaluatorLogger mLogger;
	private final INonrelationalValueFactory<VALUE> mNonrelationalValueFactory;

	private IEvaluator<VALUE, STATE> mSubEvaluator;
	private Operator mOperator;

	public UnaryExpressionEvaluator(final EvaluatorLogger logger,
			final INonrelationalValueFactory<VALUE> nonrelationalValueFactory) {
		mLogger = logger;
		mNonrelationalValueFactory = nonrelationalValueFactory;
	}

	@Override
	public List<IEvaluationResult<VALUE>> evaluate(final STATE currentState) {
		assert currentState != null;

		final List<IEvaluationResult<VALUE>> returnList = new ArrayList<>();

		final List<IEvaluationResult<VALUE>> subResults = mSubEvaluator.evaluate(currentState);

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
				returnValue = mNonrelationalValueFactory.createTopValue();
				break;
			default:
				mLogger.warnUnknownOperator(mOperator);
				returnBool = BooleanValue.TOP;
				returnValue = mNonrelationalValueFactory.createTopValue();
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
		return mSubEvaluator.inverseEvaluate(evalResult, currentState);
	}

	@Override
	public void addSubEvaluator(final IEvaluator<VALUE, STATE> evaluator) {
		assert evaluator != null;

		if (mSubEvaluator == null) {
			mSubEvaluator = evaluator;
		} else {
			throw new UnsupportedOperationException("Cannot add more evaluators to this unary expression evaluator.");
		}
	}

	@Override
	public Set<IProgramVarOrConst> getVarIdentifiers() {
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

		sb.append(mSubEvaluator);

		if (mOperator == Operator.OLD) {
			sb.append(')');
		}

		return sb.toString();
	}

	@Override
	public EvaluatorType getType() {
		return mSubEvaluator.getType();
	}
}
