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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.sign;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.INAryEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.sign.SignDomainValue.SignValues;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Expression evaluator for unary expressions in the interval domain.
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class SignUnaryExpressionEvaluator implements INAryEvaluator<SignDomainValue, SignDomainState, CodeBlock> {

	protected IEvaluator<SignDomainValue, SignDomainState, CodeBlock> mSubEvaluator;
	protected UnaryExpression.Operator mOperator;

	@Override
	public void addSubEvaluator(IEvaluator<SignDomainValue, SignDomainState, CodeBlock> evaluator) {
		assert mSubEvaluator == null;
		assert evaluator != null;
		mSubEvaluator = evaluator;
	}

	@Override
	public void setOperator(Object operator) {
		assert operator != null;
		assert operator instanceof Operator;
		mOperator = (Operator) operator;
	}

	@Override
	public List<IEvaluationResult<SignDomainValue>> evaluate(SignDomainState oldState) {

		final List<IEvaluationResult<SignDomainValue>> returnList = new ArrayList<>();

		final List<IEvaluationResult<SignDomainValue>> subEvalResult = mSubEvaluator.evaluate(oldState);

		for (final IEvaluationResult<SignDomainValue> res : subEvalResult) {
			switch (mOperator) {
			case LOGICNEG:
				// returnList.add(negateValue(res.getValue()));
				break;
			case ARITHNEGATIVE:
				// returnList.add(negateValue(res.getValue()));
				break;
			default:
				throw new UnsupportedOperationException(
						"The operator " + mOperator.toString() + " is not implemented.");
			}
		}

		return returnList;
	}

	private IEvaluationResult<SignDomainValue.SignValues> negateValue(SignDomainValue.SignValues value) {
		assert value != null;

		switch (value) {
		case POSITIVE:
			return new SignDomainValue(SignValues.NEGATIVE);
		case NEGATIVE:
			return new SignDomainValue(SignValues.POSITIVE);
		case TOP:
			return new SignDomainValue(SignValues.TOP);
		case BOTTOM:
			return new SignDomainValue(SignValues.BOTTOM);
		case ZERO:
			return new SignDomainValue(SignValues.ZERO);
		default:
			throw new UnsupportedOperationException(
					"The sign domain value " + value.toString() + " is not implemented.");
		}
	}

	@Override
	public boolean hasFreeOperands() {
		return (mSubEvaluator == null);
	}

	@Override
	public Set<IBoogieVar> getVarIdentifiers() {
		return mSubEvaluator.getVarIdentifiers();
	}

	@Override
	public int getArity() {
		return 1;
	}

	@Override
	public boolean containsBool() {
		throw new UnsupportedOperationException("not implemented");
	}

	@Override
	public List<SignDomainState> inverseEvaluate(final IEvaluationResult<SignDomainValue> computedValue,
			final SignDomainState currentState) {
		throw new UnsupportedOperationException("not implemented");
	}
}
