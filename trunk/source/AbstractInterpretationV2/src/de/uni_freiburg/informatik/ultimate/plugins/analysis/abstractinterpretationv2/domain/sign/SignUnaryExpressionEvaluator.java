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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.evaluator.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.evaluator.IEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.evaluator.INAryEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign.SignDomainValue.Values;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Expression evaluator for unary expressions in the interval domain.
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public class SignUnaryExpressionEvaluator implements INAryEvaluator<Values, CodeBlock, BoogieVar> {

	protected IEvaluator<Values, CodeBlock, BoogieVar> mSubEvaluator;
	protected UnaryExpression.Operator mOperator;

	@Override
	public void addSubEvaluator(IEvaluator<Values, CodeBlock, BoogieVar> evaluator) {

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
	public IEvaluationResult<Values> evaluate(IAbstractState<CodeBlock, BoogieVar> oldState) {

		IEvaluator<Values, CodeBlock, BoogieVar> castedSubEvaluator = (IEvaluator<Values, CodeBlock, BoogieVar>) mSubEvaluator;
		final IEvaluationResult<Values> subEvalResult = (IEvaluationResult<Values>) castedSubEvaluator
		        .evaluate(oldState);

		switch (mOperator) {
		case LOGICNEG:
			return negateValue(subEvalResult.getResult());
		case ARITHNEGATIVE:
			return negateValue(subEvalResult.getResult());
		default:
			throw new UnsupportedOperationException("The operator " + mOperator.toString() + " is not implemented.");
		}
	}

	private IEvaluationResult<SignDomainValue.Values> negateValue(SignDomainValue.Values value) {
		assert value != null;

		switch (value) {
		case POSITIVE:
			return new SignDomainValue(Values.NEGATIVE);
		case NEGATIVE:
			return new SignDomainValue(Values.POSITIVE);
		case TOP:
			return new SignDomainValue(Values.TOP);
		case BOTTOM:
			return new SignDomainValue(Values.BOTTOM);
		case ZERO:
			return new SignDomainValue(Values.ZERO);
		default:
			throw new UnsupportedOperationException("The sign domain value " + value.toString()
			        + " is not implemented.");
		}
	}

	@Override
	public boolean hasFreeOperands() {
		return (mSubEvaluator == null);
	}

	@Override
	public Set<String> getVarIdentifiers() {
		return mSubEvaluator.getVarIdentifiers();
	}
}
