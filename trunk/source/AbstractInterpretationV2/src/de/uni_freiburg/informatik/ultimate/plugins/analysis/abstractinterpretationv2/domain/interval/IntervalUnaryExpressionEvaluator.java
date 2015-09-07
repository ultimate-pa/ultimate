/*
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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.interval;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.INAryEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Expression evaluator for unary expressions in the interval domain.
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public class IntervalUnaryExpressionEvaluator implements INAryEvaluator<IntervalDomainValue, CodeBlock, BoogieVar> {

	private final static int BUFFER_MAX = 100;

	protected IEvaluator<IntervalDomainValue, CodeBlock, BoogieVar> mSubEvaluator;
	protected UnaryExpression.Operator mOperator;

	@Override
	public IEvaluationResult<IntervalDomainValue> evaluate(IAbstractState<CodeBlock, BoogieVar> currentState) {

		IEvaluator<IntervalDomainValue, CodeBlock, BoogieVar> castedSubEvaluator = (IEvaluator<IntervalDomainValue, CodeBlock, BoogieVar>) mSubEvaluator;

		final IEvaluationResult<IntervalDomainValue> subEvaluatorResult = (IEvaluationResult<IntervalDomainValue>) castedSubEvaluator;

		switch (mOperator) {
		case ARITHNEGATIVE:
			return negateValue(subEvaluatorResult.getResult());
		default:
			StringBuilder stringBuilder = new StringBuilder(BUFFER_MAX);
			stringBuilder.append("The operator ").append(mOperator).append(" is not implemented.");
			throw new UnsupportedOperationException(stringBuilder.toString());

		}
	}

	/**
	 * Negates the given interval.
	 * 
	 * @param interval
	 *            The interval to negate.
	 * @return A new interval which corresponds to the negated input interval.
	 */
	private IEvaluationResult<IntervalDomainValue> negateValue(IntervalDomainValue interval) {

		if (interval.isBottom()) {
			return new IntervalDomainValue(true);
		}

		if (interval.getLower().isInfinity() && interval.getUpper().isInfinity()) {
			return new IntervalDomainValue();
		}

		if (interval.getLower().isInfinity()) {
			return new IntervalDomainValue(new IntervalValue(interval.getUpper().getValue().negate()),
			        new IntervalValue());
		}

		if (interval.getUpper().isInfinity()) {
			return new IntervalDomainValue(new IntervalValue(), new IntervalValue(interval.getLower().getValue()
			        .negate()));
		}

		return new IntervalDomainValue(new IntervalValue(interval.getUpper().getValue().negate()), new IntervalValue(
		        interval.getLower().getValue().negate()));
	}

	@Override
	public void addSubEvaluator(IEvaluator<IntervalDomainValue, CodeBlock, BoogieVar> evaluator) {
		assert mSubEvaluator == null;
		assert evaluator != null;

		mSubEvaluator = evaluator;
	}

	@Override
	public Set<String> getVarIdentifiers() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean hasFreeOperands() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public void setOperator(Object operator) {
		assert operator != null;
		assert operator instanceof Operator;
		mOperator = (Operator) operator;
	}

}
