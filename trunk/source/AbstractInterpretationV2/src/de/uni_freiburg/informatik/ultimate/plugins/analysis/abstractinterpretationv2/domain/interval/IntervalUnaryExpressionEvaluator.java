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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.interval;

import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.evaluator.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.evaluator.IEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.evaluator.INAryEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Expression evaluator for unary expressions in the interval domain.
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class IntervalUnaryExpressionEvaluator implements INAryEvaluator<IntervalDomainValue, CodeBlock, BoogieVar> {

	private final static int BUFFER_MAX = 100;

	private final Logger mLogger;

	protected IEvaluator<IntervalDomainValue, CodeBlock, BoogieVar> mSubEvaluator;
	protected UnaryExpression.Operator mOperator;

	public IntervalUnaryExpressionEvaluator(Logger logger) {
		mLogger = logger;
	}

	@Override
	public IEvaluationResult<IntervalDomainValue> evaluate(IAbstractState<CodeBlock, BoogieVar> currentState) {

		IEvaluator<IntervalDomainValue, CodeBlock, BoogieVar> castedSubEvaluator = (IEvaluator<IntervalDomainValue, CodeBlock, BoogieVar>) mSubEvaluator;

		@SuppressWarnings("unchecked")
		final IEvaluationResult<IntervalDomainValue> subEvaluatorResult = (IEvaluationResult<IntervalDomainValue>) castedSubEvaluator;

		switch (mOperator) {
		case ARITHNEGATIVE:
			return subEvaluatorResult.getResult().negate();
		case LOGICNEG:
			mLogger.warn("Operator application: Logic Negation. Possible loss of precision. Returning Top.");
			return new IntervalDomainValue();
		default:
			StringBuilder stringBuilder = new StringBuilder(BUFFER_MAX);
			stringBuilder.append("The operator ").append(mOperator).append(" is not implemented.");
			throw new UnsupportedOperationException(stringBuilder.toString());

		}
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

	@Override
	public int getArity() {
		return 1;
	}

}
