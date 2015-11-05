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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.interval;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.evaluator.EvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.evaluator.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.evaluator.ILogicalEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Class that handles unary logical expression evaluators in the {@link IntervalDomain}.
 * 
 * @author Marius Greitschus <greitsch@informatik.uni-freiburg.de>
 *
 */
public class IntervalLogicalUnaryExpressionEvaluator extends IntervalUnaryExpressionEvaluator implements
        ILogicalEvaluator<EvaluationResult<IntervalDomainValue, CodeBlock, IBoogieVar>, CodeBlock, IBoogieVar> {

	private BooleanValue mBooleanValue;

	protected IntervalLogicalUnaryExpressionEvaluator(Logger logger) {
		super(logger);
	}

	@Override
	public IEvaluationResult<EvaluationResult<IntervalDomainValue, CodeBlock, IBoogieVar>> evaluate(
	        IAbstractState<CodeBlock, IBoogieVar> currentState) {

		final IEvaluationResult<EvaluationResult<IntervalDomainValue, CodeBlock, IBoogieVar>> evaluated = super.evaluate(
		        currentState);

		ILogicalEvaluator<EvaluationResult<IntervalDomainValue, CodeBlock, IBoogieVar>, CodeBlock, IBoogieVar> boolSubEvaluator = (ILogicalEvaluator<EvaluationResult<IntervalDomainValue, CodeBlock, IBoogieVar>, CodeBlock, IBoogieVar>) mSubEvaluator;

		switch (mOperator) {
		case LOGICNEG:
			mBooleanValue = boolSubEvaluator.booleanValue().neg();
			break;
		default:
			mLogger.warn("Operator " + mOperator + " not implemented. Assuming logical interpretation to be false.");
			mBooleanValue = new BooleanValue(false);
			return new EvaluationResult<IntervalDomainValue, CodeBlock, IBoogieVar>(new IntervalDomainValue(),
			        currentState);
		}

		return evaluated;
	}

	@Override
	public BooleanValue booleanValue() {
		return mBooleanValue;
	}

	@Override
	public boolean containsBool() {
		final ILogicalEvaluator<EvaluationResult<IntervalDomainValue, CodeBlock, IBoogieVar>, CodeBlock, IBoogieVar> logicSub = (ILogicalEvaluator<EvaluationResult<IntervalDomainValue, CodeBlock, IBoogieVar>, CodeBlock, IBoogieVar>) mSubEvaluator;
		return logicSub.containsBool();
	}

}
