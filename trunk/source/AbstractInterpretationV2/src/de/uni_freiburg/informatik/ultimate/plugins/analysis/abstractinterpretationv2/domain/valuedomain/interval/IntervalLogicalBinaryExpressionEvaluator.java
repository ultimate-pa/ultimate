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

import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.evaluator.EvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.evaluator.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.evaluator.ILogicalEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public class IntervalLogicalBinaryExpressionEvaluator extends IntervalBinaryExpressionEvaluator implements
        ILogicalEvaluator<EvaluationResult<IntervalDomainValue, CodeBlock, BoogieVar>, CodeBlock, BoogieVar> {

	private boolean mBooleanValue;

	protected IntervalLogicalBinaryExpressionEvaluator(Logger logger) {
		super(logger);
	}

	@Override
	public IEvaluationResult<EvaluationResult<IntervalDomainValue, CodeBlock, BoogieVar>> evaluate(
	        IAbstractState<CodeBlock, BoogieVar> currentState) {

		final IEvaluationResult<EvaluationResult<IntervalDomainValue, CodeBlock, BoogieVar>> evaluationResult = super.evaluate(
		        currentState);

		ILogicalEvaluator<EvaluationResult<IntervalDomainValue, CodeBlock, BoogieVar>, CodeBlock, BoogieVar> logicLeft = (ILogicalEvaluator<EvaluationResult<IntervalDomainValue, CodeBlock, BoogieVar>, CodeBlock, BoogieVar>) mLeftSubEvaluator;
		ILogicalEvaluator<EvaluationResult<IntervalDomainValue, CodeBlock, BoogieVar>, CodeBlock, BoogieVar> logicRight = (ILogicalEvaluator<EvaluationResult<IntervalDomainValue, CodeBlock, BoogieVar>, CodeBlock, BoogieVar>) mRightSubEvaluator;

		switch (mOperator) {
		case LOGICAND:
			mBooleanValue = logicLeft.booleanValue() && logicRight.booleanValue();
			break;
		case LOGICOR:
			mBooleanValue = logicLeft.booleanValue() || logicRight.booleanValue();
			break;
		case LOGICIMPLIES:
			mBooleanValue = !logicLeft.booleanValue() || logicRight.booleanValue();
			break;
		case LOGICIFF:
			mBooleanValue = (logicLeft.booleanValue() && logicRight.booleanValue())
			        || (!logicLeft.booleanValue() && !logicRight.booleanValue());
		case COMPEQ:
		case COMPGEQ:
		case COMPGT:
		case COMPLEQ:
		case COMPLT:
		case COMPNEQ:
		case COMPPO:
			mLogger.warn("Operator " + mOperator + " not handled.");
		default:
			mBooleanValue = false;
		}

		return evaluationResult;
	}

	@Override
	public boolean booleanValue() {
		return mBooleanValue;
	}
}
