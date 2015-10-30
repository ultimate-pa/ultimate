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

import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.evaluator.ILogicalEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * The logical evaluator for binary expressions in the {@link IntervalDomain}.
 * 
 * @author Marius Greitschus <greitsch@informatik.uni-freiburg.de>
 *
 */
public class IntervalLogicalBinaryExpressionEvaluator extends IntervalBinaryExpressionEvaluator
        implements ILogicalEvaluator<IntervalDomainValue, CodeBlock, BoogieVar> {

	@Override
	public IAbstractState<CodeBlock, BoogieVar> logicallyInterpret(IAbstractState<CodeBlock, BoogieVar> currentState) {
		assert currentState != null;

		final ILogicalEvaluator<IntervalDomainValue, CodeBlock, BoogieVar> left = (ILogicalEvaluator<IntervalDomainValue, CodeBlock, BoogieVar>) mLeftSubEvaluator;
		final ILogicalEvaluator<IntervalDomainValue, CodeBlock, BoogieVar> right = (ILogicalEvaluator<IntervalDomainValue, CodeBlock, BoogieVar>) mRightSubEvaluator;

		final IntervalDomainState<CodeBlock, BoogieVar> leftResult = (IntervalDomainState<CodeBlock, BoogieVar>) left
		        .logicallyInterpret(currentState);
		final IntervalDomainState<CodeBlock, BoogieVar> rightResult = (IntervalDomainState<CodeBlock, BoogieVar>) right
		        .logicallyInterpret(currentState);

		switch (mOperator) {
		case LOGICAND:
			return leftResult.intersect(rightResult);
		case LOGICOR:
			// TODO merge
		default:
			throw new UnsupportedOperationException("The operator " + mOperator + " is not implemented.");
		}
	}

	@Override
	public boolean logicalEvaluation(IAbstractState<CodeBlock, BoogieVar> currentState) {
		// TODO Auto-generated method stub
		return false;
	}

}
