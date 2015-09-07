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

import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.ILogicalEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.sign.SignDomainValue.Values;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Represents a boolean expression in the {@link SignDomain}. This requires the program to be analyzed to contain the
 * literals "True" or "False". If "True" is read, the value of {@link this} is <code>true</code>, otherwise
 * <code>false</code>.
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public class SignLogicalSingletonValueExpressionEvaluator extends SignSingletonValueExpressionEvaluator<Boolean>
        implements ILogicalEvaluator<Values, CodeBlock, BoogieVar> {

	public SignLogicalSingletonValueExpressionEvaluator(String value) {
		super(value);
	}

	@Override
	public void setOperator(Object operator) {
		throw new UnsupportedOperationException("Setting the operator for this kind of expression is not permitted.");
	}

	@Override
	public IEvaluationResult<Values> evaluate(IAbstractState<CodeBlock, BoogieVar> currentState) {
		if (mValue) {
			return new SignDomainValue(Values.POSITIVE);
		} else {
			return new SignDomainValue(Values.NEGATIVE);
		}
	}

	@Override
	public IAbstractState<CodeBlock, BoogieVar> logicallyInterpret(IAbstractState<CodeBlock, BoogieVar> currentState) {
		return currentState;
	}

	@Override
	protected Boolean instantiate(String value) {
		Boolean bool = new Boolean(value);

		return bool;
	}

	@Override
	protected int getSignum() {
		return 0;
	}

	@Override
    public boolean logicalEvaluation(IAbstractState<CodeBlock, BoogieVar> currentState) {
	    // TODO Think about if this is right here.
	    return false;
    }

}
