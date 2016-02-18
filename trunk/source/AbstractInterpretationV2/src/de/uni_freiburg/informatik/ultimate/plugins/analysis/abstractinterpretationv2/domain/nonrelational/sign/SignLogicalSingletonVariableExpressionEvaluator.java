/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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

import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.sign.SignDomainValue.Values;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public class SignLogicalSingletonVariableExpressionEvaluator extends SignSingletonVariableExpressionEvaluator
        implements IEvaluator<Values, SignDomainState, CodeBlock, IBoogieVar> {

	private BooleanValue mBooleanValue;

	public SignLogicalSingletonVariableExpressionEvaluator(String variableName) {
		super(variableName);
	}

	private SignDomainState logicallyInterpret(SignDomainState currentState) {
		assert currentState.containsVariable(mVariableName);

		final IBoogieVar var = currentState.getVariables().get(mVariableName);

		final BoogieType varType = (BoogieType) var.getIType();

		// TODO: Check type for bool. How to do that?

		final SignDomainValue value = currentState.getValues().get(mVariableName);

		SignDomainState newState = currentState.copy();

		return newState;
	}

	protected final SignDomainValue getBooleanValue(SignDomainState currentState) {

		assert currentState.containsVariable(mVariableName);

		final SignDomainValue value = currentState.getValues().get(mVariableName);

		SignDomainValue newValue;

		switch (value.getValue()) {
		case NEGATIVE:
			return new SignDomainValue(Values.NEGATIVE);
		case POSITIVE:
			return new SignDomainValue(Values.POSITIVE);
		case BOTTOM:
			return new SignDomainValue(Values.BOTTOM);
		default:
			throw new UnsupportedOperationException(
			        "The value " + value.getValue().toString() + " is no valid boolean sign domain value.");
		}
	}

	private boolean logicalEvaluation(SignDomainState currentState) {

		assert currentState.containsVariable(mVariableName);

		final SignDomainValue value = currentState.getValues().get(mVariableName);

		SignDomainValue newValue;

		switch (value.getValue()) {
		case NEGATIVE:
			return false;
		case POSITIVE:
			return true;
		case BOTTOM:
			return false;
		default:
			throw new UnsupportedOperationException(
			        "The value " + value.getValue().toString() + " is no valid boolean sign domain value.");
		}
	}

	@Override
	public boolean containsBool() {
		// TODO Auto-generated method stub
		return false;
	}

}
