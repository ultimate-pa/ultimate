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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.sign;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.evaluator.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.evaluator.IEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.sign.SignDomainValue.Values;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Represents an expression that consists of a single variable in the {@link SignDomain}.
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class SignSingletonVariableExpressionEvaluator implements IEvaluator<Values, CodeBlock, BoogieVar> {

	protected String mVariableName;
	protected final SignStateConverter<CodeBlock, BoogieVar> mStateConverter;
	private final Set<String> mVariableSet;

	/**
	 * Constructor that creates a singleton variable expression evaluator in the sign domain.
	 * 
	 * @param variableName
	 *            The name of the variable.
	 * @param stateConverter
	 *            The interval domain state converter.
	 */
	public SignSingletonVariableExpressionEvaluator(String variableName,
	        SignStateConverter<CodeBlock, BoogieVar> stateConverter) {
		mVariableName = variableName;
		mStateConverter = stateConverter;
		mVariableSet = new HashSet<String>();
	}

	@Override
	public final void addSubEvaluator(IEvaluator<Values, CodeBlock, BoogieVar> evaluator) {
		throw new UnsupportedOperationException("A sub evaluator cannot be added to a singleton expression type.");
	}

	@Override
	public final boolean hasFreeOperands() {
		return false;
	}

	@Override
	public final IEvaluationResult<Values> evaluate(IAbstractState<CodeBlock, BoogieVar> currentState) {
		final SignDomainState<CodeBlock, BoogieVar> concreteState = mStateConverter.getCheckedState(currentState);

		final SignDomainValue val = concreteState.getValues().get(mVariableName);

		if (val == null) {
			throw new UnsupportedOperationException("The variable with name " + mVariableName
			        + " has not been found in the current abstract state.");
		}

		return new SignDomainValue(val.getResult());
	}

	@Override
	public Set<String> getVarIdentifiers() {
		return mVariableSet;
	}
}
