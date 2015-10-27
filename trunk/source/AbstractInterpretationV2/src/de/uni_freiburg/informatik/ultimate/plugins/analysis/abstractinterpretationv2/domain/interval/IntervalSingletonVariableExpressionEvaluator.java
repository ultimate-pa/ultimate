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

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.evaluator.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.evaluator.IEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Represents an expression that consists of a single variable in the {@link IntervalDomain}.
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public class IntervalSingletonVariableExpressionEvaluator implements
        IEvaluator<IntervalDomainValue, CodeBlock, BoogieVar> {

	protected String mVariableName;
	protected final IntervalStateConverter<CodeBlock, BoogieVar> mStateConverter;
	private final Set<String> mVariableSet;

	/**
	 * Constructor that creates a singleton variable expression evaluator in the interval domain.
	 * 
	 * @param variableName
	 *            The name of the variable.
	 * @param stateConverter
	 *            The interval domain state converter.
	 */
	public IntervalSingletonVariableExpressionEvaluator(String variableName,
	        IntervalStateConverter<CodeBlock, BoogieVar> stateConverter) {
		mVariableName = variableName;
		mStateConverter = stateConverter;
		mVariableSet = new HashSet<String>();
	}

	@Override
	public IEvaluationResult<IntervalDomainValue> evaluate(IAbstractState<CodeBlock, BoogieVar> currentState) {

		final IntervalDomainState<CodeBlock, BoogieVar> concreteState = mStateConverter.getCheckedState(currentState);

		final IntervalDomainValue val = concreteState.getValues().get(mVariableName);

		if (val == null) {
			throw new UnsupportedOperationException("The variable with name " + mVariableName
			        + " has not been found in the current abstract state.");
		}

		return new IntervalDomainValue(val.getLower(), val.getUpper());
	}

	@Override
	public void addSubEvaluator(IEvaluator<IntervalDomainValue, CodeBlock, BoogieVar> evaluator) {
		throw new UnsupportedOperationException(
		        "A sub evaluator cannot be added to a singleton variable expression evaluator.");
	}

	@Override
	public Set<String> getVarIdentifiers() {
		return mVariableSet;
	}

	@Override
	public boolean hasFreeOperands() {
		return false;
	}

}
