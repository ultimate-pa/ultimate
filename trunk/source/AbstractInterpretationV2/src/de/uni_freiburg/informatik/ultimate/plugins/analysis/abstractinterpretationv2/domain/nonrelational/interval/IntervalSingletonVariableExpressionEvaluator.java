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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.type.ArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.type.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue.Value;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Class to represent the logical evaluator for singleton variable expressions in the {@link IntervalDomain}.
 * 
 * @author Marius Greitschus <greitsch@informatik.uni-freiburg.de>
 *
 */
public class IntervalSingletonVariableExpressionEvaluator
        implements IEvaluator<IntervalDomainValue, IntervalDomainState, CodeBlock, IBoogieVar> {

	private final Set<String> mVariableSet;
	private final String mVariableName;

	private boolean mContainsBoolean = false;

	public IntervalSingletonVariableExpressionEvaluator(final String variableName) {
		mVariableName = variableName;
		mVariableSet = new HashSet<>();
		mVariableSet.add(variableName);
	}

	@Override
	public List<IEvaluationResult<IntervalDomainValue>> evaluate(final IntervalDomainState currentState) {

		final List<IEvaluationResult<IntervalDomainValue>> returnList = new ArrayList<>();

		IntervalDomainValue val;
		BooleanValue returnBool = new BooleanValue();

		final IBoogieVar type = currentState.getVariableDeclarationType(mVariableName);
		if (type.getIType() instanceof PrimitiveType) {
			final PrimitiveType primitiveType = (PrimitiveType) type.getIType();

			if (primitiveType.getTypeCode() == PrimitiveType.BOOL) {
				val = new IntervalDomainValue();
				returnBool = currentState.getBooleanValue(mVariableName);
				mContainsBoolean = true;
			} else {
				val = currentState.getValue(mVariableName);

				assert val != null : "The variable with name " + mVariableName
				        + " has not been found in the current abstract state.";
			}
		} else if (type.getIType() instanceof ArrayType) {
			// TODO: Implement better handling of arrays.
			val = currentState.getValue(mVariableName);
		} else {
			val = currentState.getValue(mVariableName);
		}

		if (val.isBottom() || returnBool.isBottom()) {
			returnList.add(
			        new IntervalDomainEvaluationResult(new IntervalDomainValue(true), new BooleanValue(Value.BOTTOM)));
		} else {
			returnList.add(new IntervalDomainEvaluationResult(val, returnBool));
		}

		return returnList;

	}

	@Override
	public boolean containsBool() {
		return mContainsBoolean;
	}

	@Override
	public void addSubEvaluator(
	        final IEvaluator<IntervalDomainValue, IntervalDomainState, CodeBlock, IBoogieVar> evaluator) {
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

	@Override
	public String toString() {
		return mVariableName;
	}

	@Override
	public List<IntervalDomainState> inverseEvaluate(final IEvaluationResult<IntervalDomainValue> computedValue,
	        final IntervalDomainState currentState) {
		final List<IntervalDomainState> returnList = new ArrayList<>();

		if (mContainsBoolean) {
			returnList.add(currentState.setBooleanValue(mVariableName, computedValue.getBooleanValue()));
		} else {
			returnList.add(currentState.setValue(mVariableName, computedValue.getValue()));
		}

		return returnList;
	}
}
