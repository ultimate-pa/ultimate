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

import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.boogie.type.ArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.type.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.valuedomain.BooleanValue;

/**
 * The merge operator for the interval domain.
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 * @param <ACTION>
 *            Any action type.
 * @param <VARDECL>
 *            Any variable declaration type.
 */
public class IntervalMergeOperator<ACTION, VARDECL> implements IAbstractStateBinaryOperator<ACTION, VARDECL> {

	private final IntervalStateConverter<ACTION, VARDECL> mStateConverter;

	protected IntervalMergeOperator(IntervalStateConverter<ACTION, VARDECL> stateConverter) {
		mStateConverter = stateConverter;
	}

	/**
	 * Merges two {@link IntervalState}s, first and second, into one new abstract state. All variables that occur in
	 * first must also occur in second.
	 */
	@SuppressWarnings("unchecked")
	@Override
	public IAbstractState<ACTION, VARDECL> apply(IAbstractState<ACTION, VARDECL> first,
	        IAbstractState<ACTION, VARDECL> second) {
		assert first != null;
		assert second != null;

		final IntervalDomainState firstState = mStateConverter.getCheckedState(first);
		final IntervalDomainState secondState = mStateConverter.getCheckedState(second);

		if (!firstState.hasSameVariables(secondState)) {
			throw new UnsupportedOperationException(
			        "Cannot merge the two states as their sets of variables in the states are disjoint.");
		}

		final IntervalDomainState newState = (IntervalDomainState) first.copy();

		final Map<String, IBoogieVar> variables = firstState.getVariables();
		final Map<String, IntervalDomainValue> firstValues = firstState.getValues();
		final Map<String, BooleanValue> firstBoolValues = firstState.getBooleanValues();
		final Map<String, IntervalDomainValue> secondValues = secondState.getValues();
		final Map<String, BooleanValue> secondBoolValues = secondState.getBooleanValues();

		for (final Entry<String, IBoogieVar> entry : variables.entrySet()) {

			if (entry.getValue().getIType() instanceof PrimitiveType) {

				final PrimitiveType primitiveType = (PrimitiveType) entry.getValue().getIType();
				if (primitiveType.getTypeCode() == PrimitiveType.BOOL) {
					final BooleanValue value1 = firstBoolValues.get(entry.getKey());
					final BooleanValue value2 = secondBoolValues.get(entry.getKey());

					newState.setBooleanValue(entry.getKey(), value1.merge(value2));
				} else {
					final IntervalDomainValue value1 = firstValues.get(entry.getKey());
					final IntervalDomainValue value2 = secondValues.get(entry.getKey());

					newState.setValue(entry.getKey(), value1.merge(value2));
				}
			} else if (entry.getValue().getIType() instanceof ArrayType) {
				// TODO:
				// Implement better handling of arrays.
				final IntervalDomainValue value1 = firstValues.get(entry.getKey());
				final IntervalDomainValue value2 = secondValues.get(entry.getKey());

				newState.setValue(entry.getKey(), value1.merge(value2));
			} else {
				final IntervalDomainValue value1 = firstValues.get(entry.getKey());
				final IntervalDomainValue value2 = secondValues.get(entry.getKey());

				newState.setValue(entry.getKey(), value1.merge(value2));
			}
		}

		return (IAbstractState<ACTION, VARDECL>) newState;
	}
}
