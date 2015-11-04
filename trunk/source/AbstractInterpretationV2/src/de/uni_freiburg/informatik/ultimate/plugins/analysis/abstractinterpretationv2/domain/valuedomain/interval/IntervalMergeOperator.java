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

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractStateBinaryOperator;

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
	@Override
	public IAbstractState<ACTION, VARDECL> apply(IAbstractState<ACTION, VARDECL> first,
	        IAbstractState<ACTION, VARDECL> second) {
		assert first != null;
		assert second != null;

		final IntervalDomainState<ACTION, VARDECL> firstState = mStateConverter.getCheckedState(first);
		final IntervalDomainState<ACTION, VARDECL> secondState = mStateConverter.getCheckedState(second);

		if (!firstState.hasSameVariables(secondState)) {
			throw new UnsupportedOperationException(
			        "Cannot merge the two states as their sets of variables in the states are disjoint.");
		}

		final IntervalDomainState<ACTION, VARDECL> newState = (IntervalDomainState<ACTION, VARDECL>) first.copy();

		final Map<String, VARDECL> variables = firstState.getVariables();
		final Map<String, IntervalDomainValue> firstValues = firstState.getValues();
		final Map<String, IntervalDomainValue> secondValues = secondState.getValues();

		for (final Entry<String, VARDECL> entry : variables.entrySet()) {
			final IntervalDomainValue value1 = firstValues.get(entry.getKey());
			final IntervalDomainValue value2 = secondValues.get(entry.getKey());

			newState.setValue(entry.getKey(), computeMergedValue(value1, value2));
		}

		return newState;
	}

	/**
	 * Computes the merger of two {@link IntervalDomainValue}s.
	 * 
	 * @param value1
	 *            The first Interval.
	 * @param value2
	 *            The second interval.
	 * @return A new interval which is the result of merging the first and the second interval.
	 */
	private IntervalDomainValue computeMergedValue(IntervalDomainValue value1, IntervalDomainValue value2) {
		if (value1.equals(value2)) {
			return value1;
		}

		if (value1.isBottom() || value2.isBottom()) {
			return new IntervalDomainValue(true);
		}

		IntervalValue lower;
		IntervalValue upper;

		if (value1.getLower().isInfinity() || value2.getLower().isInfinity()) {
			lower = new IntervalValue();
		} else {
			if (value1.getLower().compareTo(value2.getLower()) < 0) {
				lower = new IntervalValue(value1.getLower().getValue());
			} else {
				lower = new IntervalValue(value2.getLower().getValue());
			}
		}

		if (value1.getUpper().isInfinity() || value2.getUpper().isInfinity()) {
			upper = new IntervalValue();
		} else {
			if (value1.getUpper().compareTo(value2.getUpper()) < 0) {
				upper = new IntervalValue(value1.getUpper().getValue());
			} else {
				upper = new IntervalValue(value2.getUpper().getValue());
			}
		}

		return new IntervalDomainValue(lower, upper);
	}

}
