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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.sign;

import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.sign.SignDomainValue.Values;

/**
 * The implementation of a simple merge operator on the sign domain. This operator can also be used as widening
 * operator.
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 * @param <ACTION>
 *            Any action.
 * @param <IBoogieVar>
 *            Any variable declaration.
 */
public class SignMergeOperator implements IAbstractStateBinaryOperator<SignDomainState> {

	private static final int BUFFER_SIZE = 100;

	protected SignMergeOperator() {
	}

	/**
	 * Merges two abstract states, first and second, into one new abstract state. All variables that occur in first must
	 * also occur in second.<br />
	 * 
	 * <p>
	 * Assume, there is a variable with name "v". The value of "v" in first is v1 and the value of "v" in second is v2.
	 * <br />
	 * </p>
	 * 
	 * <p>
	 * It is distinguished between four cases for the resulting merged value of "v":<br />
	 * <ol>
	 * <li>v1 is equal to v2:<br />
	 * The resulting value will be v1.</li>
	 * <li>v1 is positive (negative) and v2 is negative (positive):<br />
	 * The resulting value will be \top.</li>
	 * <li>v1 is not 0 (is 0) and v2 is 0 (is not 0):<br />
	 * The resulting value will be \top.</li>
	 * <li>v1 is \bot or v2 is \bot:<br />
	 * The resulting value will be \bot.</li>
	 * </ol>
	 * </p>
	 * 
	 * @param first
	 *            The first state to merge.
	 * @param second
	 *            The second state to merge.
	 */
	@Override
	public SignDomainState apply(SignDomainState first,
			SignDomainState second) {
		assert first != null;
		assert second != null;

		if (!first.hasSameVariables(second)) {
			throw new UnsupportedOperationException("Cannot merge two states with a disjoint set of variables.");
		}

		final SignDomainState newState = (SignDomainState) first.copy();

		final Map<String, IBoogieVar> variables = first.getVariables();
		final Map<String, SignDomainValue> firstValues = first.getValues();
		final Map<String, SignDomainValue> secondValues = second.getValues();

		for (final Entry<String, IBoogieVar> entry : variables.entrySet()) {
			final SignDomainValue value1 = firstValues.get(entry.getKey());
			final SignDomainValue value2 = secondValues.get(entry.getKey());

			newState.setValue(entry.getKey(), computeMergedValue(value1, value2));
		}

		return newState;
	}

	/**
	 * Computes the merging of two {@link SignDomainValue}s. {@link SignDomainValue}s.
	 * 
	 * @param value1
	 *            The first value.
	 * @param value2
	 *            The second value.
	 * @return Returns a new {@link SignDomainValue}.
	 */
	private SignDomainValue computeMergedValue(SignDomainValue value1, SignDomainValue value2) {
		if (value1.getResult() == value2.getResult()) {
			return new SignDomainValue(value1.getResult());
		}

		if (value1.getResult() == Values.BOTTOM || value2.getResult() == Values.BOTTOM) {
			return new SignDomainValue(Values.BOTTOM);
		}

		if ((value1.getResult() == Values.POSITIVE && value2.getResult() == Values.NEGATIVE)
				|| (value1.getResult() == Values.NEGATIVE && value2.getResult() == Values.POSITIVE)) {
			return new SignDomainValue(Values.TOP);
		}

		if (value1.getResult() == Values.ZERO || value2.getResult() == Values.ZERO) {
			return new SignDomainValue(Values.TOP);
		}

		final StringBuilder stringBuilder = new StringBuilder(BUFFER_SIZE);

		stringBuilder.append("Unable to handle value1 = ").append(value1.getResult()).append(" and value2 = ")
				.append(value2.getResult()).append('.');

		throw new UnsupportedOperationException(stringBuilder.toString());
	}

}
