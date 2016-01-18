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

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.List;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.boogie.type.ArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.type.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.LiteralCollection;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.LiteralCollector;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue.Value;

/**
 * Implementation of a widening operator in the interval domain which widens according to number literals occurring in
 * the program.
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class IntervalLiteralWideningOperator implements IAbstractStateBinaryOperator<IntervalDomainState> {

	private final LiteralCollection mLiteralCollection;

	protected IntervalLiteralWideningOperator(LiteralCollector literalCollector) {
		mLiteralCollection = literalCollector.getLiteralCollection();
	}

	@Override
	public IntervalDomainState apply(IntervalDomainState first, IntervalDomainState second) {
		assert first.hasSameVariables(second);
		assert !first.isBottom() && !second.isBottom();

		final List<String> boolsToWiden = new ArrayList<>();
		final List<BooleanValue.Value> boolValues = new ArrayList<>();
		final List<String> varsToWiden = new ArrayList<>();
		final List<IntervalDomainValue> varValues = new ArrayList<>();
		final List<String> arraysToWiden = new ArrayList<>();
		final List<IntervalDomainValue> arrayValues = new ArrayList<>();

		for (Entry<String, IBoogieVar> entry : first.getVariables().entrySet()) {
			final String var = entry.getKey();
			final IBoogieVar type = entry.getValue();

			if (type.getIType() instanceof PrimitiveType) {
				final PrimitiveType primitiveType = (PrimitiveType) type.getIType();

				if (primitiveType.getTypeCode() == PrimitiveType.BOOL) {
					final BooleanValue firstValue = first.getBooleanValue(var);
					final BooleanValue secondValue = second.getBooleanValue(var);

					if (!firstValue.isEqualTo(secondValue)) {
						boolsToWiden.add(var);
						// Bools are always set to top.
						boolValues.add(Value.TOP);
					}
				} else {
					final IntervalDomainValue firstValue = first.getValue(var);
					final IntervalDomainValue secondValue = second.getValue(var);

					if (!firstValue.isEqualTo(secondValue)) {
						varsToWiden.add(var);
						varValues.add(determineNextValue(firstValue, secondValue));
					}
				}
			} else if (type.getIType() instanceof ArrayType) {
				// TODO: We treat arrays as normal variables for the time being.
				final IntervalDomainValue firstValue = first.getValue(var);
				final IntervalDomainValue secondValue = second.getValue(var);

				if (!firstValue.isEqualTo(secondValue)) {
					arraysToWiden.add(var);
					arrayValues.add(determineNextValue(firstValue, secondValue));
				}
			} else {
				final IntervalDomainValue firstValue = first.getValue(var);
				final IntervalDomainValue secondValue = second.getValue(var);

				if (!firstValue.isEqualTo(secondValue)) {
					varsToWiden.add(var);
					varValues.add(determineNextValue(firstValue, secondValue));
				}
			}
		}

		final String[] vars = varsToWiden.toArray(new String[varsToWiden.size()]);
		final IntervalDomainValue[] vals = varValues.toArray(new IntervalDomainValue[varValues.size()]);
		final String[] bools = boolsToWiden.toArray(new String[boolsToWiden.size()]);
		final BooleanValue.Value[] boolVals = boolValues.toArray(new BooleanValue.Value[boolValues.size()]);
		final String[] arrays = arraysToWiden.toArray(new String[arraysToWiden.size()]);
		final IntervalDomainValue[] arrayVals = arrayValues.toArray(new IntervalDomainValue[arrayValues.size()]);

		return first.setMixedValues(vars, vals, bools, boolVals, arrays, arrayVals);
	}

	private IntervalDomainValue determineNextValue(IntervalDomainValue first, IntervalDomainValue second) {
		final IntervalValue firstLower = first.getLower();
		final IntervalValue firstUpper = first.getUpper();

		final IntervalValue secondLower = second.getLower();
		final IntervalValue secondUpper = second.getUpper();

		IntervalValue newLower;
		IntervalValue newUpper;

		// Compute new lower
		if (firstLower.isInfinity() || secondLower.isInfinity()) {
			newLower = new IntervalValue();
		} else {
			// If the lower bound has changed, we need to widen the lower bound, starting from the lower value. If the
			// lower bounds are the same, we use this value as current bound.
			if (firstLower.compareTo(secondLower) < 0) {
				newLower = new IntervalValue(mLiteralCollection.getNextRealNegative(firstLower.getValue()));
			} else if (firstLower.compareTo(secondLower) > 0) {
				newLower = new IntervalValue(mLiteralCollection.getNextIntegerNegative(secondLower.getValue()));
			} else {
				newLower = new IntervalValue(firstLower.getValue());
			}
		}

		// Compute new upper
		if (firstUpper.isInfinity() || secondUpper.isInfinity()) {
			newUpper = new IntervalValue();
		} else {
			// If the upper bound has changed, we need to widen the upper bound, starting from the largest value. If the
			// upper bounds are the same, we use this value as current bound.
			if (firstUpper.compareTo(secondUpper) > 0) {
				newUpper = new IntervalValue(mLiteralCollection.getNextRealPositive(firstUpper.getValue()));
			} else if (firstUpper.compareTo(secondUpper) < 0) {
				newUpper = new IntervalValue(mLiteralCollection.getNextRealPositive(secondUpper.getValue()));
			} else {
				newUpper = new IntervalValue(firstUpper.getValue());
			}
		}

		return new IntervalDomainValue(newLower, newUpper);
	}
}
