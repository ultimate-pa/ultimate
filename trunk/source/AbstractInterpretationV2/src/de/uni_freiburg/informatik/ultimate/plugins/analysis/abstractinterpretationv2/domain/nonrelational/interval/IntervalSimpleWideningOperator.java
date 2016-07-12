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
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.boogie.type.ArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.type.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue;

/**
 * Implementation of a simple widening operator that just returns a new interval of the form (-&infin; ; &infin;).
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class IntervalSimpleWideningOperator implements IAbstractStateBinaryOperator<IntervalDomainState> {

	@Override
	public IntervalDomainState apply(final IntervalDomainState first, final IntervalDomainState second) {
		assert first.hasSameVariables(second);
		assert !first.isBottom() && !second.isBottom();

		final List<IBoogieVar> boolsToTop = new ArrayList<>();
		final List<IBoogieVar> varsToTop = new ArrayList<>();
		final List<IBoogieVar> arraysToTop = new ArrayList<>();

		for (final IBoogieVar var : first.getVariables()) {
			if (var.getIType() instanceof PrimitiveType) {
				final PrimitiveType primitiveType = (PrimitiveType) var.getIType();

				if (primitiveType.getTypeCode() == PrimitiveType.BOOL) {
					final BooleanValue firstBool = first.getBooleanValue(var);
					final BooleanValue secondBool = second.getBooleanValue(var);
					if (!firstBool.isEqualTo(secondBool)) {
						boolsToTop.add(var);
					}
				} else {
					final IntervalDomainValue firstValue = first.getValue(var);
					final IntervalDomainValue secondValue = second.getValue(var);

					if (!firstValue.isEqualTo(secondValue)) {
						varsToTop.add(var);
					}
				}
			} else if (var.getIType() instanceof ArrayType) {
				// TODO:
				// We treat Arrays as normal variables for the time being.
				final IntervalDomainValue firstValue = first.getValue(var);
				final IntervalDomainValue secondValue = second.getValue(var);

				if (!firstValue.isEqualTo(secondValue)) {
					arraysToTop.add(var);
				}
			} else {
				final IntervalDomainValue firstValue = first.getValue(var);
				final IntervalDomainValue secondValue = second.getValue(var);

				if (!firstValue.isEqualTo(secondValue)) {
					varsToTop.add(var);
				}
			}
		}

		return first.setVarsToTop(varsToTop, boolsToTop, arraysToTop);
	}
}
