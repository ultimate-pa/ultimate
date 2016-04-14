/*
 * Copyright (C) 2015-2016 Claus Schaetzle (schaetzc@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2016 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalDomainValue;

public class OctInterval {

	private final OctValue mMin;
	private final OctValue mMax;

	public OctInterval(IntervalDomainValue ivlInterval) {
		if (ivlInterval.isBottom()) {
			mMin = OctValue.ONE;
			mMax = OctValue.ZERO;
		} else {
			mMin = new OctValue(ivlInterval.getLower());
			mMax = new OctValue(ivlInterval.getUpper());
		}
	}

	public OctInterval(OctValue min, OctValue max) {
		mMin = min;
		mMax = max;
	}

	public static OctInterval fromMatrix(OctMatrix m, int variableIndex) {
		int i2 = variableIndex * 2;
		int i21 = i2 + 1;
		return new OctInterval(m.get(i2, i21).half().negateIfNotInfinity(), m.get(i21, i2).half());
	}

	public OctInterval() {
		mMin = mMax = OctValue.INFINITY;
	}

	public IntervalDomainValue toIvlInterval() {
		if (isBottom()) {
			return new IntervalDomainValue(true);
		}
		return new IntervalDomainValue(mMin.toIvlValue(), mMax.toIvlValue());
	}

	public OctValue getMin() {
		return mMin;
	}

	public OctValue getMax() {
		return mMax;
	}
	
	public boolean isBottom() {
		if (mMin.isInfinity()) { // [-inf, inf] is represeted as [inf, inf]
			return false;
		}
		return mMin.compareTo(mMax) > 0;
	}
	
	public boolean isTop() {
		return mMin.isInfinity() && mMax.isInfinity();
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append('[');
		if (mMin.isInfinity()) {
			sb.append('-');
		}
		sb.append(mMin).append("; ").append(mMax).append(']');
		return sb.toString();
	}
}
