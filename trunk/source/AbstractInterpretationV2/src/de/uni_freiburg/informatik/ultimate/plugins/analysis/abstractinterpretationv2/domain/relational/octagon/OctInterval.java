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

	public static OctInterval fromMatrixEntries(OctValue minNeg2, OctValue max2) {
		return new OctInterval(minNeg2.half().negateIfNotInfinity(), max2.half());
	}

	public static OctInterval fromMatrix(OctMatrix m, int variableIndex) {
		int i2 = variableIndex * 2;
		int i21 = i2 + 1;
		return fromMatrixEntries(m.get(i2, i21), m.get(i21, i2));
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
		// note: [-inf, inf] is represeted as [inf, inf], which is also not empty
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
