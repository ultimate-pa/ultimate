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
}
