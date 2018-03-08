package de.uni_freiburg.informatik.ultimate.lib.srparse.pattern;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;

public class BndReccurrencePattern extends PatternType {
	@Override
	public void transform(final Map<String, Integer> id2bounds) {
		final CDD p_cdd = mCdds.get(0);
		final CDD q_cdd = mScope.getCdd1();
		final CDD r_cdd = mScope.getCdd2();

		mPea = mPeaTransformator.periodicPattern(mId, p_cdd, q_cdd, r_cdd, parseDuration(getDuration(), id2bounds),
				mScope.toString());
	}

	@Override
	public String toString() {
		String res = new String();

		res = "it is always the case that \"" + mCdds.get(0) + "\" holds at least every \"" + mDuration
				+ "\" time units";

		return res;
	}
}
