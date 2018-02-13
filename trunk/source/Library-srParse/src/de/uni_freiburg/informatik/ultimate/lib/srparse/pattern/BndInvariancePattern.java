package de.uni_freiburg.informatik.ultimate.lib.srparse.pattern;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;

public class BndInvariancePattern extends PatternType {
	@Override
	public void transform() {
		final CDD p_cdd = mCdds.get(1);
		final CDD q_cdd = mScope.getCdd1();
		final CDD r_cdd = mScope.getCdd2();
		final CDD s_cdd = mCdds.get(0);

		mPea = mPeaTransformator.bndInvariancePattern(mId, p_cdd, q_cdd, r_cdd, s_cdd, mDuration, mScope.toString());
	}

	@Override
	public String toString() {
		String res = new String();

		res = "it is always the case that if \"" + mCdds.get(1) + "\" holds, then \"" + mCdds.get(0)
				+ "\" holds for at least \"" + mDuration + "\" time units";

		return res;
	}
}
