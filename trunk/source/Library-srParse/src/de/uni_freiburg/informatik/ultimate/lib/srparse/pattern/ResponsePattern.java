package de.uni_freiburg.informatik.ultimate.lib.srparse.pattern;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;

public class ResponsePattern extends PatternType {
	@Override
	public void transform(Map<String, Integer> id2bounds) {
		final CDD p_cdd = mCdds.get(1);
		final CDD q_cdd = mScope.getCdd1();
		final CDD r_cdd = mScope.getCdd2();
		final CDD s_cdd = mCdds.get(0);
		mPea = mPeaTransformator.responsePattern(mId, p_cdd, q_cdd, r_cdd, s_cdd, mScope.toString());
	}

	@Override
	public String toString() {
		String res = new String();

		res = "it is always the case that if \"" + mCdds.get(1) + "\" holds, then \"" + mCdds.get(0)
				+ "\" eventually holds";

		return res;
	}
}
