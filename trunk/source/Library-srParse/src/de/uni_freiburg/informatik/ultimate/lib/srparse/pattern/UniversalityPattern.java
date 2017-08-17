package de.uni_freiburg.informatik.ultimate.lib.srparse.pattern;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;

public class UniversalityPattern extends PatternType {

	@Override
	public void transform() {
		/*
		 * CDD p_cdd = BooleanDecision.create("ANB_Request_valid = 1"); CDD q_cdd = BooleanDecision.create(
		 * "ANB_Teilbremsung_Freigabe = 1").and( BooleanDecision.create("ANB_info_Teilbremsung = 1") ); CDD r_cdd =
		 * p_cdd;
		 */

		final CDD p_cdd = mCdds.get(0);
		final CDD q_cdd = mScope.getCdd1();
		final CDD r_cdd = mScope.getCdd2();

		mPea = mPeaTransformator.universalityPattern(p_cdd, q_cdd, r_cdd, mScope.toString());
	}

	@Override
	public String toString() {
		String res = new String();

		res = "it is always the case that \"" + mCdds.get(0) + "\" holds";

		return res;
	}
}
