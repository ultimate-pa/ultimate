package de.uni_freiburg.informatik.ultimate.lib.srparse.pattern;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;

public class BndExistencePattern extends PatternType {
	@Override
	public void transform() {
		final CDD p_cdd = mCdds.get(0);
		final CDD q_cdd = mScope.getCdd1();
		final CDD r_cdd = mScope.getCdd2();

		mPea = mPeaTransformator.bndExistencePattern(mId, p_cdd, q_cdd, r_cdd, mScope.toString());
	}

	@Override
	public String toString() {
		String res = new String();
		res = "transitions to states in which \"" + mCdds.get(0) + "\" holds occur at most twice";
		return res;
	}
}
