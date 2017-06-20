package de.uni_freiburg.informatik.ultimate.lib.srparse.pattern;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;

public class BndEntryConditionPattern extends PatternType {
	@Override
	public void transform() {
		final CDD p_cdd = cdds.get(1);
		final CDD q_cdd = scope.getCdd1();
		final CDD r_cdd = scope.getCdd2();
		final CDD s_cdd = cdds.get(0);

		pea = peaTransformator.bndEntryConditionPattern(p_cdd, q_cdd, r_cdd, s_cdd, duration, scope.toString());
	}

	@Override
	public String toString() {
		String res = new String();

		res = "it is always the case that after \"" + cdds.get(1) + "\" holds for \"" + duration
				+ "\" time units, then \"" + cdds.get(0) + "\" holds";

		return res;
	}
}
