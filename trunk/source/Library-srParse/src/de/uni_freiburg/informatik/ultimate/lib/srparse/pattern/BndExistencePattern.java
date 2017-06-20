package de.uni_freiburg.informatik.ultimate.lib.srparse.pattern;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;

public class BndExistencePattern extends PatternType {
	@Override
	public void transform() {
		final CDD p_cdd = cdds.get(0);
		final CDD q_cdd = scope.getCdd1();
		final CDD r_cdd = scope.getCdd2();

		pea = peaTransformator.bndExistencePattern(p_cdd, q_cdd, r_cdd, scope.toString());
	}

	@Override
	public String toString() {
		String res = new String();
		res = "transitions to states in which \"" + cdds.get(0) + "\" holds occur at most twice";
		return res;
	}
}
