package de.uni_freiburg.informatik.ultimate.lib.srparse;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;

public abstract class SrParseScope {

	private final CDD mCdd1;
	private final CDD mCdd2;

	protected SrParseScope(final CDD cdd1, final CDD cdd2) {
		mCdd1 = cdd1;
		mCdd2 = cdd2;
	}

	public CDD getCdd1() {
		return mCdd1;
	}

	public CDD getCdd2() {
		return mCdd2;
	}

	@Override
	public abstract String toString();
}
