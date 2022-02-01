package de.uni_freiburg.informatik.ultimate.lib.srparse;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;

public class SrParseScopeAfter extends SrParseScope<SrParseScopeAfter> {

	public SrParseScopeAfter(final CDD cdd1) {
		super(cdd1, null);
	}

	@Override
	public SrParseScopeAfter create(final CDD cdd1, final CDD cdd2) {
		return new SrParseScopeAfter(cdd1);
	}

	@Override
	public String toString() {
		return "After \"" + getCdd1().toBoogieString() + "\", ";
	}
}
