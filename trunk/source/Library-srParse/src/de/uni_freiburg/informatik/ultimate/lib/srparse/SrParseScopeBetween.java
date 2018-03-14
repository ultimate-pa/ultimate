package de.uni_freiburg.informatik.ultimate.lib.srparse;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;

public class SrParseScopeBetween extends SrParseScope {

	public SrParseScopeBetween(final CDD cdd1, final CDD cdd2) {
		super(cdd1, cdd2);
	}

	@Override
	public String toString() {
		return "Between \"" + getCdd1() + "\" and \"" + getCdd2() + "\", ";
	}
}
