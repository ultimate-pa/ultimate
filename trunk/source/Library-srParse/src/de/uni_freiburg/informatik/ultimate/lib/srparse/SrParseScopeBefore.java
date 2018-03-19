package de.uni_freiburg.informatik.ultimate.lib.srparse;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;

public class SrParseScopeBefore extends SrParseScope {

	public SrParseScopeBefore(final CDD cdd) {
		super(cdd, null);
	}

	@Override
	public String toString() {
		return "Before \"" + getCdd1() + "\", ";
	}
}
