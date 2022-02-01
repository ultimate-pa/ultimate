package de.uni_freiburg.informatik.ultimate.lib.srparse;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;

public class SrParseScopeBefore extends SrParseScope<SrParseScopeBefore> {

	public SrParseScopeBefore(final CDD cdd) {
		super(cdd, null);
	}

	@Override
	public SrParseScopeBefore create(final CDD cdd1, final CDD cdd2) {
		return new SrParseScopeBefore(cdd1);
	}

	@Override
	public String toString() {
		return "Before \"" + getCdd1() + "\", ";
	}
}
