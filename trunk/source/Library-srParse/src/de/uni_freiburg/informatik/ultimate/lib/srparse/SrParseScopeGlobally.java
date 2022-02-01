package de.uni_freiburg.informatik.ultimate.lib.srparse;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;

public class SrParseScopeGlobally extends SrParseScope<SrParseScopeGlobally> {

	public SrParseScopeGlobally() {
		super(null, null);
	}

	@Override
	public SrParseScopeGlobally create(final CDD cdd1, final CDD cdd2) {
		return new SrParseScopeGlobally();
	}

	@Override
	public String toString() {
		return "Globally, ";
	}
}
