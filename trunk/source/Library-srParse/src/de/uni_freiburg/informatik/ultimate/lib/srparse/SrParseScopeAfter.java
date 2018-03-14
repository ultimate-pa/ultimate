package de.uni_freiburg.informatik.ultimate.lib.srparse;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;

public class SrParseScopeAfter extends SrParseScope {

	public SrParseScopeAfter(final CDD cdd1) {
		super(cdd1, null);
	}

	@Override
	public String toString() {
		return "After \"" + getCdd1() + "\", ";
	}
}
