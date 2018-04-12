package de.uni_freiburg.informatik.ultimate.lib.srparse;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;

public class SrParseScopeAfterUntil extends SrParseScope {

	public SrParseScopeAfterUntil(final CDD cdd1, final CDD cdd2) {
		super(cdd1, cdd2);
	}

	@Override
	public String toString() {
		return "After \"" + getCdd1().toBoogieString() + "\" until \"" + getCdd2().toBoogieString() + "\", ";
	}
}
