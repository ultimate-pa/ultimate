package de.uni_freiburg.informatik.ultimate.lib.srparse;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;

public class srParseScopeAfter extends srParseScope {

	public srParseScopeAfter(final CDD cdd1) {
		this.cdd1 = cdd1;
	}

	@Override
	public String toString() {
		return "After \"" + cdd1 + "\", ";
	}
}
