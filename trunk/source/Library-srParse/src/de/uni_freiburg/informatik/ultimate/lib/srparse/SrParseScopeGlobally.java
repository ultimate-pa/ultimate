package de.uni_freiburg.informatik.ultimate.lib.srparse;

public class SrParseScopeGlobally extends SrParseScope {

	public SrParseScopeGlobally() {
		super(null, null);
	}

	@Override
	public String toString() {
		return "Globally, ";
	}
}
