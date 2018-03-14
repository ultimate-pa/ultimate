package de.uni_freiburg.informatik.ultimate.lib.srparse;

public class SrParseScopeGlob extends SrParseScope {

	public SrParseScopeGlob() {
		super(null, null);
	}

	@Override
	public String toString() {
		return "Globally, ";
	}
}
