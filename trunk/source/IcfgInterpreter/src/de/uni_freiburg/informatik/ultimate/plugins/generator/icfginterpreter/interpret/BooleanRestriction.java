package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret;

import java.util.HashSet;

public class BooleanRestriction extends Restriction<Boolean> {
	public BooleanRestriction(final HashSet<Boolean> inequal) {
		super(inequal, null, null);
	}
}