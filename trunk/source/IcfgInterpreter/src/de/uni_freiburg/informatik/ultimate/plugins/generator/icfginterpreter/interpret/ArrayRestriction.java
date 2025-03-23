package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret;

import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.SMTArray;

public class ArrayRestriction extends Restriction<SMTArray> {
	public ArrayRestriction(final HashSet<SMTArray> inequal) {
		super(inequal, null, null);
	}
}