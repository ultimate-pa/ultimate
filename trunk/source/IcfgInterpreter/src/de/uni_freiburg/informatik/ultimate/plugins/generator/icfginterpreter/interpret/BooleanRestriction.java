package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret;

import java.util.ArrayList;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;

public class BooleanRestriction extends Restriction<Boolean> {
	public BooleanRestriction(final HashSet<Boolean> inequal) {
		super(inequal, null, null);
	}

	@Override
	public String toCode() {
		return "new " + this.getClass().getSimpleName() + "(Util.toHashSet("
				+ String.join(", ", Util.map(mInequal, (inequal) -> {
					return inequal.toString();
				}, new ArrayList<>()));
	}
}