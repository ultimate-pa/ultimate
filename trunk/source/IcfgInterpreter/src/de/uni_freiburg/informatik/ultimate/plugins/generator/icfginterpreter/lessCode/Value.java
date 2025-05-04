package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ITermProvider;

public interface Value extends ITermProvider, Comparable<Value> {
	BoolValue equals(Value other);

	BoolValue distinct(Value other);

	Object getValue();

	@Override
	int compareTo(Value b);
}