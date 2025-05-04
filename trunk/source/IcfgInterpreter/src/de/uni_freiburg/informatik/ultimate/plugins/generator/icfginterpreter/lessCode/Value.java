package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ITermProvider;

public interface Value extends ITermProvider {
	BoolValue equals(Value other);

	BoolValue distinct(Value other);

	Object getValue();

	int compareTo(Value b);
}