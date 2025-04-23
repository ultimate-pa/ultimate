package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode;

public interface Value {
	BoolValue equals(Value other);

	BoolValue distinct(Value other);

	Object getValue();
}