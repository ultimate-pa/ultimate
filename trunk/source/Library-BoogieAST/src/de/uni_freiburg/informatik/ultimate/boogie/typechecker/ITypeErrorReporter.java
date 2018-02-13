package de.uni_freiburg.informatik.ultimate.boogie.typechecker;

import java.util.function.Function;

public interface ITypeErrorReporter<T> {
	void report(final Function<T, String> func);
}