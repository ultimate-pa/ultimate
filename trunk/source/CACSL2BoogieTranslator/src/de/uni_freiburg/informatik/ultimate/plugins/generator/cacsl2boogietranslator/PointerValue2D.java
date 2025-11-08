package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;

/**
 * Represents a pair of values forming a pointer struct in Boogie.
 */
public record PointerValue2D(Expression base, Expression offset) implements IPointerValue {
	// empty
}
