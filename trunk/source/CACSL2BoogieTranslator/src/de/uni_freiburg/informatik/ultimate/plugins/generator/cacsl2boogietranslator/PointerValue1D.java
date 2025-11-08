package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;

/**
 * Represents a single value forming a pointer struct in Boogie.
 */
public record PointerValue1D(Expression base) implements IPointerValue {

}
