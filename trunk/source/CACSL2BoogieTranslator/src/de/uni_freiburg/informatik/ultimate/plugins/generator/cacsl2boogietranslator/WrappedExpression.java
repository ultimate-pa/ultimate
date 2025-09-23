package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;

public record WrappedExpression(Expression expr) implements IExpressionOrPointer {
	// empty
}
