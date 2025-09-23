package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * Represents a 1-dimensional pointer variable in Boogie.
 *
 * This class is only used to represent variables (keys in the program state). For values of pointer structs, use
 * {@link PointerValue1D} instead.
 */
public record PointerVariable1D(ILocation loc, IdentifierExpression rawPointer, boolean isOld) {
	/**
	 * Checks if the given expression is the base of a pointer struct and returns the corresponding
	 * {@link PointerVariable1D} if so. Otherwise, returns {@code null}.
	 */
	static PointerVariable1D fromBaseExpression(final Expression expr) {
		if (expr instanceof final IdentifierExpression id && id.getIdentifier().endsWith(SFO.POINTER_BASE)) {
			final String baseName = id.getIdentifier();
			final String pointerName = baseName.substring(0, baseName.length() - SFO.POINTER_BASE.length() - 1);
			final var pointer =
					new IdentifierExpression(id.getLoc(), id.getType(), pointerName, id.getDeclarationInformation());
			return new PointerVariable1D(pointer.getLoc(), pointer, false);
		}
		if (expr instanceof final UnaryExpression unary && unary.getOperator() == Operator.OLD) {
			final var underlying = fromBaseExpression(unary.getExpr());
			if (underlying != null) {
				return new PointerVariable1D(unary.getLoc(), underlying.rawPointer(), true);
			}
		}
		return null;
	}

	Expression toExpression() {
		if (isOld) {
			return new UnaryExpression(loc, Operator.OLD, rawPointer);
		}
		return rawPointer;
	}

	PointerVariable1D asNonOld() {
		return new PointerVariable1D(rawPointer.getLoc(), rawPointer, false);
	}
}
