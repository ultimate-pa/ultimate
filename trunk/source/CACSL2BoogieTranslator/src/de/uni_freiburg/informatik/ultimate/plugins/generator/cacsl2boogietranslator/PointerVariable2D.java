package de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * Represents a 2-dimensional pointer variable in Boogie.
 *
 * This class is only used to represent variables (keys in the program state). For values of pointer structs, use
 * {@link PointerValue2D} instead.
 */
public record PointerVariable2D(ILocation loc, IdentifierExpression rawPointer, boolean isOld) {
	/**
	 * Checks if the given expression is the base of a pointer struct and returns the corresponding
	 * {@link PointerVariable2D} if so. Otherwise, returns {@code null}.
	 */
	static PointerVariable2D fromBaseExpression(final Expression expr) {
		if (expr instanceof final IdentifierExpression id && id.getIdentifier().endsWith(SFO.POINTER_BASE)) {
			final String baseName = id.getIdentifier();
			final String pointerName = baseName.substring(0, baseName.length() - SFO.POINTER_BASE.length() - 1);
			final var pointer =
					new IdentifierExpression(id.getLoc(), id.getType(), pointerName, id.getDeclarationInformation());
			return new PointerVariable2D(pointer.getLoc(), pointer, false);
		}
		if (expr instanceof final UnaryExpression unary && unary.getOperator() == Operator.OLD) {
			final var underlying = fromBaseExpression(unary.getExpr());
			if (underlying != null) {
				return new PointerVariable2D(unary.getLoc(), underlying.rawPointer(), true);
			}
		}
		return null;
	}

	/**
	 * Checks if the given expression is a variable representing an offset for this pointer variable.
	 */
	boolean isMatchingPointerOffset(final Expression expr) {
		if (isOld() && expr instanceof final UnaryExpression uExpr) {
			return uExpr.getOperator() == Operator.OLD && asNonOld().isMatchingPointerOffset(uExpr.getExpr());
		}
		if (!isOld() && expr instanceof final IdentifierExpression idExpr) {
			final var identifier = idExpr.getIdentifier();
			return identifier.startsWith(rawPointer().getIdentifier()) && identifier.endsWith(SFO.POINTER_OFFSET);
		}
		return false;
	}

	Expression toExpression() {
		if (isOld) {
			return new UnaryExpression(loc, Operator.OLD, rawPointer);
		}
		return rawPointer;
	}

	PointerVariable2D asNonOld() {
		return new PointerVariable2D(rawPointer.getLoc(), rawPointer, false);
	}
}
