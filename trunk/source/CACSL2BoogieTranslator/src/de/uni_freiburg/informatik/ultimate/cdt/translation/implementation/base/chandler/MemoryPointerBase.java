package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

public abstract class MemoryPointerBase implements IMemoryPointer {
	TypeSizes mTypeSizes;
	BoogieType mBoogieType;

	public MemoryPointerBase(final TypeSizes typeSizes) {
		mTypeSizes = typeSizes;
	}

	/**
	 * Returns the base pointer Address.
	 *
	 * @return The base address.
	 */
	@Override
	public Expression getPointerAddress(final Expression pointer, final ILocation loc) {
		if (pointer instanceof StructConstructor) {
			return ((StructConstructor) pointer).getFieldValues()[0];
		}
		return ExpressionFactory.constructStructAccessExpression(loc, pointer, SFO.POINTER_BASE);
	}

	/**
	 * Constructs a valid pointer component relation expression.
	 *
	 * @return The expression.
	 */
	@SuppressWarnings("static-method")
	protected Expression pointerComponentRelation(final ILocation loc, final int op, final Expression leftPointer,
			final Expression rightPointer, final String component, final ExpressionTranslation expressionTranslation) {
		final StructAccessExpression leftComponent =
				ExpressionFactory.constructStructAccessExpression(loc, leftPointer, component);
		final StructAccessExpression rightComponent =
				ExpressionFactory.constructStructAccessExpression(loc, rightPointer, component);
		final var cTypeOfPointerComponents = expressionTranslation.getCTypeOfPointerComponents();
		switch (op) {
		case IASTBinaryExpression.op_equals:
		case IASTBinaryExpression.op_notequals: {
			return expressionTranslation.constructBinaryEqualityExpression(loc, op, leftComponent,
					cTypeOfPointerComponents, rightComponent, cTypeOfPointerComponents);
		}
		case IASTBinaryExpression.op_lessThan:
		case IASTBinaryExpression.op_lessEqual:
		case IASTBinaryExpression.op_greaterThan:
		case IASTBinaryExpression.op_greaterEqual:
			return expressionTranslation.constructBinaryComparisonExpression(loc, op, leftComponent,
					cTypeOfPointerComponents, rightComponent, cTypeOfPointerComponents);
		default:
			throw new IllegalArgumentException("op " + op);
		}
	}
}
