package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

public abstract class BaseMemoryManagementStrategy implements IMemoryManagementStrategy {
	protected final TypeSizes mTypeSizes;
	protected final ExpressionTranslation mExpressionTranslation;
	protected final ITypeHandler mTypeHandler;
	protected final TypeSizeAndOffsetComputer mTypeSizeAndOffsetComputer;

	public BaseMemoryManagementStrategy(final TypeSizes typeSizes, final ExpressionTranslation expressionTranslation,
			final ITypeHandler typeHandler, final TypeSizeAndOffsetComputer typeSizeAndOffsetComputer) {
		mTypeSizes = typeSizes;
		mExpressionTranslation = expressionTranslation;
		mTypeHandler = typeHandler;
		mTypeSizeAndOffsetComputer = typeSizeAndOffsetComputer;
	}

	protected static Expression baseNotEqualZeroExpr(final ILocation tuLoc, final Expression resultExpr,
			final Expression zeroNumericValueExpr) {
		return ExpressionFactory.newBinaryExpression(tuLoc, Operator.COMPNEQ,
				ExpressionFactory.constructStructAccessExpression(tuLoc, resultExpr, SFO.POINTER_BASE),
				zeroNumericValueExpr);
	}

	protected Expression baseGreaterThanBarrier(final ILocation tuLoc, final Expression stackHeapBarrierExpr,
			final Expression resultExpr) {
		return mExpressionTranslation.constructBinaryComparisonIntegerExpression(tuLoc,
				IASTBinaryExpression.op_greaterThan,
				ExpressionFactory.constructStructAccessExpression(tuLoc, resultExpr, SFO.POINTER_BASE),
				mExpressionTranslation.getCTypeOfPointerComponents(), stackHeapBarrierExpr,
				mExpressionTranslation.getCTypeOfPointerComponents());
	}

	protected Expression baseSmallerThanBarrier(final ILocation tuLoc, final Expression stackHeapBarrierExpr,
			final Expression resultExpr) {
		return mExpressionTranslation.constructBinaryComparisonIntegerExpression(tuLoc,
				IASTBinaryExpression.op_lessThan,
				ExpressionFactory.constructStructAccessExpression(tuLoc, resultExpr, SFO.POINTER_BASE),
				mExpressionTranslation.getCTypeOfPointerComponents(), stackHeapBarrierExpr,
				mExpressionTranslation.getCTypeOfPointerComponents());
	}
}
