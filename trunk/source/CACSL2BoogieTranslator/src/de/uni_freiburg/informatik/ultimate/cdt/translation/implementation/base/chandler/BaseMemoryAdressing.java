package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

public abstract class BaseMemoryAdressing implements IMemoryAdressing {
	ITypeHandler mTypeHandler;
	ExpressionTranslation mExpressionTranslation;
	IBooleanArrayHelper mBooleanArrayHelper;
	TypeSizes mTypeSizes;

	public BaseMemoryAdressing(final ITypeHandler typeHandler, final ExpressionTranslation exprTranslation,
			final IBooleanArrayHelper booleanArrayHelper, final TypeSizes typeSizes) {
		mTypeHandler = typeHandler;
		mExpressionTranslation = exprTranslation;
		mBooleanArrayHelper = booleanArrayHelper;
		mTypeSizes = typeSizes;
	}

	protected VariableDeclaration constructStackHeapBarrierConstant() {
		final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
		return new VariableDeclaration(ignoreLoc, new Attribute[0],
				new VarList[] { new VarList(ignoreLoc,
						new String[] { MemoryModelDeclarations.ULTIMATE_STACK_HEAP_BARRIER.getName() },
						mTypeHandler.cType2AstType(ignoreLoc, mExpressionTranslation.getCTypeOfPointerComponents())) });
	}

	protected static Expression offsetEqualsZeroExpr(final ILocation tuLoc, final Expression resultExpr,
			final Expression zeroNumericValueExpr) {
		return ExpressionFactory.newBinaryExpression(tuLoc, Operator.COMPEQ,
				ExpressionFactory.constructStructAccessExpression(tuLoc, resultExpr, SFO.POINTER_OFFSET),
				zeroNumericValueExpr);
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
				IASTBinaryExpression.op_lessThan, stackHeapBarrierExpr,
				mExpressionTranslation.getCTypeOfPointerComponents(),
				ExpressionFactory.constructStructAccessExpression(tuLoc, resultExpr, SFO.POINTER_BASE),
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
