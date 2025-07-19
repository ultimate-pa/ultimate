package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.math.BigInteger;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.IPointerIntegerConversion;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.ICType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

public abstract class BaseMemoryAdressing implements IMemoryAdressing {
	ITypeHandler mTypeHandler;
	ExpressionTranslation mExpressionTranslation;
	IBooleanArrayHelper mBooleanArrayHelper;
	TypeSizes mTypeSizes;
	TypeSizeAndOffsetComputer mTypeSizeAndOffsetComputer;
	IPointerIntegerConversion mPointerIntegerConversion;

	BigInteger functionPointerPointerBaseValue = BigInteger.valueOf(-1);

	public BaseMemoryAdressing(final ITypeHandler typeHandler, final ExpressionTranslation exprTranslation,
			final IBooleanArrayHelper booleanArrayHelper, final TypeSizes typeSizes,
			final TypeSizeAndOffsetComputer typeSizeAndOffsetComputer) {
		mTypeHandler = typeHandler;
		mExpressionTranslation = exprTranslation;
		mBooleanArrayHelper = booleanArrayHelper;
		mTypeSizes = typeSizes;
		mTypeSizeAndOffsetComputer = typeSizeAndOffsetComputer;
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

	/**
	 * Multiply an integerExpresion with the size of another type.
	 *
	 * @return An {@link Expression} that represents <i>integerExpression * sizeof(valueType)</i>
	 */
	protected Expression multiplyWithSizeOfAnotherType(final ILocation loc, final ICType valueType,
			final Expression integerExpression, final CPrimitive integerExpresionType) {
		return mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_multiply,
				integerExpression, integerExpresionType, calculateSizeOf(loc, valueType), integerExpresionType);
	}

	/**
	 * Calculates the size of a given type.
	 *
	 * @return The size.
	 */
	private Expression calculateSizeOf(final ILocation loc, final ICType cType) {
		return mTypeSizeAndOffsetComputer.constructBytesizeExpression(loc, cType);
	}

	@Override
	public Expression constructPointerBaseValidityCheckExpr(final ILocation loc, final Expression ptr,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		final Expression ptrBase = MemoryHandler.getPointerBaseAddress(ptr, loc);
		final ArrayAccessExpression aae = ExpressionFactory.constructNestedArrayAccessExpression(loc,
				MemoryModelExpressionHelper.getValidArray(loc, requiredMemoryModelFeatures,
						memoryModelDeclarationsHandler),
				new Expression[] { ptrBase });
		return mBooleanArrayHelper.compareWithTrue(aae);
	}

	@Override
	public ExpressionResult convertPointerToInt(final ILocation loc, final ExpressionResult rexp,
			final CPrimitive newType) {
		return mPointerIntegerConversion.convertPointerToInt(loc, rexp, newType);
	}

	@Override
	public ExpressionResult convertIntToPointer(final ILocation loc, final ExpressionResult rexp,
			final CPointer newType) {
		return mPointerIntegerConversion.convertIntToPointer(loc, rexp, newType);
	}
}
