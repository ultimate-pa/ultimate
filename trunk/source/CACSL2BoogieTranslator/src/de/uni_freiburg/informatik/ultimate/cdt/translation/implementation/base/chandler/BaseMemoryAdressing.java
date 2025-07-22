package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.math.BigInteger;
import java.util.Collections;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.IPointerIntegerConversion;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.ICType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.CheckMode;

public abstract class BaseMemoryAdressing<T extends IMemoryPointer> implements IMemoryAdressing {
	ITypeHandler mTypeHandler;
	ExpressionTranslation mExpressionTranslation;
	IBooleanArrayHelper mBooleanArrayHelper;
	TypeSizes mTypeSizes;
	TypeSizeAndOffsetComputer mTypeSizeAndOffsetComputer;
	IPointerIntegerConversion mPointerIntegerConversion;
	T mMemoryPointer;

	BigInteger functionPointerPointerBaseValue = BigInteger.valueOf(-1);

	public BaseMemoryAdressing(final ITypeHandler typeHandler, final ExpressionTranslation exprTranslation,
			final IBooleanArrayHelper booleanArrayHelper, final TypeSizes typeSizes,
			final TypeSizeAndOffsetComputer typeSizeAndOffsetComputer, final T pointer) {
		mTypeHandler = typeHandler;
		mExpressionTranslation = exprTranslation;
		mBooleanArrayHelper = booleanArrayHelper;
		mTypeSizes = typeSizes;
		mTypeSizeAndOffsetComputer = typeSizeAndOffsetComputer;
		mMemoryPointer = pointer;
	}

	protected VariableDeclaration constructStackHeapBarrierConstant() {
		final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
		return new VariableDeclaration(ignoreLoc, new Attribute[0],
				new VarList[] { new VarList(ignoreLoc,
						new String[] { MemoryModelDeclarations.ULTIMATE_STACK_HEAP_BARRIER.getName() },
						mTypeHandler.cType2AstType(ignoreLoc, mExpressionTranslation.getCTypeOfPointerComponents())) });
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
	public Expression constructPointerValidityCheckExpr(final ILocation loc, final Expression ptr,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		final Expression ptrBase = mMemoryPointer.pointerAddress(ptr, loc);
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

	protected Expression baseEqualsNull(final ILocation loc, final Expression tmpExpr,
			final CPrimitive cTypeOfPointerComponent, final Expression nullPtrExpr) {
		// res.base == 0
		return mExpressionTranslation.constructBinaryComparisonIntegerExpression(loc, IASTBinaryExpression.op_equals,
				mMemoryPointer.pointerAddress(tmpExpr, loc), cTypeOfPointerComponent,
				mMemoryPointer.pointerAddress(nullPtrExpr, loc), cTypeOfPointerComponent);
	}

	protected Expression baseEqual(final ILocation loc, final Expression tmpExpr,
			final CPrimitive cTypeOfPointerComponent, final Expression argSPtr) {
		// res.base == arg_s.base
		return mExpressionTranslation.constructBinaryComparisonIntegerExpression(loc, IASTBinaryExpression.op_equals,
				mMemoryPointer.pointerAddress(tmpExpr, loc), cTypeOfPointerComponent,
				mMemoryPointer.pointerAddress(argSPtr, loc), cTypeOfPointerComponent);
	}

	@Override
	public Expression[] rhsAssignmentStatementHda(final ILocation loc, final HeapDataArray hda,
			final Expression baseAddress) {
		return new Expression[] { ExpressionFactory.constructFunctionApplication(loc,
				MemoryHandler.getNameOfHeapInitFunction(hda.getName()),
				new Expression[] { hda.getIdentifierExpression(), mMemoryPointer.pointerAddress(baseAddress, loc) },
				(BoogieType) hda.getIdentifierExpression().getType()) };
	}

	@Override
	public List<Specification> constructPointerValidityCheck(final ILocation loc, final String ptrName,
			final String procedureName, final CheckMode mode,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		if (mode == CheckMode.IGNORE) {
			return Collections.emptyList();
		}

		throw new UnsupportedOperationException("The pointer base validity check is not compatible with the selected: "
				+ this.getClass() + " addressing mode!");
	}

	@Override
	public List<Specification> constructPointerTargetFullyAllocatedCheck(final ILocation loc, final Expression size,
			final String ptrName, final String procedureName, final CheckMode mode,
			final Boolean isBitVectorTranslation, final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		if (mode == CheckMode.IGNORE) {
			return Collections.emptyList();
		}

		throw new UnsupportedOperationException(
				"The target pointer fully allocated check is not compatible with the selected: " + this.getClass()
						+ "  " + "addressing mode!");
	}

	@Override
	public List<Statement> getChecksForFreeCall(final ILocation loc, final RValue pointerToBeFreed,
			final boolean isPointerCheckRequired, final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		assert pointerToBeFreed.getCType().getUnderlyingType() instanceof CPointer;

		if (!isPointerCheckRequired) {
			return Collections.emptyList();
		}

		throw new UnsupportedOperationException(
				"The check if the freed pointer is valid is not compatible with the selected: " + this.getClass()
						+ "  addressing mode!");
	}

	@Override
	public List<Statement> constructMemSafeStatementsForPointerExpression(final ILocation loc, final Expression ptr,
			final CheckMode pointerBaseValid, final CheckMode pointerTargetFullyAllocated,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		if (pointerBaseValid == CheckMode.IGNORE && pointerTargetFullyAllocated == CheckMode.IGNORE) {
			return Collections.emptyList();
		}

		throw new UnsupportedOperationException(
				"The MemSafety checks are not compatible with the selected: " + this.getClass() + "  addressing mode!");
	}

	@Override
	public Statement checksForStringCopyOverlapping(final ILocation loc, final Expression src, final Expression srcId,
			final Expression destId, final Expression dest) {
		throw new UnsupportedOperationException(
				"The string copy overlapping check is not compatible with the selected: " + this.getClass()
						+ "  addressing mode!");
	}
}
