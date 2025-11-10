package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.math.BigInteger;
import java.util.Collections;
import java.util.List;
import java.util.Set;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.FunctionDeclarations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.IPointerIntegerConversion;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.NonBijectiveMapping2D;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.NonBijectiveMapping1D;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.OverapproximationUF2D;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.OverapproximationUF1D;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.ICType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.CheckMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.PointerIntegerConversion;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

public abstract class MemoryAdressingBase<T extends IMemoryPointer> implements IMemoryAdressing {
	protected final ITypeHandler mTypeHandler;
	protected final ExpressionTranslation mExpressionTranslation;
	protected final IBooleanArrayHelper mBooleanArrayHelper;
	protected final TypeSizes mTypeSizes;
	protected final TypeSizeAndOffsetComputer mTypeSizeAndOffsetComputer;
	protected IPointerIntegerConversion mPointerIntegerConversion;
	protected final T mMemoryPointer;
	protected IMemoryManagementStrategy mMemoryManagementStrategy;

	protected final BigInteger functionPointerPointerBaseValue = BigInteger.valueOf(-1);

	public MemoryAdressingBase(final ITypeHandler typeHandler, final ExpressionTranslation exprTranslation,
			final IBooleanArrayHelper booleanArrayHelper, final TypeSizes typeSizes,
			final TypeSizeAndOffsetComputer typeSizeAndOffsetComputer, final T pointer,
			final PointerIntegerConversion pointerIntegerMode, final FunctionDeclarations functionDeclarations) {
		mTypeHandler = typeHandler;
		mExpressionTranslation = exprTranslation;
		mBooleanArrayHelper = booleanArrayHelper;
		mTypeSizes = typeSizes;
		mTypeSizeAndOffsetComputer = typeSizeAndOffsetComputer;
		mMemoryPointer = pointer;

		mPointerIntegerConversion = switch (pointerIntegerMode) {
		case NonBijectiveMapping:
			if (mMemoryPointer instanceof final MemoryPointer1D pointer1D) {
				yield new NonBijectiveMapping1D(exprTranslation, pointer1D);
			} else if (mMemoryPointer instanceof final MemoryPointer2D pointer2D) {
				yield new NonBijectiveMapping2D(exprTranslation, typeSizes, pointer2D);
			} else {
				throw new UnsupportedOperationException("Unknown pointer type " + mMemoryPointer.getClass());
			}
		case Overapproximate:
			if (mMemoryPointer instanceof final MemoryPointer1D pointer1D) {
				yield new OverapproximationUF1D(exprTranslation, functionDeclarations, typeHandler,
						pointer1D);
			} else if (mMemoryPointer instanceof final MemoryPointer2D pointer2D) {
				yield new OverapproximationUF2D(exprTranslation, functionDeclarations, typeHandler, typeSizes, pointer2D);
			} else {
				throw new UnsupportedOperationException("Unknown pointer type " + mMemoryPointer.getClass());
			}
		default:
			throw new UnsupportedOperationException(
					"Pointer-Integer conversion not yet implemented " + pointerIntegerMode);
		};
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
	public List<Pair<Expression, Set<VariableLHS>>> constructMallocSpecificationExpressions(final ILocation tuLoc,
			final MemoryArea memoryArea, final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		return mMemoryManagementStrategy.constructMallocSpecificationExpressions(tuLoc, memoryArea,
				requiredMemoryModelFeatures, memoryModelDeclarationsHandler);
	}

	@Override
	public List<Triple<Expression, Set<VariableLHS>, Boolean>> constructDeallocSpecificationExpressions(
			final ILocation tuLoc, final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		return mMemoryManagementStrategy.constructDeallocSpecificationExpressions(tuLoc, requiredMemoryModelFeatures,
				memoryModelDeclarationsHandler);
	}

	@Override
	public List<Statement> constructUltimateInitStatements(final ILocation loc,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler, final BigInteger fixedAddressCounter) {
		return mMemoryManagementStrategy.constructUltimateInitStatements(loc, requiredMemoryModelFeatures,
				memoryModelDeclarationsHandler, fixedAddressCounter);
	}

	@Override
	public List<Pair<Expression, Set<VariableLHS>>> constructAllocInitSpecificationExpressions(final ILocation tuLoc,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		return mMemoryManagementStrategy.constructAllocInitSpecificationExpressions(tuLoc, requiredMemoryModelFeatures,
				memoryModelDeclarationsHandler);
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
				mMemoryPointer.getPointerAddress(tmpExpr, loc), cTypeOfPointerComponent,
				mMemoryPointer.getPointerAddress(nullPtrExpr, loc), cTypeOfPointerComponent);
	}

	protected Expression baseEqual(final ILocation loc, final Expression tmpExpr,
			final CPrimitive cTypeOfPointerComponent, final Expression argSPtr) {
		// res.base == arg_s.base
		return mExpressionTranslation.constructBinaryComparisonIntegerExpression(loc, IASTBinaryExpression.op_equals,
				mMemoryPointer.getPointerAddress(tmpExpr, loc), cTypeOfPointerComponent,
				mMemoryPointer.getPointerAddress(argSPtr, loc), cTypeOfPointerComponent);
	}

	@Override
	public Expression[] constructRhsAssignmentStatementHda(final ILocation loc, final HeapDataArray hda,
			final Expression baseAddress) {
		return new Expression[] { ExpressionFactory.constructFunctionApplication(loc,
				MemoryHandler.getNameOfHeapInitFunction(hda.getName()),
				new Expression[] { hda.getIdentifierExpression(), mMemoryPointer.getPointerAddress(baseAddress, loc) },
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

	/**
	 * Creates a valid expression representing a pointer subtractions of a pointer component. The component is either
	 * base or offset.
	 *
	 * @return The expression.
	 */
	protected Expression pointerComponentSubtraction(final ILocation loc, final Expression ptrComp1,
			final Expression ptrComp2, final ICType pointsToType) {
		final CPrimitive typesizeType = mExpressionTranslation.getCTypeOfPointerComponents();

		final Expression offsetDifference = mExpressionTranslation.constructArithmeticExpression(loc,
				IASTBinaryExpression.op_minus, ptrComp1, typesizeType, ptrComp2, typesizeType);

		final Expression typesize = mTypeSizeAndOffsetComputer.constructBytesizeExpression(loc, pointsToType);

		final Expression offsetDifferenceDividedByTypesize = mExpressionTranslation.constructArithmeticExpression(loc,
				IASTBinaryExpression.op_divide, offsetDifference, typesizeType, typesize, typesizeType);

		return offsetDifferenceDividedByTypesize;
	}
}
