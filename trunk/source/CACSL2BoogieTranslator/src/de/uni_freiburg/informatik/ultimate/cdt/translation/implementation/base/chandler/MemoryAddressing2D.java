package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.StatementFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RequiresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.FunctionDeclarations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizeAndOffsetComputer.Offset;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.NonBijectiveMapping;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.OverapproximationUF;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.ICType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Spec;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.CheckMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.PointerIntegerConversion;

/**
 * The two dimensional memory addressing.
 */
public class MemoryAddressing2D extends MemoryAdressingBase<MemoryPointer2D> {
	private final MemoryMetadataDefault2D mMemoryMetadata;

	public MemoryAddressing2D(final ITypeHandler typeHandler, final ExpressionTranslation exprTranslation,
			final IBooleanArrayHelper booleanArrayHelper, final TypeSizes typeSizes,
			final TypeSizeAndOffsetComputer typeSizeAndOffsetComputer,
			final PointerIntegerConversion pointerIntegerMode, final FunctionDeclarations functionDeclarations,
			final MemoryPointer2D pointer) {
		super(typeHandler, exprTranslation, booleanArrayHelper, typeSizes, typeSizeAndOffsetComputer, pointer);

		mPointerIntegerConversion = switch (pointerIntegerMode) {
		case NonBijectiveMapping:
			yield new NonBijectiveMapping(exprTranslation, typeSizes, pointer);
		case Overapproximate:
			yield new OverapproximationUF(exprTranslation, functionDeclarations, typeHandler, typeSizes, pointer);
		default:
			throw new UnsupportedOperationException(
					"Pointer-Integer conversion not yet implemented " + pointerIntegerMode);
		};

		mMemoryMetadata = new MemoryMetadataDefault2D(typeHandler, exprTranslation, booleanArrayHelper);

		mMemoryManagementStrategy = new NonDetStrategy2D<>(typeSizes, exprTranslation, typeHandler,
				typeSizeAndOffsetComputer, booleanArrayHelper, this, mMemoryMetadata);
	}

	@Override
	public List<Declaration> constructMetaData(final RequiredMemoryModelFeatures requiredFeatures) {
		return mMemoryMetadata.constructMetaData(requiredFeatures);
	}

	@Override
	public List<MemoryModelDeclarations> getMetaDataDeclarations() {
		return mMemoryMetadata.getMetaDataDeclarations();
	}

	@Override
	public Expression doPointerArithmetic(final int operator, final ILocation loc, final Expression ptrAddress,
			final RValue integer, final ICType valueType, final CPrimitive integerExpressionType) {

		if (mTypeSizes.getSize(((CPrimitive) integer.getCType().getUnderlyingType()).getType()) != mTypeSizes
				.getSize(integerExpressionType.getType())) {
			throw new UnsupportedOperationException("not yet implemented, conversion is needed");
		}

		final Expression pointerBase = mMemoryPointer.getPointerAddress(ptrAddress, loc);
		final Expression pointerOffset = mMemoryPointer.pointerOffset(ptrAddress, loc);

		final Expression timesSizeOf =
				multiplyWithSizeOfAnotherType(loc, valueType, integer.getValue(), integerExpressionType);

		final Expression sum = mExpressionTranslation.constructArithmeticExpression(loc, operator, pointerOffset,
				integerExpressionType, timesSizeOf, integerExpressionType);

		return mMemoryPointer.constructPointerFromBaseAndOffset(pointerBase, sum, loc);
	}

	@Override
	public BigInteger getFixedAddressCounterCountingStep(final Expression size) {
		return BigInteger.ONE;
	}

	@Override
	public Expression constructAddressForStructField(final ILocation loc, final Expression baseAddress,
			final Offset fieldOffset, final CPrimitive sizeT) {

		final Expression pointerBase = mMemoryPointer.getPointerAddress(baseAddress, loc);
		final Expression pointerOffset = mMemoryPointer.pointerOffset(baseAddress, loc);

		final Expression sum = mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_plus,
				pointerOffset, sizeT, fieldOffset.getAddressOffsetAsExpression(loc), sizeT);

		return mMemoryPointer.constructPointerFromBaseAndOffset(pointerBase, sum, loc);
	}

	@Override
	public Expression addIntegerConstantToPointer(final ILocation loc, final Expression ptrExpr,
			final BigInteger integerConstant) {

		final Expression integerExpr =
				mTypeSizes.constructLiteralForIntegerType(loc, mTypeSizeAndOffsetComputer.getSizeT(), integerConstant);

		return addExpressionToPointer(loc, ptrExpr, integerExpr);
	}

	@Override
	public List<Specification> constructPointerValidityCheck(final ILocation loc, final String ptrName,
			final String procedureName, final CheckMode mode,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		if (mode == CheckMode.IGNORE) {
			return Collections.emptyList();
		}

		final Expression ptrExpr =
				ExpressionFactory.constructIdentifierExpression(loc, mTypeHandler.getBoogiePointerType(), ptrName,
						new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, procedureName));
		final Expression isValid = constructPointerValidityCheckExpr(loc, ptrExpr, requiredMemoryModelFeatures,
				memoryModelDeclarationsHandler);

		final boolean isFreeRequires = mode == CheckMode.CHECK ? false : true;

		final RequiresSpecification spec = new RequiresSpecification(loc, isFreeRequires, isValid);
		final Check check = new Check(Spec.MEMORY_DEREFERENCE);
		check.annotate(spec);
		return Collections.singletonList(spec);
	}

	@Override
	public List<Specification> constructPointerTargetFullyAllocatedCheck(final ILocation loc, final Expression size,
			final String ptrName, final String procedureName, final CheckMode mode,
			final Boolean isBitVectorTranslation, final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {

		if (mode == CheckMode.IGNORE) {
			return Collections.emptyList();
		}

		final Expression ptrExpr =
				ExpressionFactory.constructIdentifierExpression(loc, mTypeHandler.getBoogiePointerType(), ptrName,
						new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, procedureName));

		final Expression ptrBase = mMemoryPointer.getPointerAddress(ptrExpr, loc);
		final Expression ptrOffset = mMemoryPointer.pointerOffset(ptrExpr, loc);
		final CPrimitive cTypeOfPointerComponent = mExpressionTranslation.getCTypeOfPointerComponents();

		final Expression lengthArray =
				mMemoryMetadata.getLengthArray(loc, requiredMemoryModelFeatures, memoryModelDeclarationsHandler);
		final Expression aae =
				ExpressionFactory.constructNestedArrayAccessExpression(loc, lengthArray, new Expression[] { ptrBase });
		final Expression sum =
				constructPointerBinaryArithmeticExpression(loc, IASTBinaryExpression.op_plus, size, ptrOffset);
		Expression leq = constructPointerBinaryComparisonExpression(loc, IASTBinaryExpression.op_lessEqual, sum, aae);

		final Expression zeroNumericLiteral =
				mTypeSizes.constructLiteralForIntegerType(loc, cTypeOfPointerComponent, BigInteger.ZERO);

		final Expression offsetGeqZero = constructPointerBinaryComparisonExpression(loc,
				IASTBinaryExpression.op_lessEqual, zeroNumericLiteral, ptrOffset);

		if (isBitVectorTranslation) {
			/*
			 * Check that "#ptr!offset <= #ptr!offset + #sizeOf[Written|Read]Type", i.e., the sum does not overflow.
			 * (This works because #size.. is positive.)
			 */

			final Expression noOverFlowInSum =
					constructPointerBinaryComparisonExpression(loc, IASTBinaryExpression.op_lessEqual, ptrOffset, sum);
			leq = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICAND, leq, noOverFlowInSum);
		}

		final Expression offsetInAllocatedRange =
				ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICAND, leq, offsetGeqZero);

		final boolean isFreeRequires = mode == CheckMode.CHECK ? false : true;
		final RequiresSpecification spec = new RequiresSpecification(loc, isFreeRequires, offsetInAllocatedRange);
		final Check check = new Check(Spec.MEMORY_DEREFERENCE);
		check.annotate(spec);
		return Collections.singletonList(spec);
	}

	/**
	 * Create an arithmetic expression from a pointer component (base or offset) and another expression.
	 *
	 * @param op
	 *            One of the comparison operators defined in {@link IASTBinaryExpression}.
	 * @returns The expression.
	 */
	private Expression constructPointerBinaryArithmeticExpression(final ILocation loc, final int op,
			final Expression left, final Expression right) {
		final CPrimitive cTypeOfPointerComponent = mExpressionTranslation.getCTypeOfPointerComponents();
		return mExpressionTranslation.constructArithmeticExpression(loc, op, left, cTypeOfPointerComponent, right,
				cTypeOfPointerComponent);
	}

	/**
	 * Compare a pointer component (base or offset) to another expression.
	 *
	 * @param op
	 *            One of the comparison operators defined in {@link IASTBinaryExpression}.
	 * @return The expression.
	 */
	private Expression constructPointerBinaryComparisonExpression(final ILocation loc, final int op,
			final Expression left, final Expression right) {
		final CPrimitive cTypeOfPointerComponent = mExpressionTranslation.getCTypeOfPointerComponents();

		return mExpressionTranslation.constructBinaryComparisonExpression(loc, op, left, cTypeOfPointerComponent, right,
				cTypeOfPointerComponent);
	}

	@Override
	public List<Statement> getChecksForFreeCall(final ILocation loc, final RValue pointerToBeFreed,
			final boolean isPointerCheckRequired, final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		assert pointerToBeFreed.getCType().getUnderlyingType() instanceof CPointer;

		if (!isPointerCheckRequired) {
			return Collections.emptyList();
		}

		final var cTypeOfPointerComponent = mExpressionTranslation.getCTypeOfPointerComponents();

		final Expression zeroNumericExpr =
				mTypeSizes.constructLiteralForIntegerType(loc, cTypeOfPointerComponent, BigInteger.ZERO);

		final Expression valid =
				mMemoryMetadata.getValidArray(loc, requiredMemoryModelFeatures, memoryModelDeclarationsHandler);
		final Expression stackHeapBarrier = MemoryMetadataBase.getStackHeapBarrier(loc, requiredMemoryModelFeatures,
				memoryModelDeclarationsHandler);

		final Expression addrOffset = mMemoryPointer.pointerOffset(pointerToBeFreed.getValue(), loc);
		final Expression addrBase = mMemoryPointer.getPointerAddress(pointerToBeFreed.getValue(), loc);
		final Expression[] idcFree = { addrBase };

		final List<Statement> result = new ArrayList<>();

		/*
		 * creating the specification according to C99:7.20.3.2-2: The free function causes the space pointed to by ptr
		 * to be deallocated, that is, made available for further allocation. If ptr is a null pointer, no action
		 * occurs. Otherwise, if the argument does not match a pointer earlier returned by the calloc, malloc, or
		 * realloc function, or if the space has been deallocated by a call to free or realloc, the behavior is
		 * undefined.
		 */
		final Check check = new Check(Spec.MEMORY_FREE);

		// assert (~addr!offset == 0);
		final AssertStatement offsetZero = new AssertStatement(loc,
				ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, addrOffset, zeroNumericExpr));
		check.annotate(offsetZero);
		result.add(offsetZero);

		// assert (~addr!base < #StackHeapBarrier);
		final Expression inHeapArea =
				mExpressionTranslation.constructBinaryComparisonIntegerExpression(loc, IASTBinaryExpression.op_lessThan,
						addrBase, cTypeOfPointerComponent, stackHeapBarrier, cTypeOfPointerComponent);
		final AssertStatement assertInHeapArea = new AssertStatement(loc, inHeapArea);
		check.annotate(assertInHeapArea);
		result.add(assertInHeapArea);

		// ~addr!base == 0
		final Expression isNullPtr =
				ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, addrBase, zeroNumericExpr);

		// requires ~addr!base == 0 || #valid[~addr!base];
		final Expression addrIsValid = mBooleanArrayHelper
				.compareWithTrue(ExpressionFactory.constructNestedArrayAccessExpression(loc, valid, idcFree));
		final AssertStatement baseValid = new AssertStatement(loc,
				ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, isNullPtr, addrIsValid));
		check.annotate(baseValid);
		result.add(baseValid);

		return result;
	}

	@Override
	public Expression constructFunctionPointer(final ILocation loc, final BigInteger offset) {
		final Expression baseExpr = mTypeSizes.constructLiteralForIntegerType(loc,
				mExpressionTranslation.getCTypeOfPointerComponents(), functionPointerPointerBaseValue);
		final Expression offsetExpr = mTypeSizes.constructLiteralForIntegerType(loc,
				mExpressionTranslation.getCTypeOfPointerComponents(), offset);

		final Expression integerExpr =
				mTypeSizes.constructLiteralForIntegerType(loc, mTypeSizeAndOffsetComputer.getSizeT(), offset);

		final Expression offsetMinus =
				mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_plus, offsetExpr,
						mTypeSizeAndOffsetComputer.getSizeT(), integerExpr, mTypeSizeAndOffsetComputer.getSizeT());

		return mMemoryPointer.constructPointerFromBaseAndOffset(baseExpr, offsetMinus, loc);

	}

	@Override
	public Expression addExpressionToPointer(final ILocation loc, final Expression ptrExpr, final Expression expr) {
		final Expression base = mMemoryPointer.getPointerAddress(ptrExpr, loc);
		final Expression offset = mMemoryPointer.pointerOffset(ptrExpr, loc);

		final Expression offsetPlus =
				mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_plus, offset,
						mTypeSizeAndOffsetComputer.getSizeT(), expr, mTypeSizeAndOffsetComputer.getSizeT());

		return mMemoryPointer.constructPointerFromBaseAndOffset(base, offsetPlus, loc);
	}

	@Override
	public Expression getLastCharOfString(final ILocation loc, final CPrimitive sizeT, final IdentifierExpression len,
			final IdentifierExpression returnValue) {
		final var lenMinusOne = mExpressionTranslation.constructArithmeticIntegerExpression(loc,
				IASTBinaryExpression.op_minus, mExpressionTranslation.applyWraparound(loc, sizeT, len), sizeT,
				mTypeSizes.constructLiteralForIntegerType(loc, sizeT, BigInteger.ONE), sizeT);

		return mMemoryPointer.constructPointerFromBaseAndOffset(mMemoryPointer.getPointerAddress(returnValue, loc),
				lenMinusOne, loc);
	}

	@Override
	public AssumeStatement constructStrChrAssumeStatement(final ILocation loc, final Expression tmpExpr,
			final Expression argSPtr, final Expression nullPtrExpr,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {

		final var lengthArray =
				mMemoryMetadata.getLengthArray(loc, requiredMemoryModelFeatures, memoryModelDeclarationsHandler);

		final var cTypeOfPointerComponent = mExpressionTranslation.getCTypeOfPointerComponents();

		// res.base == 0
		final var baseEqualsNull = baseEqualsNull(loc, tmpExpr, cTypeOfPointerComponent, nullPtrExpr);

		// res.offset == 0
		final Expression offsetEqualsNull = mExpressionTranslation.constructBinaryComparisonIntegerExpression(loc,
				IASTBinaryExpression.op_equals, mMemoryPointer.pointerOffset(tmpExpr, loc), cTypeOfPointerComponent,
				mMemoryPointer.pointerOffset(nullPtrExpr, loc), cTypeOfPointerComponent);

		// res.base == 0 && res.offset == 0
		final Expression equalsNull =
				ExpressionFactory.newBinaryExpression(loc, Operator.LOGICAND, baseEqualsNull, offsetEqualsNull);
		final Expression baseEquals = baseEqual(loc, tmpExpr, cTypeOfPointerComponent, argSPtr);

		// res.offset >= 0
		final Expression offsetNonNegative = mExpressionTranslation.constructBinaryComparisonIntegerExpression(loc,
				IASTBinaryExpression.op_lessEqual,
				mExpressionTranslation.constructLiteralForIntegerType(loc, cTypeOfPointerComponent,
						new BigInteger("0")),
				cTypeOfPointerComponent, mMemoryPointer.pointerOffset(tmpExpr, loc), cTypeOfPointerComponent);
		// res.offset < length(arg_s.base)
		final Expression offsetSmallerLength = mExpressionTranslation
				.constructBinaryComparisonIntegerExpression(loc, IASTBinaryExpression.op_lessEqual,
						mMemoryPointer.pointerOffset(tmpExpr, loc), cTypeOfPointerComponent,
						ExpressionFactory.constructNestedArrayAccessExpression(loc, lengthArray,
								new Expression[] { mMemoryPointer.getPointerAddress(argSPtr, loc) }),
						cTypeOfPointerComponent);
		// res.base == arg_s.base && res.offset >= 0 && res.offset <= length(arg_s.base)
		final Expression inRange = ExpressionFactory.newBinaryExpression(loc, Operator.LOGICAND, baseEquals,
				ExpressionFactory.newBinaryExpression(loc, Operator.LOGICAND, offsetNonNegative, offsetSmallerLength));
		// assume equalsNull or inRange
		return new AssumeStatement(loc,
				ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, equalsNull, inRange));
	}

	@Override
	public Expression constructInitialPointerFromPointer(final ILocation loc, final Expression ptr) {
		final Expression zero = mExpressionTranslation.constructLiteralForIntegerType(loc,
				mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ZERO);

		return mMemoryPointer.constructPointerFromBaseAndOffset(mMemoryPointer.getPointerAddress(ptr, loc), zero, loc);
	}

	@Override
	public List<Statement> constructMemSafeStatementsForPointerExpression(final ILocation loc, final Expression ptr,
			final CheckMode pointerBaseValid, final CheckMode pointerTargetFullyAllocated,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		final List<Statement> result = new ArrayList<>();

		if (pointerBaseValid != CheckMode.IGNORE) {

			// valid[s.base]
			final Expression validBase = constructPointerValidityCheckExpr(loc, ptr, requiredMemoryModelFeatures,
					memoryModelDeclarationsHandler);
			final var stmt = statementDependentOnCheck(loc, pointerBaseValid, validBase);
			result.add(stmt);
		}

		if (pointerTargetFullyAllocated != CheckMode.IGNORE) {
			// s.offset < length[s.base])
			final Expression ptrOffset = mMemoryPointer.pointerOffset(ptr, loc);
			final Expression ptrBase = mMemoryPointer.getPointerAddress(ptr, loc);

			final Expression lengthArray =
					mMemoryMetadata.getLengthArray(loc, requiredMemoryModelFeatures, memoryModelDeclarationsHandler);

			final Expression aae = ExpressionFactory.constructNestedArrayAccessExpression(loc, lengthArray,
					new Expression[] { ptrBase });

			final Expression offsetSmallerLength =
					constructPointerBinaryComparisonExpression(loc, IASTBinaryExpression.op_lessThan, ptrOffset, aae);

			// s.offset >= 0;
			final var zeroExpr = mTypeSizes.constructLiteralForIntegerType(loc,
					mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ZERO);

			final Expression offsetNonnegative = constructPointerBinaryComparisonExpression(loc,
					IASTBinaryExpression.op_greaterEqual, ptrOffset, zeroExpr);

			final Expression aAndB = ExpressionFactory.newBinaryExpression(loc, Operator.LOGICAND, offsetSmallerLength,
					offsetNonnegative);

			final var stmt = statementDependentOnCheck(loc, pointerTargetFullyAllocated, aAndB);
			result.add(stmt);
		}
		return result;
	}

	private static Statement statementDependentOnCheck(final ILocation loc, final CheckMode check,
			final Expression expr) {
		if (check == CheckMode.CHECK) {
			final AssertStatement assertion = new AssertStatement(loc, expr);
			final Check chk = new Check(Spec.MEMORY_DEREFERENCE);
			chk.annotate(assertion);
			return assertion;
		}
		assert check == CheckMode.ASSUME : "missed a case?";
		return new AssumeStatement(loc, expr);
	}

	@Override
	public Statement checksForStringCopyOverlapping(final ILocation loc, final Expression src, final Expression srcId,
			final Expression destId, final Expression dest) {
		final Expression basesDistinct = ExpressionFactory.newBinaryExpression(loc, Operator.COMPNEQ,
				mMemoryPointer.getPointerAddress(src, loc), mMemoryPointer.getPointerAddress(src, loc));
		final Expression destDoesNotReachIntoSrc = ExpressionFactory.newBinaryExpression(loc, Operator.COMPLT,
				mMemoryPointer.pointerOffset(dest, loc), mMemoryPointer.pointerOffset(srcId, loc));
		final Expression srcDoesNotReachIntoDest = ExpressionFactory.newBinaryExpression(loc, Operator.COMPLT,
				mMemoryPointer.pointerOffset(src, loc), mMemoryPointer.pointerOffset(destId, loc));
		final Expression disjunction =
				ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, basesDistinct, ExpressionFactory
						.newBinaryExpression(loc, Operator.LOGICAND, destDoesNotReachIntoSrc, srcDoesNotReachIntoDest));

		return new AssertStatement(loc, disjunction);
	}

	@Override
	public Expression doPointerSubtraction(final ILocation loc, final Expression ptr1, final Expression ptr2,
			final ICType pointsToType) {
		final Expression ptr1Offset = mMemoryPointer.pointerOffset(ptr1, loc);
		final Expression ptr2Offset = mMemoryPointer.pointerOffset(ptr2, loc);

		return pointerComponentSubtraction(loc, ptr1Offset, ptr2Offset, pointsToType);
	}

	@Override
	public List<Statement> constructReallocBodyStatements(final ILocation loc, final String procName,
			final Collection<HeapDataArray> heapDataArrays, final BoogieType pointerType,
			final IdentifierExpression ptrIdExprImpl, final VariableLHS resultLhsImpl,
			final IdentifierExpression resultExprImpl, final IdentifierExpression sizeIdExprImpl,
			final RequiredMemoryModelFeatures requiredFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {

		final List<Statement> stmts = new ArrayList<>();

		// mem~X[res.base] := mem~X[ptr.base]
		for (final HeapDataArray hda : heapDataArrays) {
			final BoogieType innerArrayBoogieType =
					BoogieType.createArrayType(0, new BoogieType[] { mTypeHandler.getBoogieTypeForPointerComponents() },
							hda.getArrayContentBoogieType());

			final Expression select = ExpressionFactory.constructFunctionApplication(loc,
					MemoryHandler.getNameOfHeapSelectFunction(hda.getName()), new Expression[] {
							hda.getIdentifierExpression(), mMemoryPointer.getPointerAddress(ptrIdExprImpl, loc), },
					innerArrayBoogieType);

			stmts.add(StatementFactory.constructSingleAssignmentStatement(loc, hda.getVariableLHS(),
					ExpressionFactory.constructFunctionApplication(loc,
							MemoryHandler.getNameOfHeapStoreFunction(hda.getName()),
							new Expression[] { hda.getIdentifierExpression(),
									mMemoryPointer.getPointerAddress(resultExprImpl, loc), select },
							(BoogieType) hda.getVariableLHS().getType())));
		}

		return stmts;
	}

	@Override
	public Expression constructPointerValidityCheckExpr(final ILocation loc, final Expression ptr,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		final Expression ptrBase = mMemoryPointer.getPointerAddress(ptr, loc);
		final ArrayAccessExpression aae = ExpressionFactory.constructNestedArrayAccessExpression(loc,
				mMemoryMetadata.getValidArray(loc, requiredMemoryModelFeatures, memoryModelDeclarationsHandler),
				new Expression[] { ptrBase });
		return mBooleanArrayHelper.compareWithTrue(aae);
	}

	@Override
	public Expression getValidArray(final ILocation loc, final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		return mMemoryMetadata.getValidArray(loc, requiredMemoryModelFeatures, memoryModelDeclarationsHandler);
	}
}
