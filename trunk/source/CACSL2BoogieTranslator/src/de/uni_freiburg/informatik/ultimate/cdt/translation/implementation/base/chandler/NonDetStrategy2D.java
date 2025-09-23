package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CTranslationUtil;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * This strategy is the default strategy for the 2D-memory addressing mode. The generic parameter is used to ensure that
 * this strategy is only instanciated within the 2D addressing class because it is not compatible with other modes.
 * Memory addresses get a nondet value, which is not used yet.
 */
@SuppressWarnings("unused")
public class NonDetStrategy2D<T extends MemoryAddressing2D, T1 extends MemoryMetadataDefault2D>
		extends BaseMemoryManagementStrategy {
	IBooleanArrayHelper mBooleanArrayHelper;
	T mMemoryAddressing;
	T1 mMemoryMetadata;

	public NonDetStrategy2D(final TypeSizes typeSizes, final ExpressionTranslation expressionTranslation,
			final ITypeHandler typeHandler, final TypeSizeAndOffsetComputer typeSizeAndOffsetComputer,
			final IBooleanArrayHelper booleanArrayHelper, final T addressing, final T1 metadata) {
		super(typeSizes, expressionTranslation, typeHandler, typeSizeAndOffsetComputer);

		mBooleanArrayHelper = booleanArrayHelper;
		mMemoryAddressing = addressing;
		mMemoryMetadata = metadata;
	}

	@Override
	public List<Pair<Expression, Set<VariableLHS>>> constructMallocSpecificationExpressions(final ILocation tuLoc,
			final MemoryArea memoryArea, final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {

		final var memoryAreaName = memoryArea.getMemoryStructureDeclaration().getName();
		final var falseExpr = mBooleanArrayHelper.constructFalse();
		final var trueExpr = mBooleanArrayHelper.constructTrue();

		final var validArrayExpr =
				mMemoryMetadata.getValidArray(tuLoc, requiredMemoryModelFeatures, memoryModelDeclarationsHandler);
		final var stackHeapBarrierExpr = MemoryMetadataBase.getStackHeapBarrier(tuLoc, requiredMemoryModelFeatures,
				memoryModelDeclarationsHandler);
		final var lengthArrayExpr =
				mMemoryMetadata.getLengthArray(tuLoc, requiredMemoryModelFeatures, memoryModelDeclarationsHandler);

		final var zeroNumericValueExpr = mTypeSizes.constructLiteralForIntegerType(tuLoc,
				mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ZERO);
		final var resultExpr =
				ExpressionFactory.constructIdentifierExpression(tuLoc, mTypeHandler.getBoogiePointerType(), SFO.RES,
						new DeclarationInformation(StorageClass.PROC_FUNC_OUTPARAM, memoryAreaName));

		final var sizeExpr =
				ExpressionFactory.constructIdentifierExpression(tuLoc, mTypeHandler.getBoogieTypeForSizeT(), SFO.SIZE,
						new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, memoryAreaName));

		final var resBaseExpr = ExpressionFactory.constructStructAccessExpression(tuLoc, resultExpr, SFO.POINTER_BASE);

		final ArrayList<Pair<Expression, Set<VariableLHS>>> expressions = new ArrayList<>();

		// old(#valid)[#res!base] == false
		final var freshLocationCurrentlyNotValidExpr = ExpressionFactory.newBinaryExpression(tuLoc, Operator.COMPEQ,
				ExpressionFactory.constructNestedArrayAccessExpression(tuLoc,
						ExpressionFactory.constructUnaryExpression(tuLoc, UnaryExpression.Operator.OLD, validArrayExpr),
						new Expression[] { resBaseExpr }),
				falseExpr);

		expressions.add(new Pair<>(freshLocationCurrentlyNotValidExpr, Collections.emptySet()));

		// #valid == old(#valid)[#res!base := true]
		final var validUpdateExpr =
				MemoryModelExpressionHelper.ensuresArrayUpdate(tuLoc, trueExpr, resBaseExpr, validArrayExpr);
		expressions.add(new Pair<>(validUpdateExpr,
				Collections.singleton((VariableLHS) CTranslationUtil.convertExpressionToLHS(validArrayExpr))));

		// #res!offset == 0
		final var offsetEqualZeroExpr = ExpressionFactory.newBinaryExpression(tuLoc, Operator.COMPEQ,
				mMemoryAddressing.mMemoryPointer.pointerOffset(resultExpr, tuLoc), zeroNumericValueExpr);
		expressions.add(new Pair<>(offsetEqualZeroExpr, Collections.emptySet()));

		// #res!base != 0
		final var baseNotEqualZeroExpr = baseNotEqualZeroExpr(tuLoc, resultExpr, zeroNumericValueExpr);
		expressions.add(new Pair<>(baseNotEqualZeroExpr, Collections.emptySet()));

		if (memoryArea == MemoryArea.STACK) {
			// #StackHeapBarrier < res!base
			final var baseGreaterThanBarrierExpr = baseGreaterThanBarrier(tuLoc, stackHeapBarrierExpr, resultExpr);
			expressions.add(new Pair<>(baseGreaterThanBarrierExpr, Collections.emptySet()));
		} else if (memoryArea == MemoryArea.HEAP) {
			// res!base < #StackHeapBarrier
			final var baseSmallerThanBarrierExpr = baseSmallerThanBarrier(tuLoc, stackHeapBarrierExpr, resultExpr);
			expressions.add(new Pair<>(baseSmallerThanBarrierExpr, Collections.emptySet()));
		}

		// #length == old(#length)[#res!base := ~size]
		final var lengthUpdateExpr =
				ExpressionFactory
						.newBinaryExpression(tuLoc, Operator.COMPEQ, lengthArrayExpr,
								ExpressionFactory.constructArrayStoreExpression(
										tuLoc, ExpressionFactory.constructUnaryExpression(tuLoc,
												UnaryExpression.Operator.OLD, lengthArrayExpr),
										new Expression[] { resBaseExpr }, sizeExpr));
		expressions.add(new Pair<>(lengthUpdateExpr,
				Collections.singleton((VariableLHS) CTranslationUtil.convertExpressionToLHS(lengthArrayExpr))));

		return expressions;
	}

	@Override
	public List<Triple<Expression, Set<VariableLHS>, Boolean>> constructDeallocSpecificationExpressions(
			final ILocation tuLoc, final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {

		final var falseExpr = mBooleanArrayHelper.constructFalse();
		final var validArrayExpr =
				mMemoryMetadata.getValidArray(tuLoc, requiredMemoryModelFeatures, memoryModelDeclarationsHandler);

		final Expression addrExpr =
				ExpressionFactory.constructIdentifierExpression(tuLoc, mTypeHandler.getBoogiePointerType(), SFO.ADDR,
						new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM,
								MemoryModelDeclarations.ULTIMATE_DEALLOC.getName()));
		final Expression addrBaseExpr =
				ExpressionFactory.constructStructAccessExpression(tuLoc, addrExpr, SFO.POINTER_BASE);

		// #valid == old(#valid)[~addr!base := 0]
		final ArrayStoreExpression arrayStoreExpr = ExpressionFactory.constructArrayStoreExpression(tuLoc,
				ExpressionFactory.constructUnaryExpression(tuLoc, UnaryExpression.Operator.OLD, validArrayExpr),
				new Expression[] { addrBaseExpr }, falseExpr);

		final Expression updateValidArrayExpr =
				ExpressionFactory.newBinaryExpression(tuLoc, Operator.COMPEQ, validArrayExpr, arrayStoreExpr);

		return Collections.singletonList(new Triple<>(updateValidArrayExpr,
				Collections.singleton((VariableLHS) CTranslationUtil.convertExpressionToLHS(validArrayExpr)), true));
	}

	@Override
	public List<Statement> constructUltimateInitStatements(final ILocation loc,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler, final BigInteger fixedAddressCounter) {
		final var cTypeOfPointerComponent = mExpressionTranslation.getCTypeOfPointerComponents();

		final List<Statement> statements = new ArrayList<>();
		// TODO 20211115 Matthias: added the following assume-base initialization for
		// #valid[0] == 0. I presume that the assignment-case initialization is not
		// needed in any approach and can be dropped.
		if (true) {
			// assume #valid[0] == 0 (i.e., the memory at the NULL-pointer is
			// not allocated)
			final Expression zero =
					mTypeSizes.constructLiteralForIntegerType(loc, cTypeOfPointerComponent, BigInteger.ZERO);
			final Expression literalThatRepresentsFalse = mBooleanArrayHelper.constructFalse();
			final Expression eq = ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ,
					ExpressionFactory.constructNestedArrayAccessExpression(loc,
							mMemoryMetadata.getValidArray(loc, requiredMemoryModelFeatures,
									memoryModelDeclarationsHandler),
							new Expression[] { zero }),
					literalThatRepresentsFalse);
			final AssumeStatement assume = new AssumeStatement(loc, eq);
			statements.add(assume);
		} else {
			// set #valid[0] = 0 (i.e., the memory at the NULL-pointer is
			// not allocated)
			final Expression zero =
					mTypeSizes.constructLiteralForIntegerType(loc, cTypeOfPointerComponent, BigInteger.ZERO);
			final Expression literalThatRepresentsFalse = mBooleanArrayHelper.constructFalse();
			final AssignmentStatement assignment = MemoryHandler.constructOneDimensionalArrayUpdate(loc, zero,
					mMemoryMetadata.getValidArrayLhs(loc, requiredMemoryModelFeatures, memoryModelDeclarationsHandler),
					literalThatRepresentsFalse);

			statements.add(assignment);
		}

		// Add assume(0 < #StackHeapBarrier) to ensure that the null
		// pointer is on the heap.
		final Expression zero =
				mTypeSizes.constructLiteralForIntegerType(loc, cTypeOfPointerComponent, BigInteger.ZERO);
		final Expression zeroSmallerStackHeapBarrier =
				mExpressionTranslation.constructBinaryComparisonIntegerExpression(
						loc, IASTBinaryExpression.op_lessThan, zero, cTypeOfPointerComponent, MemoryMetadataBase
								.getStackHeapBarrier(loc, requiredMemoryModelFeatures, memoryModelDeclarationsHandler),
						cTypeOfPointerComponent);

		statements.add(new AssumeStatement(loc, zeroSmallerStackHeapBarrier));

		return statements;
	}

	@Override
	public List<Pair<Expression, Set<VariableLHS>>> constructAllocInitSpecificationExpressions(final ILocation tuLoc,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		final var pointerBaseIdentifier = "ptrBase";
		final var procedureIdentifier = MemoryModelDeclarations.ULTIMATE_ALLOC_INIT.getName();

		final var trueExpr = mBooleanArrayHelper.constructTrue();
		final var validArrayExpr =
				mMemoryMetadata.getValidArray(tuLoc, requiredMemoryModelFeatures, memoryModelDeclarationsHandler);
		final var lengthArrayExpr =
				mMemoryMetadata.getLengthArray(tuLoc, requiredMemoryModelFeatures, memoryModelDeclarationsHandler);
		final var size = ExpressionFactory.constructIdentifierExpression(tuLoc, mTypeHandler.getBoogieTypeForSizeT(),
				SFO.SIZE, new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, procedureIdentifier));

		final var ptrBase = ExpressionFactory.constructIdentifierExpression(tuLoc,
				mTypeHandler.getBoogieTypeForPointerComponents(), pointerBaseIdentifier,
				new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, procedureIdentifier));

		final ArrayList<Pair<Expression, Set<VariableLHS>>> expressions = new ArrayList<>();
		// ensures #valid[ptrBase] == true;
		final var validPtrBaseExpr =
				MemoryModelExpressionHelper.ensuresArrayHasValue(tuLoc, trueExpr, ptrBase, validArrayExpr);
		expressions.add(new Pair<>(validPtrBaseExpr, Collections.emptySet()));

		// ensures #length[ptrBase] == size;
		final var lengthPtrBaseSize =
				MemoryModelExpressionHelper.ensuresArrayHasValue(tuLoc, size, ptrBase, lengthArrayExpr);
		expressions.add(new Pair<>(lengthPtrBaseSize, Collections.emptySet()));

		return expressions;
	}

}
