/*
 * Copyright (C) 2013-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2025 Jan Körner
 * Copyright (C) 2012-2025 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */
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

/**
 * This strategy is the default strategy for the 2D-memory addressing scheme. The generic parameter is used to ensure
 * that this strategy is only instantiated within the 2D addressing class because it is not compatible with other modes.
 * Memory addresses get a non-deterministic value, which is not used yet.
 *
 * @author Jan Körner
 */
public class NonDetStrategy2D<T extends MemoryAddressing2D> extends MemoryManagementStrategyBase {
	private final IBooleanArrayHelper mBooleanArrayHelper;
	private final T mMemoryAddressing;

	public NonDetStrategy2D(final TypeSizes typeSizes, final ExpressionTranslation expressionTranslation,
			final ITypeHandler typeHandler, final TypeSizeAndOffsetComputer typeSizeAndOffsetComputer,
			final IBooleanArrayHelper booleanArrayHelper, final T addressing) {
		super(typeSizes, expressionTranslation, typeHandler, typeSizeAndOffsetComputer);

		mBooleanArrayHelper = booleanArrayHelper;
		mMemoryAddressing = addressing;
	}

	@Override
	public AllocationProcedureSpec constructMallocSpecification(final ILocation tuLoc, final MemoryArea memoryArea,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {

		final var memoryAreaName = memoryArea.getMemoryStructureDeclaration().getName();
		final var falseExpr = mBooleanArrayHelper.constructFalse();
		final var trueExpr = mBooleanArrayHelper.constructTrue();

		final var validArrayExpr = MemoryMetadataDefault2D.getValidArray(tuLoc, requiredMemoryModelFeatures,
				memoryModelDeclarationsHandler);
		final var stackHeapBarrierExpr = MemoryMetadataBase.getStackHeapBarrier(tuLoc, requiredMemoryModelFeatures,
				memoryModelDeclarationsHandler);
		final var lengthArrayExpr = MemoryMetadataDefault2D.getLengthArray(tuLoc, requiredMemoryModelFeatures,
				memoryModelDeclarationsHandler);

		final var zeroNumericValueExpr = mTypeSizes.constructLiteralForIntegerType(tuLoc,
				mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ZERO);
		final var resultExpr =
				ExpressionFactory.constructIdentifierExpression(tuLoc, mTypeHandler.getBoogiePointerType(), SFO.RES,
						new DeclarationInformation(StorageClass.PROC_FUNC_OUTPARAM, memoryAreaName));

		final var sizeExpr =
				ExpressionFactory.constructIdentifierExpression(tuLoc, mTypeHandler.getBoogieTypeForSizeT(), SFO.SIZE,
						new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, memoryAreaName));

		final var resBaseExpr = ExpressionFactory.constructStructAccessExpression(tuLoc, resultExpr, SFO.POINTER_BASE);

		final ArrayList<Expression> expressions = new ArrayList<>();

		// old(#valid)[#res!base] == false
		final var freshLocationCurrentlyNotValidExpr = ExpressionFactory.newBinaryExpression(tuLoc, Operator.COMPEQ,
				ExpressionFactory.constructNestedArrayAccessExpression(tuLoc,
						ExpressionFactory.constructUnaryExpression(tuLoc, UnaryExpression.Operator.OLD, validArrayExpr),
						new Expression[] { resBaseExpr }),
				falseExpr);
		expressions.add(freshLocationCurrentlyNotValidExpr);

		// #valid == old(#valid)[#res!base := true]
		final var validUpdateExpr =
				MemoryModelExpressionHelper.ensuresArrayUpdate(tuLoc, trueExpr, resBaseExpr, validArrayExpr);
		expressions.add(validUpdateExpr);

		// #res!offset == 0
		final var offsetEqualZeroExpr = ExpressionFactory.newBinaryExpression(tuLoc, Operator.COMPEQ,
				mMemoryAddressing.mMemoryPointer.pointerOffset(resultExpr, tuLoc), zeroNumericValueExpr);
		expressions.add(offsetEqualZeroExpr);

		// #res!base != 0
		final var baseNotEqualZeroExpr = baseNotEqualZeroExpr(tuLoc, resultExpr, zeroNumericValueExpr);
		expressions.add(baseNotEqualZeroExpr);

		if (memoryArea == MemoryArea.STACK) {
			// #StackHeapBarrier < res!base
			final var baseGreaterThanBarrierExpr = baseGreaterThanBarrier(tuLoc, stackHeapBarrierExpr, resultExpr);
			expressions.add(baseGreaterThanBarrierExpr);
		} else if (memoryArea == MemoryArea.HEAP) {
			// res!base < #StackHeapBarrier
			final var baseSmallerThanBarrierExpr = baseSmallerThanBarrier(tuLoc, stackHeapBarrierExpr, resultExpr);
			expressions.add(baseSmallerThanBarrierExpr);
		}

		// #length == old(#length)[#res!base := ~size]
		final var lengthUpdateExpr =
				ExpressionFactory
						.newBinaryExpression(tuLoc, Operator.COMPEQ, lengthArrayExpr,
								ExpressionFactory.constructArrayStoreExpression(
										tuLoc, ExpressionFactory.constructUnaryExpression(tuLoc,
												UnaryExpression.Operator.OLD, lengthArrayExpr),
										new Expression[] { resBaseExpr }, sizeExpr));
		expressions.add(lengthUpdateExpr);

		final var validArrayLHS = (VariableLHS) CTranslationUtil.convertExpressionToLHS(validArrayExpr);
		final var lengthArrayLHS = (VariableLHS) CTranslationUtil.convertExpressionToLHS(lengthArrayExpr);
		return new AllocationProcedureSpec(expressions, Set.of(validArrayLHS, lengthArrayLHS));
	}

	@Override
	public AllocationProcedureSpec constructDeallocSpecification(final ILocation tuLoc,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {

		final var falseExpr = mBooleanArrayHelper.constructFalse();
		final var validArrayExpr = MemoryMetadataDefault2D.getValidArray(tuLoc, requiredMemoryModelFeatures,
				memoryModelDeclarationsHandler);

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

		return new AllocationProcedureSpec(Collections.emptyList(), List.of(updateValidArrayExpr),
				Collections.singleton((VariableLHS) CTranslationUtil.convertExpressionToLHS(validArrayExpr)));
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
							MemoryMetadataDefault2D.getValidArray(loc, requiredMemoryModelFeatures,
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
					MemoryMetadataDefault2D.getValidArrayLhs(loc, requiredMemoryModelFeatures,
							memoryModelDeclarationsHandler),
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
	public AllocationProcedureSpec constructAllocInitSpecification(final ILocation tuLoc,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		final var pointerBaseIdentifier = "ptrBase";
		final var procedureIdentifier = MemoryModelDeclarations.ULTIMATE_ALLOC_INIT.getName();

		final var trueExpr = mBooleanArrayHelper.constructTrue();
		final var validArrayExpr = MemoryMetadataDefault2D.getValidArray(tuLoc, requiredMemoryModelFeatures,
				memoryModelDeclarationsHandler);
		final var lengthArrayExpr = MemoryMetadataDefault2D.getLengthArray(tuLoc, requiredMemoryModelFeatures,
				memoryModelDeclarationsHandler);
		final var size = ExpressionFactory.constructIdentifierExpression(tuLoc, mTypeHandler.getBoogieTypeForSizeT(),
				SFO.SIZE, new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, procedureIdentifier));

		final var ptrBase = ExpressionFactory.constructIdentifierExpression(tuLoc,
				mTypeHandler.getBoogieTypeForPointerComponents(), pointerBaseIdentifier,
				new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, procedureIdentifier));

		// ensures #valid[ptrBase] == true;
		final var validPtrBaseExpr =
				MemoryModelExpressionHelper.ensuresArrayHasValue(tuLoc, trueExpr, ptrBase, validArrayExpr);

		// ensures #length[ptrBase] == size;
		final var lengthPtrBaseSize =
				MemoryModelExpressionHelper.ensuresArrayHasValue(tuLoc, size, ptrBase, lengthArrayExpr);

		return new AllocationProcedureSpec(List.of(validPtrBaseExpr, lengthPtrBaseSize), Collections.emptySet());
	}

}
