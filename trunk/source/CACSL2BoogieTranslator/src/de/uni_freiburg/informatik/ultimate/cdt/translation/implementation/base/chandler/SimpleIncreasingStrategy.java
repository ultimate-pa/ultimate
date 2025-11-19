/*
 * Copyright (C) 2025 Jan Körner
 * Copyright (C) 2025 University of Freiburg
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
 * This strategy is the default strategy for the 1D-memory addressing scheme. The generic parameter is used to ensure
 * that this strategy is only instanciated within the 1D addressing class because it is not compatible with other modes.
 * Memory addresses are increased with every allocation.
 *
 * @author Jan Körner
 */
public class SimpleIncreasingStrategy extends MemoryManagementStrategyBase {
	private final boolean mIsBitVectorTranslation;

	public SimpleIncreasingStrategy(final TypeSizes typeSizes, final ExpressionTranslation expressionTranslation,
			final ITypeHandler typeHandler, final TypeSizeAndOffsetComputer typeSizeAndOffsetComputer,
			final boolean isBitVectorTranslation) {
		super(typeSizes, expressionTranslation, typeHandler, typeSizeAndOffsetComputer);
		mIsBitVectorTranslation = isBitVectorTranslation;
	}

	@Override
	public List<Pair<Expression, Set<VariableLHS>>> constructMallocSpecificationExpressions(final ILocation tuLoc,
			final MemoryArea memoryArea, final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		final var cTypeOfPointerComponent = mExpressionTranslation.getCTypeOfPointerComponents();

		final ArrayList<Pair<Expression, Set<VariableLHS>>> expressions = new ArrayList<>();

		final var memoryAreaName = memoryArea.getMemoryStructureDeclaration().getName();
		final var zeroNumericValueExpr =
				mTypeSizes.constructLiteralForIntegerType(tuLoc, cTypeOfPointerComponent, BigInteger.ZERO);
		final var resultExpr =
				ExpressionFactory.constructIdentifierExpression(tuLoc, mTypeHandler.getBoogiePointerType(), SFO.RES,
						new DeclarationInformation(StorageClass.PROC_FUNC_OUTPARAM, memoryAreaName));

		final var resBaseExpr = ExpressionFactory.constructStructAccessExpression(tuLoc, resultExpr, SFO.POINTER_BASE);

		final var counterExpression = memoryArea == MemoryArea.STACK
				? MemoryMetadataDefault1D.getStackAllocCounter(tuLoc, requiredMemoryModelFeatures,
						memoryModelDeclarationsHandler)
				: MemoryMetadataDefault1D.getHeapAllocCounter(tuLoc, requiredMemoryModelFeatures,
						memoryModelDeclarationsHandler);

		final var stackHeapBarrierExpr = MemoryMetadataBase.getStackHeapBarrier(tuLoc, requiredMemoryModelFeatures,
				memoryModelDeclarationsHandler);

		final var initialAllocCounterExpr = MemoryMetadataDefault1D.getInitialAllocCounter(tuLoc,
				requiredMemoryModelFeatures, memoryModelDeclarationsHandler);

		final var sizeExpr =
				ExpressionFactory.constructIdentifierExpression(tuLoc, mTypeHandler.getBoogieTypeForSizeT(), SFO.SIZE,
						new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, memoryAreaName));

		// #res!base == old(counterExpression);
		final var baseEqualCounterExpr = ExpressionFactory.newBinaryExpression(tuLoc, Operator.COMPEQ, resBaseExpr,
				ExpressionFactory.constructUnaryExpression(tuLoc, UnaryExpression.Operator.OLD, counterExpression));
		expressions.add(new Pair<>(baseEqualCounterExpr, Collections.emptySet()));

		// #res!base > 0;
		final var baseGreaterZeroExpr = mExpressionTranslation.constructBinaryComparisonIntegerExpression(tuLoc,
				IASTBinaryExpression.op_greaterThan,
				ExpressionFactory.constructStructAccessExpression(tuLoc, resultExpr, SFO.POINTER_BASE),
				cTypeOfPointerComponent, zeroNumericValueExpr, cTypeOfPointerComponent);

		expressions.add(new Pair<>(baseGreaterZeroExpr, Collections.emptySet()));

		if (memoryArea == MemoryArea.STACK) {
			// res!base > #StackHeapBarrier
			final var baseGreaterThanBarrierExpr = baseGreaterThanBarrier(tuLoc, stackHeapBarrierExpr, resultExpr);
			expressions.add(new Pair<>(baseGreaterThanBarrierExpr, Collections.emptySet()));

			// #StackAllocations > #StackHeapBarrier;
			final var stackAllocationsGreaterThanBarrier = mExpressionTranslation
					.constructBinaryComparisonIntegerExpression(tuLoc, IASTBinaryExpression.op_greaterThan,
							counterExpression, cTypeOfPointerComponent, stackHeapBarrierExpr, cTypeOfPointerComponent);
			expressions.add(new Pair<>(stackAllocationsGreaterThanBarrier, Collections.emptySet()));

			// #StackAllocations < #32-bit max / 64-bit max
			if (mIsBitVectorTranslation) {
				final var pointerSize = mTypeSizes.getSizeOfPointer();
				final int bits = pointerSize * 8;

				// max signed = 2^(bits - 1) - 1
				final var max = BigInteger.valueOf(2).pow(bits - 1).subtract(BigInteger.ONE);
				final var maxExpr =
						mExpressionTranslation.constructLiteralForIntegerType(tuLoc, cTypeOfPointerComponent, max);

				final var stackAllocationsSmallerThanMax = mExpressionTranslation
						.constructBinaryComparisonIntegerExpression(tuLoc, IASTBinaryExpression.op_lessThan,
								counterExpression, cTypeOfPointerComponent, maxExpr, cTypeOfPointerComponent);

				expressions.add(new Pair<>(stackAllocationsSmallerThanMax, Collections.emptySet()));
			}

		} else if (memoryArea == MemoryArea.HEAP) {
			// res!base < #StackHeapBarrier
			final var baseSmallerThanBarrierExpr = baseSmallerThanBarrier(tuLoc, stackHeapBarrierExpr, resultExpr);
			expressions.add(new Pair<>(baseSmallerThanBarrierExpr, Collections.emptySet()));

			// #HeapAllocations < #StackHeapBarrier;
			final var stackAllocationsGreaterThanBarrier = mExpressionTranslation
					.constructBinaryComparisonIntegerExpression(tuLoc, IASTBinaryExpression.op_lessThan,
							counterExpression, cTypeOfPointerComponent, stackHeapBarrierExpr, cTypeOfPointerComponent);
			expressions.add(new Pair<>(stackAllocationsGreaterThanBarrier, Collections.emptySet()));
		}

		// res!base > #InitialAllocation
		final var baseGreaterThanInitialAllocsExpr = mExpressionTranslation.constructBinaryComparisonIntegerExpression(
				tuLoc, IASTBinaryExpression.op_greaterThan,
				ExpressionFactory.constructStructAccessExpression(tuLoc, resultExpr, SFO.POINTER_BASE),
				cTypeOfPointerComponent, initialAllocCounterExpr, cTypeOfPointerComponent);
		expressions.add(new Pair<>(baseGreaterThanInitialAllocsExpr, Collections.emptySet()));

		// StackAllocations == old(StackAllocations) + ~size
		// HeapAllocations == old(HeapAllocations) + ~size
		final var oldExpr =
				ExpressionFactory.constructUnaryExpression(tuLoc, UnaryExpression.Operator.OLD, counterExpression);
		final var sumExpr = mExpressionTranslation.constructArithmeticExpression(tuLoc, IASTBinaryExpression.op_plus,
				oldExpr, cTypeOfPointerComponent, sizeExpr, mTypeSizeAndOffsetComputer.getSizeT());
		final var counterUpdateValueExpr =
				ExpressionFactory.newBinaryExpression(tuLoc, Operator.COMPEQ, counterExpression, sumExpr);

		expressions.add(new Pair<>(counterUpdateValueExpr,
				Collections.singleton((VariableLHS) CTranslationUtil.convertExpressionToLHS(counterExpression))));

		return expressions;
	}

	@Override
	public List<Triple<Expression, Set<VariableLHS>, Boolean>> constructDeallocSpecificationExpressions(
			final ILocation tuLoc, final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		return Collections.emptyList();
	}

	@Override
	public List<Statement> constructUltimateInitStatements(final ILocation loc,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler, final BigInteger fixedAddressCounter) {
		final List<Statement> stmts = new ArrayList<>();

		final var cTypeOfPointerComponent = mExpressionTranslation.getCTypeOfPointerComponents();

		final var initialAllocationsExpr = MemoryMetadataDefault1D.getInitialAllocCounter(loc,
				requiredMemoryModelFeatures, memoryModelDeclarationsHandler);

		// Add assume(fixedAddressCounter == #InitialAllocations)
		final Expression fixedAddressCounterExpr =
				mTypeSizes.constructLiteralForIntegerType(loc, cTypeOfPointerComponent, fixedAddressCounter);

		final Expression initialAllocCounterEqualsFixedAddressCounterExpr =
				mExpressionTranslation.constructBinaryComparisonIntegerExpression(loc, IASTBinaryExpression.op_equals,
						fixedAddressCounterExpr, cTypeOfPointerComponent, initialAllocationsExpr,
						cTypeOfPointerComponent);

		stmts.add(new AssumeStatement(loc, initialAllocCounterEqualsFixedAddressCounterExpr));

		// Add assume(#StackHeapBarrier > #InitialAllocations)
		final var stackHeapBarrierExpr = MemoryMetadataBase.getStackHeapBarrier(loc, requiredMemoryModelFeatures,
				memoryModelDeclarationsHandler);

		final Expression barrierGreaterThanInitialAllocationsExpr = mExpressionTranslation
				.constructBinaryComparisonIntegerExpression(loc, IASTBinaryExpression.op_greaterThan,
						stackHeapBarrierExpr, cTypeOfPointerComponent, initialAllocationsExpr, cTypeOfPointerComponent);

		stmts.add(new AssumeStatement(loc, barrierGreaterThanInitialAllocationsExpr));
		return stmts;
	}

	@Override
	public List<Pair<Expression, Set<VariableLHS>>> constructAllocInitSpecificationExpressions(final ILocation tuLoc,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		return Collections.emptyList();
	}

}
