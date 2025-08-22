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
 * This strategy is the default strategy for the 1D-memory addressing mode. The generic parameter is used to ensure that
 * this strategy is only instanciated within the 1D addressing class because it is not compatible with other modes.
 * Memory addresses are increased with every allocation.
 */
public class SimpleIncreasingStrategy<T extends OneDimensionalMemoryAddressing> extends BaseMemoryManagementStrategy {
	T mMemoryAddressing;

	public SimpleIncreasingStrategy(final TypeSizes typeSizes, final ExpressionTranslation expressionTranslation,
			final ITypeHandler typeHandler, final TypeSizeAndOffsetComputer typeSizeAndOffsetComputer,
			final T addressing) {
		super(typeSizes, expressionTranslation, typeHandler, typeSizeAndOffsetComputer);
		mMemoryAddressing = addressing;
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
				? MemoryModelExpressionHelper.getStackAllocCounter(tuLoc, requiredMemoryModelFeatures,
						memoryModelDeclarationsHandler)
				: MemoryModelExpressionHelper.getHeapAllocCounter(tuLoc, requiredMemoryModelFeatures,
						memoryModelDeclarationsHandler);

		final var stackHeapBarrierExpr = MemoryModelExpressionHelper.getStackHeapBarrier(tuLoc,
				requiredMemoryModelFeatures, memoryModelDeclarationsHandler);

		final var initialAllocCounterExpr = MemoryModelExpressionHelper.getInitialAllocCounter(tuLoc,
				requiredMemoryModelFeatures, memoryModelDeclarationsHandler);

		final var sizeExpr =
				ExpressionFactory.constructIdentifierExpression(tuLoc, mTypeHandler.getBoogieTypeForSizeT(), SFO.SIZE,
						new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, memoryAreaName));

		// #res!base == old(counterExpression);
		final var baseEqualCounterExpr = ExpressionFactory.newBinaryExpression(tuLoc, Operator.COMPEQ, resBaseExpr,
				ExpressionFactory.constructUnaryExpression(tuLoc, UnaryExpression.Operator.OLD, counterExpression));
		expressions.add(new Pair<>(baseEqualCounterExpr, Collections.emptySet()));

		// #res!base != 0;
		final var baseNotEqualZeroExpr = baseNotEqualZeroExpr(tuLoc, resultExpr, zeroNumericValueExpr);
		expressions.add(new Pair<>(baseNotEqualZeroExpr, Collections.emptySet()));

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

		} else if (memoryArea == MemoryArea.HEAP) {
			// res!base < #StackHeapBarrier
			final var baseSmallerThanBarrierExpr = baseSmallerThanBarrier(tuLoc, stackHeapBarrierExpr, resultExpr);
			expressions.add(new Pair<>(baseSmallerThanBarrierExpr, Collections.emptySet()));

			// res!base > #InitialAllocation
			final var baseGreaterThanInitialAllocsExpr = mExpressionTranslation
					.constructBinaryComparisonIntegerExpression(tuLoc, IASTBinaryExpression.op_greaterThan,
							ExpressionFactory.constructStructAccessExpression(tuLoc, resultExpr, SFO.POINTER_BASE),
							cTypeOfPointerComponent, initialAllocCounterExpr, cTypeOfPointerComponent);
			expressions.add(new Pair<>(baseGreaterThanInitialAllocsExpr, Collections.emptySet()));

			// #HeapAllocations < #StackHeapBarrier;
			final var stackAllocationsGreaterThanBarrier = mExpressionTranslation
					.constructBinaryComparisonIntegerExpression(tuLoc, IASTBinaryExpression.op_lessThan,
							counterExpression, cTypeOfPointerComponent, stackHeapBarrierExpr, cTypeOfPointerComponent);
			expressions.add(new Pair<>(stackAllocationsGreaterThanBarrier, Collections.emptySet()));
		}

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

		final var cTypeOfPointerComponent = mExpressionTranslation.getCTypeOfPointerComponents();

		// Add assume(fixedAddressCounter == #InitialAllocations)
		final Expression fixedAddressCounterExpr =
				mTypeSizes.constructLiteralForIntegerType(loc, cTypeOfPointerComponent, fixedAddressCounter);

		final Expression initialAllocCounterEqualsFixedAddressCounterExpr =
				mExpressionTranslation.constructBinaryComparisonIntegerExpression(loc, IASTBinaryExpression.op_equals,
						fixedAddressCounterExpr, cTypeOfPointerComponent,
						MemoryModelExpressionHelper.getInitialAllocCounter(loc, requiredMemoryModelFeatures,
								memoryModelDeclarationsHandler),
						cTypeOfPointerComponent);

		final Statement statement = new AssumeStatement(loc, initialAllocCounterEqualsFixedAddressCounterExpr);

		return Collections.singletonList(statement);
	}

	@Override
	public List<Pair<Expression, Set<VariableLHS>>> constructAllocInitSpecificationExpressions(final ILocation tuLoc,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		return Collections.emptyList();
	}

}
