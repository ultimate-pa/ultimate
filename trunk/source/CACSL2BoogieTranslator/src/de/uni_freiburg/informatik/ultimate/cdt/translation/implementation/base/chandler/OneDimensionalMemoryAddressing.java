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
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CTranslationUtil;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * The one dimensional memory addressing.
 */
public class OneDimensionalMemoryAddressing extends BaseMemoryAdressing {
	public OneDimensionalMemoryAddressing(final ITypeHandler typeHandler, final ExpressionTranslation exprTranslation,
			final IBooleanArrayHelper booleanArrayHelper, final TypeSizes typeSizes) {
		super(typeHandler, exprTranslation, booleanArrayHelper, typeSizes);
	}

	@Override
	public List<Declaration> constructMetaData(final RequiredMemoryModelFeatures requiredFeatures) {
		final var metaDataDeclarations = new ArrayList<Declaration>();

		if (requiredFeatures.getRequiredMemoryStructureDeclarations()
				.contains(MemoryModelDeclarations.ULTIMATE_INITIAL_ALLOCATIONS)) {
			metaDataDeclarations.add(constructInitialAllocationsConstant());
		}

		if (requiredFeatures.getRequiredMemoryStructureDeclarations()
				.contains(MemoryModelDeclarations.ULTIMATE_STACK_ALLOCATIONS)) {
			metaDataDeclarations.add(constructStackAllocationsVariable());
		}

		if (requiredFeatures.getRequiredMemoryStructureDeclarations()
				.contains(MemoryModelDeclarations.ULTIMATE_HEAP_ALLOCATIONS)) {
			metaDataDeclarations.add(constructHeapAllocationsVariable());
		}

		if (requiredFeatures.getRequiredMemoryStructureDeclarations()
				.contains(MemoryModelDeclarations.ULTIMATE_STACK_HEAP_BARRIER)) {
			metaDataDeclarations.add(constructStackHeapBarrierConstant());
		}

		return metaDataDeclarations;
	}

	/**
	 * Constructs the declaration of the constant that holds the count of all initial allocations.
	 *
	 * @return The declaration.
	 */
	private VariableDeclaration constructInitialAllocationsConstant() {
		final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
		return new VariableDeclaration(ignoreLoc, new Attribute[0],
				new VarList[] { new VarList(ignoreLoc,
						new String[] { MemoryModelDeclarations.ULTIMATE_INITIAL_ALLOCATIONS.getName() },
						mTypeHandler.cType2AstType(ignoreLoc, mExpressionTranslation.getCTypeOfPointerComponents())) });
	}

	/**
	 * Constructs the declaration of the variable holding the count of stack allocations.
	 *
	 * @return The declaration.
	 */
	private VariableDeclaration constructStackAllocationsVariable() {
		final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
		return new VariableDeclaration(ignoreLoc, new Attribute[0],
				new VarList[] { new VarList(ignoreLoc,
						new String[] { MemoryModelDeclarations.ULTIMATE_STACK_ALLOCATIONS.getName() },
						mTypeHandler.cType2AstType(ignoreLoc, mExpressionTranslation.getCTypeOfPointerComponents())) });
	}

	/**
	 * Constructs the declaration of the variable holding the count of heap allocations.
	 *
	 * @return The declaration.
	 */
	private VariableDeclaration constructHeapAllocationsVariable() {
		final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
		return new VariableDeclaration(ignoreLoc, new Attribute[0],
				new VarList[] { new VarList(ignoreLoc,
						new String[] { MemoryModelDeclarations.ULTIMATE_HEAP_ALLOCATIONS.getName() },
						mTypeHandler.cType2AstType(ignoreLoc, mExpressionTranslation.getCTypeOfPointerComponents())) });
	}

	@Override
	public List<MemoryModelDeclarations> metaDataDeclarations() {
		return List.of(MemoryModelDeclarations.ULTIMATE_INITIAL_ALLOCATIONS,
				MemoryModelDeclarations.ULTIMATE_STACK_ALLOCATIONS, MemoryModelDeclarations.ULTIMATE_HEAP_ALLOCATIONS);
	}

	@Override
	public List<Pair<Expression, Set<VariableLHS>>> constructMallocSpecificationExpressions(final ILocation tuLoc,
			final MemoryArea memoryArea, final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		final ArrayList<Pair<Expression, Set<VariableLHS>>> expressions = new ArrayList<>();

		final var memoryAreaName = memoryArea.getMemoryStructureDeclaration().getName();
		final var zeroNumericValueExpr = mTypeSizes.constructLiteralForIntegerType(tuLoc,
				mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ZERO);
		final var resultExpr =
				ExpressionFactory.constructIdentifierExpression(tuLoc, mTypeHandler.getBoogiePointerType(), SFO.RES,
						new DeclarationInformation(StorageClass.PROC_FUNC_OUTPARAM, memoryAreaName));

		final var resBaseExpr = ExpressionFactory.constructStructAccessExpression(tuLoc, resultExpr, SFO.POINTER_BASE);

		final var counterExpression = memoryArea == MemoryArea.STACK
				? MemoryModelExpressionHelper.getStackAllocCounter(tuLoc, requiredMemoryModelFeatures,
						memoryModelDeclarationsHandler)
				: MemoryModelExpressionHelper.getStackAllocCounter(tuLoc, requiredMemoryModelFeatures,
						memoryModelDeclarationsHandler);

		final var stackHeapBarrierExpr = MemoryModelExpressionHelper.getStackHeapBarrier(tuLoc,
				requiredMemoryModelFeatures, memoryModelDeclarationsHandler);

		final var initialAllocCounterExpr = MemoryModelExpressionHelper.getInitialAllocCounter(tuLoc,
				requiredMemoryModelFeatures, memoryModelDeclarationsHandler);

		final var sizeExpr =
				ExpressionFactory.constructIdentifierExpression(tuLoc, mTypeHandler.getBoogieTypeForSizeT(), SFO.SIZE,
						new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, memoryAreaName));

		// ensures #res!base == old(counterExpression);
		final var baseEqualCounterExpr = ExpressionFactory.newBinaryExpression(tuLoc, Operator.COMPEQ, resBaseExpr,
				ExpressionFactory.constructUnaryExpression(tuLoc, UnaryExpression.Operator.OLD, counterExpression));
		expressions.add(new Pair<>(baseEqualCounterExpr, Collections.emptySet()));

		// ensures #res!offset = 0;
		final var offsetEqualZeroExpr = offsetEqualsZeroExpr(tuLoc, resultExpr, zeroNumericValueExpr);
		expressions.add(new Pair<>(offsetEqualZeroExpr, Collections.emptySet()));

		// ensures #res!base != 0;
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

			// #InitialAllocation < res!base
			final var baseGreaterThanInitialAllocsExpr = mExpressionTranslation
					.constructBinaryComparisonIntegerExpression(tuLoc, IASTBinaryExpression.op_lessThan,
							initialAllocCounterExpr, mExpressionTranslation.getCTypeOfPointerComponents(),
							ExpressionFactory.constructStructAccessExpression(tuLoc, resultExpr, SFO.POINTER_BASE),
							mExpressionTranslation.getCTypeOfPointerComponents());
			expressions.add(new Pair<>(baseGreaterThanInitialAllocsExpr, Collections.emptySet()));
		}

		// ensures StackAllocCounter == old(StackAllocCounter) + ~size
		final var counterUpdateValueExpr =
				ExpressionFactory.newBinaryExpression(tuLoc, Operator.COMPEQ, counterExpression,
						ExpressionFactory.newBinaryExpression(tuLoc, Operator.ARITHPLUS, ExpressionFactory
								.constructUnaryExpression(tuLoc, UnaryExpression.Operator.OLD, counterExpression),
								sizeExpr));
		expressions.add(new Pair<>(counterUpdateValueExpr,
				Collections.singleton((VariableLHS) CTranslationUtil.convertExpressionToLHS(counterExpression))));

		return expressions;
	}

	@Override
	public List<Pair<Expression, Set<VariableLHS>>> constructDeallocSpecificationExpressions(final ILocation tuLoc,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		return Collections.emptyList();
	}

	@Override
	public List<Statement> constructUltimateInitStatements(final ILocation loc,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		return Collections.emptyList();
	}

	@Override
	public List<Pair<Expression, Set<VariableLHS>>> constructAllocInitSpecificationExpressions(final ILocation tuLoc,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		return Collections.emptyList();
	}

}
