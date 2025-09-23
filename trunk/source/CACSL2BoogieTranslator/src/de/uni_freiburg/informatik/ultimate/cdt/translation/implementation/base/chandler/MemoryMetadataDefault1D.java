package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

public class MemoryMetadataDefault1D extends MemoryMetadataBase {
	public MemoryMetadataDefault1D(final ITypeHandler typeHandler, final ExpressionTranslation expressionTranslation,
			final IBooleanArrayHelper booleanArrayHelper) {
		super(typeHandler, expressionTranslation, booleanArrayHelper);
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

	/**
	 * Returns the #StackAllocations expression.
	 *
	 * @return The expression.
	 */
	public static Expression getStackAllocCounter(final ILocation loc,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		return MemoryModelExpressionHelper.getMemoryModelFeatureExpression(loc,
				MemoryModelDeclarations.ULTIMATE_STACK_ALLOCATIONS, requiredMemoryModelFeatures,
				memoryModelDeclarationsHandler);
	}

	/**
	 * Returns the #HeapAllocations expression.
	 *
	 * @return The expression.
	 */
	public static Expression getHeapAllocCounter(final ILocation loc,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		return MemoryModelExpressionHelper.getMemoryModelFeatureExpression(loc,
				MemoryModelDeclarations.ULTIMATE_HEAP_ALLOCATIONS, requiredMemoryModelFeatures,
				memoryModelDeclarationsHandler);
	}

	/**
	 * Returns the #InitialAllocations expression.
	 *
	 * @return The expression.
	 */
	public static Expression getInitialAllocCounter(final ILocation loc,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		return MemoryModelExpressionHelper.getMemoryModelFeatureExpression(loc,
				MemoryModelDeclarations.ULTIMATE_INITIAL_ALLOCATIONS, requiredMemoryModelFeatures,
				memoryModelDeclarationsHandler);
	}

}
