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

/**
 * Default implementation of memory metadata for one-dimensional memory structures.
 *
 * This class {@link MemoryMetadataBase} to provide declarations of the specific data structures and allocation
 * expressions of the metadata required by memory models with a one-dimensional memory structure.
 */
public class MemoryMetadataDefault1D extends MemoryMetadataBase {

	/**
	 * Constructs an instance of MemoryMetadataDefault1D with the specified components.
	 *
	 * @param typeHandler
	 *            Handler for managing data types.
	 * @param expressionTranslation
	 *            Translator for converting expressions.
	 * @param booleanArrayHelper
	 *            Helper for boolean array operations.
	 */
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
	public List<MemoryModelDeclarations> getMetaDataDeclarations() {
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
