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

import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * Abstract base class providing common functionality for memory metadata implementations.
 *
 * This class stores references to essential components such as type handling, expression translation, and boolean array
 * helpers, and provides utility methods related to memory model barriers.
 *
 * @author Jan Körner
 */
public abstract class MemoryMetadataBase implements IMemoryMetadata {
	protected final ITypeHandler mTypeHandler;
	protected final ExpressionTranslation mExpressionTranslation;
	protected final IBooleanArrayHelper mBooleanArrayHelper;

	/**
	 * Constructs a new instance with the specified type handler, expression translation, and boolean array helper.
	 *
	 * @param typeHandler
	 *            The type handler for managing data types.
	 * @param expressionTranslation
	 *            The translator for converting expressions.
	 * @param booleanArrayHelper
	 *            Helper for boolean array operations.
	 */
	public MemoryMetadataBase(final ITypeHandler typeHandler, final ExpressionTranslation expressionTranslation,
			final IBooleanArrayHelper booleanArrayHelper) {
		mTypeHandler = typeHandler;
		mExpressionTranslation = expressionTranslation;
		mBooleanArrayHelper = booleanArrayHelper;
	}

	/**
	 * Constructs a variable declaration representing the stack/heap barrier constant used in the representation of
	 * memory models.
	 *
	 * @return The variable declaration for the stack/heap barrier.
	 */
	protected VariableDeclaration constructStackHeapBarrierConstant() {
		final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
		return new VariableDeclaration(ignoreLoc, new Attribute[0],
				new VarList[] { new VarList(ignoreLoc,
						new String[] { MemoryModelDeclarations.ULTIMATE_STACK_HEAP_BARRIER.getName() },
						mTypeHandler.cType2AstType(ignoreLoc, mExpressionTranslation.getCTypeOfPointerComponents())) });
	}

	/**
	 * Retrieves the expression representing the stack/heap barrier in the memory model.
	 *
	 * @param loc
	 *            The location context.
	 * @param requiredMemoryModelFeatures
	 *            The features required for verification.
	 * @param memoryModelDeclarationsHandler
	 *            Handler for managing memory model declarations.
	 * @return The expression corresponding to the stack/heap barrier.
	 */
	public static Expression getStackHeapBarrier(final ILocation loc,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		return MemoryModelExpressionHelper.getMemoryModelFeatureExpression(loc,
				MemoryModelDeclarations.ULTIMATE_STACK_HEAP_BARRIER, requiredMemoryModelFeatures,
				memoryModelDeclarationsHandler);
	}
}
