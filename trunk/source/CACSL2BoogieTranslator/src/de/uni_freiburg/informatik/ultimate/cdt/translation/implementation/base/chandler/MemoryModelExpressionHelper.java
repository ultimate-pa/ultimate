/*
 * Copyright (C) 2013-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2025 Jan Körner
 * Copyright (C) 2015-2025 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * Utility class providing helper methods for constructing memory model expressions, especially for handling memory
 * features, array accesses and updates.
 *
 * @author Jan Körner
 */
public class MemoryModelExpressionHelper {

	/**
	 * Ensures that the specified memory model feature is required and creates its necessary declaration information.
	 *
	 * @param mmDecl
	 *            The memory model declaration to require.
	 * @param requiredMemoryModelFeatures
	 *            The required memory model features.
	 * @param memoryModelDeclarationsHandler
	 *            Handler for managing memory model declarations.
	 */
	public static void requireMemoryModelFeature(final MemoryModelDeclarations mmDecl,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		requiredMemoryModelFeatures.require(mmDecl);
		memoryModelDeclarationsHandler.createMemoryModelDeclarationInfo(mmDecl);
	}

	/**
	 * Retrieves the left-hand side (LHS) variable for a memory model feature.
	 *
	 * @param loc
	 *            The location context.
	 * @param decl
	 *            The memory model declaration.
	 * @param requiredMemoryModelFeatures
	 *            The required memory model features.
	 * @param memoryModelDeclarationsHandler
	 *            Handler for managing memory model declarations.
	 * @return The variable corresponding to the memory model feature.
	 */
	public static VariableLHS getMemoryModelFeatureLhs(final ILocation loc, final MemoryModelDeclarations decl,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		requireMemoryModelFeature(decl, requiredMemoryModelFeatures, memoryModelDeclarationsHandler);
		final MemoryModelDeclarationInfo mmdi = memoryModelDeclarationsHandler.memoryModelDeclarationInfo(decl);
		return mmdi.constructVariableLHS(loc);
	}

	/**
	 * Constructs an expression representing the memory model feature at a given location.
	 *
	 * @param loc
	 *            The location context.
	 * @param decl
	 *            The memory model declaration.
	 * @param requiredMemoryModelFeatures
	 *            The required memory model features.
	 * @param memoryModelDeclarationsHandler
	 *            Handler for managing memory model declarations.
	 * @return The expression representing the memory model feature.
	 */
	public static Expression getMemoryModelFeatureExpression(final ILocation loc, final MemoryModelDeclarations decl,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		requireMemoryModelFeature(decl, requiredMemoryModelFeatures, memoryModelDeclarationsHandler);
		final MemoryModelDeclarationInfo mmdi = memoryModelDeclarationsHandler.memoryModelDeclarationInfo(decl);
		return mmdi.constructIdentifierExpression(loc);
	}

	/**
	 * Constructs an expression for accessing a one-dimensional array element.
	 *
	 * Represents {@code arr[index]}.
	 *
	 * @param loc
	 *            The location context.
	 * @param arr
	 *            The array expression.
	 * @param index
	 *            The index expression.
	 * @return The array access expression.
	 */
	public static Expression constructOneDimensionalArrayAccess(final ILocation loc, final Expression arr,
			final Expression index) {
		final Expression[] singletonIndex = { index };
		return ExpressionFactory.constructNestedArrayAccessExpression(loc, arr, singletonIndex);
	}

	/**
	 * Constructs an expression for storing a value into a one-dimensional array at a specific index.
	 *
	 * Represents {@code arr[index := newValue]}.
	 *
	 * @param loc
	 *            The location context.
	 * @param arr
	 *            The array expression.
	 * @param index
	 *            The index expression.
	 * @param newValue
	 *            The value to store.
	 * @return The array store expression.
	 */
	private static Expression constructOneDimensionalArrayStore(final ILocation loc, final Expression arr,
			final Expression index, final Expression newValue) {
		final Expression[] singletonIndex = { index };
		return ExpressionFactory.constructArrayStoreExpression(loc, arr, singletonIndex, newValue);
	}

	/**
	 * Constructs nested array store expressions for multiple indices and values.
	 *
	 * @param loc
	 *            The location context.
	 * @param arr
	 *            The initial array expression.
	 * @param indices
	 *            List of index expressions.
	 * @param newValues
	 *            List of new value expressions corresponding to each index.
	 * @return The nested array store expression updating multiple indices.
	 */
	private static Expression constructNestedOneDimensionalArrayStore(final ILocation loc, final Expression arr,
			final List<Expression> indices, final List<Expression> newValues) {
		assert indices.size() == newValues.size();
		Expression result = arr;
		for (int i = 0; i < indices.size(); i++) {
			final Expression[] singletonIndex = { indices.get(i) };
			result = ExpressionFactory.constructArrayStoreExpression(loc, result, singletonIndex, newValues.get(i));
		}
		return result;
	}

	/**
	 * Constructs an expression ensuring that the memory array's value after a write operation matches the expected
	 * value.
	 *
	 * Represents {@code #memory_X == old(#memory_X)[ptr := value]}.
	 *
	 * @param loc
	 *            The location context.
	 * @param valueExprs
	 *            List of value expressions to write.
	 * @param ptrExprs
	 *            List of pointer expressions.
	 * @param hda
	 *            The heap data array.
	 * @param useSelectInsteadOfStore
	 *            Flag to determine whether to use select or store operation.
	 * @return The constructed ensures expression.
	 */
	public static Expression constructHeapArrayUpdateForWriteEnsures(final ILocation loc,
			final List<Expression> valueExprs, final List<Expression> ptrExprs, final HeapDataArray hda,
			final boolean useSelectInsteadOfStore) {
		final Expression memArray = hda.getIdentifierExpression();
		if (useSelectInsteadOfStore) {
			return ensuresArrayHasValues(loc, valueExprs, ptrExprs, memArray);
		}
		return ensuresArrayNestedUpdate(loc, valueExprs, ptrExprs, memArray);
	}

	/**
	 * Constructs an expression representing that the heap array has been hardly modified for a write operation, meaning
	 * the array remains mostly unchanged except at specific indices.
	 *
	 * Represents {@code #memory_X == old(#memory_X)[#ptr := #memory_X[#ptr]]}.
	 *
	 * @param loc
	 *            The location context.
	 * @param idxExprs
	 *            List of index expressions.
	 * @param hda
	 *            The heap data array.
	 * @return The ensures expression representing minimal modification.
	 */
	public static Expression constructHeapArrayHardlyModifiedForWriteEnsures(final ILocation loc,
			final List<Expression> idxExprs, final HeapDataArray hda) {
		final Expression memArray = hda.getIdentifierExpression();
		final List<Expression> newNondetValues = new ArrayList<>();
		for (int i = 0; i < idxExprs.size(); i++) {
			newNondetValues.add(constructOneDimensionalArrayAccess(loc, memArray, idxExprs.get(i)));
		}
		// final Expression memArray = hda.getIdentifierExpression();
		// final Expression aae = constructOneDimensionalArrayAccess(loc, memArray, ptrExpr);
		return ensuresArrayNestedUpdate(loc, newNondetValues, idxExprs, memArray);
	}

	/**
	 * Creates an expression asserting that the array equals its old value with an update at a specific index.
	 *
	 * Represents {@code arr == old(arr)[index := newValue]}.
	 *
	 * @param loc
	 *            The location context.
	 * @param newValue
	 *            The new value to assign.
	 * @param index
	 *            The index at which to assign.
	 * @param arrayExpr
	 *            The array expression.
	 * @return The equality expression ensuring the update.
	 */
	public static Expression ensuresArrayUpdate(final ILocation loc, final Expression newValue, final Expression index,
			final Expression arrayExpr) {
		final Expression oldArray =
				ExpressionFactory.constructUnaryExpression(loc, UnaryExpression.Operator.OLD, arrayExpr);
		final Expression ase = constructOneDimensionalArrayStore(loc, oldArray, index, newValue);
		return ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, arrayExpr, ase);
	}

	/**
	 * Constructs an expression asserting that the array equals its old value with multiple updates at specified
	 * indices.
	 *
	 * @param loc
	 *            The location context.
	 * @param newValues
	 *            List of new value expressions.
	 * @param indices
	 *            List of index expressions.
	 * @param arrayExpr
	 *            The array expression.
	 * @return The equality expression representing nested updates.
	 */
	private static Expression ensuresArrayNestedUpdate(final ILocation loc, final List<Expression> newValues,
			final List<Expression> indices, final Expression arrayExpr) {
		final Expression oldArray =
				ExpressionFactory.constructUnaryExpression(loc, UnaryExpression.Operator.OLD, arrayExpr);
		final Expression ase = constructNestedOneDimensionalArrayStore(loc, oldArray, indices, newValues);
		return ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, arrayExpr, ase);
	}

	/**
	 * Creates an expression asserting that the array element at a given index equals a specific value.
	 *
	 * Represents {@code arr[index] == value}.
	 *
	 * @param loc
	 *            The location context.
	 * @param value
	 *            The value to compare.
	 * @param index
	 *            The index to access.
	 * @param arrayExpr
	 *            The array expression.
	 * @return The equality expression.
	 */
	public static Expression ensuresArrayHasValue(final ILocation loc, final Expression value, final Expression index,
			final Expression arrayExpr) {
		final Expression select =
				ExpressionFactory.constructNestedArrayAccessExpression(loc, arrayExpr, new Expression[] { index });
		return ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, select, value);
	}

	/**
	 * Constructs an expression asserting that multiple array elements at specified indices have expected values.
	 *
	 * @param loc
	 *            The location context.
	 * @param values
	 *            List of value expressions.
	 * @param indices
	 *            List of index expressions.
	 * @param arrayExpr
	 *            The array expression.
	 * @return A conjunction of all individual array element value assertions.
	 */
	private static Expression ensuresArrayHasValues(final ILocation loc, final List<Expression> values,
			final List<Expression> indices, final Expression arrayExpr) {
		final List<Expression> conjuncts = new ArrayList<>();
		for (int i = 0; i < values.size(); i++) {
			conjuncts.add(ensuresArrayHasValue(loc, values.get(i), indices.get(i), arrayExpr));
		}
		return ExpressionFactory.and(loc, conjuncts);
	}
}
