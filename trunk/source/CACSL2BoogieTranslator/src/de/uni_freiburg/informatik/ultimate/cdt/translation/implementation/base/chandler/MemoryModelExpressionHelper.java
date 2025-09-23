package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

public class MemoryModelExpressionHelper {
	public static void requireMemoryModelFeature(final MemoryModelDeclarations mmDecl,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		requiredMemoryModelFeatures.require(mmDecl);
		memoryModelDeclarationsHandler.createMemoryModelDeclarationInfo(mmDecl);
	}

	public static VariableLHS getMemoryModelFeatureLhs(final ILocation loc, final MemoryModelDeclarations decl,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		requireMemoryModelFeature(decl, requiredMemoryModelFeatures, memoryModelDeclarationsHandler);
		final MemoryModelDeclarationInfo mmdi = memoryModelDeclarationsHandler.memoryModelDeclarationInfo(decl);
		return mmdi.constructVariableLHS(loc);
	}

	public static Expression getMemoryModelFeatureExpression(final ILocation loc, final MemoryModelDeclarations decl,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		requireMemoryModelFeature(decl, requiredMemoryModelFeatures, memoryModelDeclarationsHandler);
		final MemoryModelDeclarationInfo mmdi = memoryModelDeclarationsHandler.memoryModelDeclarationInfo(decl);
		return mmdi.constructIdentifierExpression(loc);
	}

	public static Expression constructOneDimensionalArrayAccess(final ILocation loc, final Expression arr,
			final Expression index) {
		final Expression[] singletonIndex = { index };
		return ExpressionFactory.constructNestedArrayAccessExpression(loc, arr, singletonIndex);
	}

	private static Expression constructOneDimensionalArrayStore(final ILocation loc, final Expression arr,
			final Expression index, final Expression newValue) {
		final Expression[] singletonIndex = { index };
		return ExpressionFactory.constructArrayStoreExpression(loc, arr, singletonIndex, newValue);
	}

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

	// ensures #memory_X == old(#memory_X)[#ptr := #value];
	public static Expression constructHeapArrayUpdateForWriteEnsures(final ILocation loc,
			final List<Expression> valueExprs, final List<Expression> ptrExprs, final HeapDataArray hda,
			final boolean useSelectInsteadOfStore) {
		final Expression memArray = hda.getIdentifierExpression();
		if (useSelectInsteadOfStore) {
			return ensuresArrayHasValues(loc, valueExprs, ptrExprs, memArray);
		}
		return ensuresArrayNestedUpdate(loc, valueExprs, ptrExprs, memArray);
	}

	// #memory_$Pointer$ == old(#memory_X)[#ptr := #memory_X[#ptr]];
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
	 * arr == old(arr)[index := newValue]
	 */
	public static Expression ensuresArrayUpdate(final ILocation loc, final Expression newValue, final Expression index,
			final Expression arrayExpr) {
		final Expression oldArray =
				ExpressionFactory.constructUnaryExpression(loc, UnaryExpression.Operator.OLD, arrayExpr);
		final Expression ase = constructOneDimensionalArrayStore(loc, oldArray, index, newValue);
		return ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, arrayExpr, ase);
	}

	private static Expression ensuresArrayNestedUpdate(final ILocation loc, final List<Expression> newValues,
			final List<Expression> indices, final Expression arrayExpr) {
		final Expression oldArray =
				ExpressionFactory.constructUnaryExpression(loc, UnaryExpression.Operator.OLD, arrayExpr);
		final Expression ase = constructNestedOneDimensionalArrayStore(loc, oldArray, indices, newValues);
		return ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, arrayExpr, ase);
	}

	/**
	 * arr[index] == value
	 */
	public static Expression ensuresArrayHasValue(final ILocation loc, final Expression value, final Expression index,
			final Expression arrayExpr) {
		final Expression select =
				ExpressionFactory.constructNestedArrayAccessExpression(loc, arrayExpr, new Expression[] { index });
		return ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, select, value);
	}

	private static Expression ensuresArrayHasValues(final ILocation loc, final List<Expression> values,
			final List<Expression> indices, final Expression arrayExpr) {
		final List<Expression> conjuncts = new ArrayList<>();
		for (int i = 0; i < values.size(); i++) {
			conjuncts.add(ensuresArrayHasValue(loc, values.get(i), indices.get(i), arrayExpr));
		}
		return ExpressionFactory.and(loc, conjuncts);
	}
}
