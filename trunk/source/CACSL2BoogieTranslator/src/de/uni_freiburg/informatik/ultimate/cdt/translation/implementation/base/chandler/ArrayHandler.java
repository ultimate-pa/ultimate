/*
 * Copyright (C) 2013-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
import java.util.Arrays;

import org.eclipse.cdt.core.dom.ast.IASTArraySubscriptExpression;
import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.HeapLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check.Spec;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.PointerCheckMode;

/**
 * Class that handles translation of arrays.
 *
 * @author Markus Lindenmann, Matthias Heizmann
 * @date 12.10.2012
 */
public class ArrayHandler {

	private final PointerCheckMode mCheckArrayAccessOffHeap;

	public ArrayHandler(final IPreferenceProvider prefs) {
		mCheckArrayAccessOffHeap =
				prefs.getEnum(CACSLPreferenceInitializer.LABEL_CHECK_ARRAYACCESSOFFHEAP, PointerCheckMode.class);
	}

	/**
	 * Handle array subscript expression according to Sections 6.5.2.1 of C11. For a[i] we will <b>not</b> return the
	 * object a[i] as an {@link RValue} instead, we return the address of the object a[i] as a {@link HeapLValue} or a
	 * {@link LocalLValue}.
	 */
	public ExpressionResult handleArraySubscriptExpression(final Dispatcher main, final MemoryHandler memoryHandler,
			final StructHandler structHandler, final IASTArraySubscriptExpression node) {
		final ILocation loc = main.getLocationFactory().createCLocation(node);

		ExpressionResult subscript = (ExpressionResult) main.dispatch(node.getArgument());
		subscript = subscript.switchToRValueIfNecessary(main, loc);
		subscript.rexBoolToIntIfNecessary(loc, ((CHandler) main.mCHandler).getExpressionTranslation());
		assert subscript.mLrVal.getCType().isIntegerType();

		ExpressionResult leftExpRes = ((ExpressionResult) main.dispatch(node.getArrayExpression()));

		final ExpressionResult result;
		final CType cTypeLeft = leftExpRes.mLrVal.getCType();
		if (cTypeLeft instanceof CPointer) {
			// if p is a pointer, then p[42] is equivalent to *(p + 42)
			leftExpRes = leftExpRes.switchToRValueIfNecessary(main, loc);
			assert cTypeLeft.equals(leftExpRes.mLrVal.getCType());
			final Expression oldAddress = leftExpRes.mLrVal.getValue();
			final RValue integer = (RValue) subscript.mLrVal;
			final CType valueType = ((CPointer) cTypeLeft).pointsToType;
			final ExpressionResult newAddress_ER = ((CHandler) main.mCHandler).doPointerArithmeticWithConversion(main,
					IASTBinaryExpression.op_plus, loc, oldAddress, integer, valueType);
			final Expression newAddress = newAddress_ER.mLrVal.getValue();
			result = ExpressionResult.copyStmtDeclAuxvarOverapprox(leftExpRes, subscript);
			final HeapLValue lValue = new HeapLValue(newAddress, valueType, false, null);
			result.addAll(newAddress_ER);
			result.mLrVal = lValue;
		} else {
			assert cTypeLeft.getUnderlyingType() instanceof CArray : "cType not instanceof CArray";
			final CArray cArray = (CArray) cTypeLeft.getUnderlyingType();

			// The result type will be an array where the first dimension is
			// missing. E.g., if the input is a (int x int -> float) array
			// the resulting array will be an (int -> float) array.
			assert cArray.getDimensions().length != 1 || isOutermostSubscriptExpression(node) : "not outermost";

			final CType resultCType = popOneDimension(cArray);

			if (leftExpRes.mLrVal instanceof HeapLValue) {
				// If the left hand side is an array represented as HeapLValue
				// we use pointer arithmetic to compute the result.
				// E.g., a[23] becomes addressOf(a) + 23 * sizeof(valueType)
				// Note that the computation is not trivial if the array is
				// multidimensional. Let's assume we have an array whose
				// declaration is a[3][5][7] and we are processing the innermost
				// of a nested subscript expression a[2].
				// Then the resulting address will be
				// addressOf(a) + 2 * 5 * 7 * sizeof(valueType)
				// We achieve this by doing pointer arithmetic where we use
				// the "remaining" array as pointsToType, i.e., we compute
				// addressOf(a) + 2 * sizeof(resultCType)
				final Expression oldAddress = ((HeapLValue) leftExpRes.mLrVal).getAddress();
				final RValue index = (RValue) subscript.mLrVal;
				final ExpressionResult newAddress_ER = ((CHandler) main.mCHandler).doPointerArithmeticWithConversion(
						main, IASTBinaryExpression.op_plus, loc, oldAddress, index, resultCType);
				final Expression newAddress = newAddress_ER.mLrVal.getValue();
				final HeapLValue lValue = new HeapLValue(newAddress, resultCType, false, null);
				result = ExpressionResult.copyStmtDeclAuxvarOverapprox(leftExpRes, subscript);
				result.addAll(newAddress_ER);
				result.mLrVal = lValue;
			} else if (leftExpRes.mLrVal instanceof LocalLValue) {
				// If the left hand side is an array represented as LocalLValue
				// we return a copy of this LocalLValue where we added the
				// current index.
				final LeftHandSide oldInnerArrayLHS = ((LocalLValue) leftExpRes.mLrVal).getLHS();
				final RValue currentDimension = cArray.getDimensions()[0];
				// The following is not in the standard, since there everything
				// is defined via pointers. However, we have to make the subscript
				// compatible to the type of the dimension of the array
				final ExpressionTranslation et = ((CHandler) main.mCHandler).getExpressionTranslation();
				et.convertIntToInt(loc, subscript, (CPrimitive) currentDimension.getCType());
				final RValue index = (RValue) subscript.mLrVal;
				final ArrayLHS newInnerArrayLHS;
				if (oldInnerArrayLHS instanceof ArrayLHS) {
					final Expression[] oldIndices = ((ArrayLHS) oldInnerArrayLHS).getIndices();
					final Expression[] newIndices = new Expression[oldIndices.length + 1];
					System.arraycopy(oldIndices, 0, newIndices, 0, oldIndices.length);
					newIndices[newIndices.length - 1] = index.getValue();
					newInnerArrayLHS = ExpressionFactory.constructNestedArrayLHS(loc,
							((ArrayLHS) oldInnerArrayLHS).getArray(), newIndices);
				} else {
					assert isInnermostSubscriptExpression(node) : "not innermost";
					newInnerArrayLHS = ExpressionFactory.constructNestedArrayLHS(loc, oldInnerArrayLHS,
							new Expression[] { index.getValue() });
				}
				final LocalLValue lValue = new LocalLValue(newInnerArrayLHS, resultCType, false, false, null);
				result = ExpressionResult.copyStmtDeclAuxvarOverapprox(leftExpRes, subscript);
				result.mLrVal = lValue;
				addArrayBoundsCheckForCurrentIndex(main, loc, index, currentDimension, result);
			} else {
				throw new AssertionError("result.lrVal has to be either HeapLValue or LocalLValue");
			}
		}

		return result;
	}

	public static CType popOneDimension(final CArray cArray) {
		final CType resultCType;
		if (cArray.getDimensions().length == 1) {
			resultCType = cArray.getValueType();
		} else {
			final RValue[] newDimensions =
					Arrays.copyOfRange(cArray.getDimensions(), 1, cArray.getDimensions().length);
			assert newDimensions.length == cArray.getDimensions().length - 1;
			resultCType = new CArray(newDimensions, cArray.getValueType());
		}
		return resultCType;
	}

	/**
	 * Add to exprResult a check that the index is within the bounds of an array. Depending on the preferences of this
	 * plugin we
	 * <ul>
	 * <li>assert that the index is in the range of the bounds,
	 * <li>assume that the index is in the range of the bounds, or
	 * <li>add nothing.
	 * </ul>
	 * For multidimensional arrays, this check has to be done separately for each index. This simple check ignores the
	 * typesize of the value, compares only the index with the dimension and is hence only applicable if the array is
	 * represented as a {@link LocalLValue}.
	 *
	 * @param currentIndex
	 *            {@link Expression} that represents the index
	 * @param currentDimension
	 *            {@link Expression} that represents the dimension that corresponds to the index
	 */
	private void addArrayBoundsCheckForCurrentIndex(final Dispatcher main, final ILocation loc,
			final RValue currentIndex, final RValue currentDimension, final ExpressionResult exprResult) {
		if (mCheckArrayAccessOffHeap == PointerCheckMode.IGNORE) {
			// do not check anything
			return;
		}
		final CHandler cHandler = (CHandler) main.mCHandler;
		final Expression inRange;
		// 2015-09-21 Matthias:
		// This check will fail in the bitvector translation if the typesize
		// of the index is different than the typesize of the dimension.
		// as a workaround we assume int for both.
		// 2015-10-24 Matthias:
		// Probably solved. Now the input is already converted to the type
		// of the dimension.
		{
			final CPrimitive indexType = (CPrimitive) currentIndex.getCType();
			final Expression zero =
					cHandler.getExpressionTranslation().constructLiteralForIntegerType(loc, indexType, BigInteger.ZERO);
			final Expression nonNegative = cHandler.getExpressionTranslation().constructBinaryComparisonExpression(loc,
					IASTBinaryExpression.op_lessEqual, zero, indexType, currentIndex.getValue(), indexType);
			final Expression notTooBig = cHandler.getExpressionTranslation().constructBinaryComparisonExpression(loc,
					IASTBinaryExpression.op_lessThan, currentIndex.getValue(), indexType, currentDimension.getValue(),
					(CPrimitive) currentDimension.getCType());
			inRange = ExpressionFactory.newBinaryExpression(loc, Operator.LOGICAND, nonNegative, notTooBig);
		}
		switch (mCheckArrayAccessOffHeap) {
		case ASSERTandASSUME:
			final Statement assertStm = new AssertStatement(loc, inRange);
			final Check chk = new Check(Spec.ARRAY_INDEX);
			chk.annotate(assertStm);
			exprResult.mStmt.add(assertStm);
			break;
		case ASSUME:
			final Statement assumeStm = new AssumeStatement(loc, inRange);
			exprResult.mStmt.add(assumeStm);
			break;
		case IGNORE:
			throw new AssertionError("case handled before");
		default:
			throw new AssertionError("unknown value");
		}

	}

	private static boolean isInnermostSubscriptExpression(final IASTArraySubscriptExpression node) {
		return !(node.getArrayExpression() instanceof IASTArraySubscriptExpression);
	}

	private static boolean isOutermostSubscriptExpression(final IASTArraySubscriptExpression node) {
		return !(node.getParent() instanceof IASTArraySubscriptExpression);
	}

}