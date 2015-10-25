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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler;

import java.math.BigInteger;
import java.util.Arrays;

import org.eclipse.cdt.core.dom.ast.IASTArraySubscriptExpression;
import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.ExpressionTranslation.AExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.PRIMITIVE;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.HeapLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.POINTER_CHECKMODE;
import de.uni_freiburg.informatik.ultimate.result.Check;
import de.uni_freiburg.informatik.ultimate.result.Check.Spec;

/**
 * Class that handles translation of arrays.
 * 
 * @author Markus Lindenmann, Matthias Heizmann
 * @date 12.10.2012
 */
public class ArrayHandler {
	
	private POINTER_CHECKMODE m_checkArrayAccessOffHeap;

	public ArrayHandler() {
		UltimatePreferenceStore ups = new UltimatePreferenceStore(Activator.s_PLUGIN_ID);
		m_checkArrayAccessOffHeap = 
				ups.getEnum(CACSLPreferenceInitializer.LABEL_CHECK_ARRAYACCESSOFFHEAP, POINTER_CHECKMODE.class);
	}

	/**
	 * Handle array subscript expression according to Sections 6.5.2.1 of C11.
	 * For a[i] we will <b>not</b> return the object a[i] as an {@link RValue}
	 * instead, we return the address of the object a[i] as a {@link HeapLValue}
	 * or a {@link LocalLValue}.
	 */
	public ExpressionResult handleArraySubscriptExpression(Dispatcher main,
			MemoryHandler memoryHandler, StructHandler structHandler,
			IASTArraySubscriptExpression node) {		
		final ILocation loc = LocationFactory.createCLocation(node);
		
		ExpressionResult subscript = (ExpressionResult) main.dispatch(node.getArgument());
		subscript = subscript.switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);
		assert subscript.lrVal.getCType().isIntegerType();
		ExpressionResult leftExpRes = ((ExpressionResult) main.dispatch(node.getArrayExpression()));
		
		final ExpressionResult result;
		final CType cTypeLeft = leftExpRes.lrVal.getCType();
		if (cTypeLeft instanceof CPointer) {
			// if p is a pointer, then p[42] is equivalent to *(p + 42)
			assert (isInnermostSubscriptExpression(node) && isOutermostSubscriptExpression(node))
					: "in this case nested subscript expressions are impossible"; 
			leftExpRes = leftExpRes.switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);
			assert cTypeLeft.equals(leftExpRes.lrVal.getCType());
			Expression oldAddress = leftExpRes.lrVal.getValue();
			RValue integer = (RValue) subscript.lrVal;
			CType valueType = ((CPointer) cTypeLeft).pointsToType;;
			ExpressionResult newAddress_ER = ((CHandler) main.cHandler).doPointerArithmeticWithConversion(main, 
					IASTBinaryExpression.op_plus, loc, oldAddress, integer, valueType);
			Expression newAddress = newAddress_ER.lrVal.getValue();
			result = ExpressionResult.copyStmtDeclAuxvarOverapprox(leftExpRes, subscript);
			HeapLValue lValue = new HeapLValue(newAddress, valueType, false);
			result.addAll(newAddress_ER);
			result.lrVal = lValue;
		} else {
			assert cTypeLeft.getUnderlyingType() instanceof CArray : "cType not instanceof CArray";
			final CArray cArray = (CArray) cTypeLeft.getUnderlyingType();

			// The result type will be an array where the first dimension is
			// missing. E.g., if the input is a (int x int -> float) array
			// the resulting array will be an (int -> float) array.
			final CType resultCType;
			if (cArray.getDimensions().length == 1) {
				assert isOutermostSubscriptExpression(node) : "not outermost";
				resultCType = cArray.getValueType();
			} else {
				RValue[] newDimensions = Arrays.copyOfRange(
						cArray.getDimensions(), 1, cArray.getDimensions().length);
				assert newDimensions.length == cArray.getDimensions().length - 1;
				resultCType = new CArray(newDimensions, cArray.getValueType());
			}

			if (leftExpRes.lrVal instanceof HeapLValue) {
				// If the left hand side is an array represented as HeapLValue
				// we use pointer arithmetic to compute the result.
				// E.g., a[23] becomes addressOf(a) + 23 * sizeof(valueType)
				// Note that the computation is not trivial if the array is
				// multidimensional. Let's assume we have an array whose 
				// declaration is a[3][5][7] and we are processing the innermost
				// of a nested subscript expression a[2].
				// Then the resulting address will be 
				//     addressOf(a) + 2 * 5 * 7 * sizeof(valueType)
				// We achieve this by doing pointer arithmetic where we use
				// the "remaining" array as pointsToType, i.e., we compute
				//     addressOf(a) + 2 * sizeof(resultCType)
				Expression oldAddress = ((HeapLValue) leftExpRes.lrVal).getAddress();
				RValue index = (RValue) subscript.lrVal;
				ExpressionResult newAddress_ER = ((CHandler) main.cHandler).doPointerArithmeticWithConversion(
						main, IASTBinaryExpression.op_plus, loc, oldAddress, index,	resultCType);
				Expression newAddress = newAddress_ER.lrVal.getValue();
				HeapLValue lValue = new HeapLValue(newAddress, resultCType, false);
				result = ExpressionResult.copyStmtDeclAuxvarOverapprox(leftExpRes, subscript);
				result.addAll(newAddress_ER);
				result.lrVal = lValue;
			} else if (leftExpRes.lrVal instanceof LocalLValue) {
				// If the left hand side is an array represented as LocalLValue
				// we return a copy of this LocalLValue where we added the
				// current index.
				final LeftHandSide oldInnerArrayLHS = ((LocalLValue) leftExpRes.lrVal).getLHS();
				RValue currentDimension = cArray.getDimensions()[0];
				// The following is not in the standard, since there everything 
				// is defined via pointers. However, we have to make the subscript
				// compatible to the type of the dimension of the array
				AExpressionTranslation et = ((CHandler) main.cHandler).getExpressionTranslation();
				et.convert(loc, subscript, (CPrimitive) currentDimension.getCType());
				final RValue index = (RValue) subscript.lrVal;
				final ArrayLHS newInnerArrayLHS;
				if (oldInnerArrayLHS instanceof ArrayLHS) {
					Expression[] oldIndices = ((ArrayLHS) oldInnerArrayLHS).getIndices();
					Expression[] newIndices = new Expression[oldIndices.length + 1];
					System.arraycopy(oldIndices, 0, newIndices, 0, oldIndices.length);
					newIndices[newIndices.length-1] = index.getValue();
					newInnerArrayLHS = new ArrayLHS(loc, 
							((ArrayLHS) oldInnerArrayLHS).getArray(), newIndices);
				} else {
					assert isInnermostSubscriptExpression(node) : "not innermost";
					newInnerArrayLHS = new ArrayLHS(loc, oldInnerArrayLHS, new Expression[] { index.getValue() });	
				}
				LocalLValue lValue = new LocalLValue(newInnerArrayLHS, resultCType, false, false);
				result = ExpressionResult.copyStmtDeclAuxvarOverapprox(leftExpRes, subscript);
				result.lrVal = lValue;
				addArrayBoundsCheckForCurrentIndex(main, loc, index, currentDimension, result);
			} else {
				throw new AssertionError("result.lrVal has to be either HeapLValue or LocalLValue");
			}
		}
		
		return result;
	}
	
	/**
	 * Add to exprResult a check that the index is within the bounds of an array.
	 * Depending on the preferences of this plugin we
	 * <ul> 
	 *  <li> assert that the index is in the range of the bounds,
	 *  <li> assume that the index is in the range of the bounds, or
	 *  <li> add nothing.
	 * </ul>
	 * For multidimensional arrays, this check has to be done separately for
	 * each index.
	 * This simple check ignores the typesize of the value, compares only
	 * the index with the dimension and is hence only applicable if the
	 * array is represented as a {@link LocalLValue}.
	 * @param currentIndex {@link Expression} that represents the index
	 * @param currentDimension {@link Expression} that represents the dimension
	 * 		that corresponds to the index
	 */
	private void addArrayBoundsCheckForCurrentIndex(Dispatcher main, 
			ILocation loc, RValue currentIndex,
			RValue currentDimension, ExpressionResult exprResult) {
		if (m_checkArrayAccessOffHeap  == POINTER_CHECKMODE.IGNORE) {
			// do not check anything
			return;
		}
		CHandler cHandler = (CHandler) main.cHandler;
		final Expression inRange;
		// 2015-09-21 Matthias:
		// This check will fail in the bitvector translation if the typesize 
		// of the index is different than the typesize of the dimension.
		// as a workaround we assume int for both.
		// 2015-10-24 Matthias:
		// Probably solved. Now the input is already converted to the type
		// of the dimension.
		{
			CPrimitive indexType = (CPrimitive) currentIndex.getCType();
			Expression zero = cHandler.getExpressionTranslation().constructLiteralForIntegerType(
					loc, indexType, BigInteger.ZERO);
			Expression nonNegative = cHandler.getExpressionTranslation().constructBinaryComparisonExpression(
					loc, IASTBinaryExpression.op_lessEqual, zero, indexType, 
					currentIndex.getValue(), indexType);
			Expression notTooBig = cHandler.getExpressionTranslation().constructBinaryComparisonExpression(
					loc, IASTBinaryExpression.op_lessThan, currentIndex.getValue(), indexType, 
					currentDimension.getValue(), (CPrimitive) currentDimension.getCType());
			inRange = new BinaryExpression(loc, Operator.LOGICAND, nonNegative, notTooBig);
		}
		switch (m_checkArrayAccessOffHeap) {
		case ASSERTandASSUME:
			Statement assertStm = new AssertStatement(loc, inRange);
			Check chk = new Check(Spec.ARRAY_INDEX);
			chk.addToNodeAnnot(assertStm);
			exprResult.stmt.add(assertStm);
			break;
		case ASSUME:
			Statement assumeStm = new AssumeStatement(loc, inRange);
			exprResult.stmt.add(assumeStm);
			break;
		case IGNORE:
			throw new AssertionError("case handled before");
		default:
			throw new AssertionError("unknown value");
		}
		
	}

	private boolean isInnermostSubscriptExpression(IASTArraySubscriptExpression node) {
		return !(node.getArrayExpression() instanceof IASTArraySubscriptExpression);
	}
	
	private boolean isOutermostSubscriptExpression(IASTArraySubscriptExpression node) {
		return !(node.getParent() instanceof IASTArraySubscriptExpression);
	}
	
}