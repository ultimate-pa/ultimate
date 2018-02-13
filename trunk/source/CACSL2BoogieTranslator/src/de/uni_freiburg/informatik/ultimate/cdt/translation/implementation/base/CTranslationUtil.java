/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarHelper;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStruct;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CUnion;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionListResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.HeapLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO.AUXVAR;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * Provides utility methods for the C to Boogie translation.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class CTranslationUtil {

	private CTranslationUtil() {
		// don't instantiate this utility class
	}

	public static AuxVarHelper makeAuxVarDeclaration(final ILocation loc, final Dispatcher main, final CType cType) {
		final AUXVAR auxVarType;
		if (cType instanceof CArray) {
			auxVarType = SFO.AUXVAR.ARRAYINIT;
		} else if (cType instanceof CStruct) {
			auxVarType = SFO.AUXVAR.STRUCTINIT;
		} else {
			throw new UnsupportedOperationException();
		}
		return makeAuxVarDeclaration(loc, main, cType, auxVarType);
	}

	public static AuxVarHelper makeAuxVarDeclaration(final ILocation loc, final Dispatcher main, final CType cType,
					final AUXVAR auxVarType) {
		final String id = main.mNameHandler.getTempVarUID(auxVarType, cType);
		final VariableDeclaration decl = new VariableDeclaration(loc,
				new Attribute[0],
				new VarList[] {
						new VarList(loc, new String[] { id }, main.mTypeHandler.cType2AstType(loc, cType)) });

		final VariableLHS lhs = new VariableLHS(loc, id);

		final IdentifierExpression exp = new IdentifierExpression(loc, id);

		return new AuxVarHelper(decl, lhs, exp);
	}

	public static LocalLValue constructArrayAccessLhs(final ILocation loc, final LocalLValue arrayLhsToInitialize,
			final List<Integer> arrayIndex, final ExpressionTranslation expressionTranslation) {
		final CArray cArrayType = (CArray) arrayLhsToInitialize.getCType().getUnderlyingType();

		final Expression[] index = new Expression[arrayIndex.size()];

		CArray currentArrayType = cArrayType;

		for (int i = 0; i < arrayIndex.size(); i++) {
			final CPrimitive currentIndexType = (CPrimitive) cArrayType.getBound().getCType().getUnderlyingType();
			index[i] = expressionTranslation.constructLiteralForIntegerType(loc, currentIndexType,
					new BigInteger(arrayIndex.get(i).toString()));

			final CType valueType = currentArrayType.getValueType().getUnderlyingType();
			if (valueType instanceof CArray) {
				currentArrayType = (CArray) valueType;
			} else {
				assert i == arrayIndex.size() - 1;
			}
		}

		final ArrayLHS alhs = ExpressionFactory.constructNestedArrayLHS(loc, arrayLhsToInitialize.getLHS(), index);

		return new LocalLValue(alhs, cArrayType.getValueType(), null);
	}

	public static LocalLValue constructArrayAccessLhs(final ILocation loc, final LocalLValue arrayLhsToInitialize,
			final Integer arrayIndex, final ExpressionTranslation expressionTranslation) {
		final CArray cArrayType = (CArray) arrayLhsToInitialize.getCType().getUnderlyingType();

		final CPrimitive currentIndexType = (CPrimitive) cArrayType.getBound().getCType();
		final Expression index = expressionTranslation.constructLiteralForIntegerType(loc, currentIndexType,
					new BigInteger(arrayIndex.toString()));

		final ArrayLHS alhs = ExpressionFactory.constructNestedArrayLHS(loc, arrayLhsToInitialize.getLHS(), new Expression[] { index });

		final CType cellType = cArrayType.getValueType();

		return new LocalLValue(alhs, cellType, null);
	}

//	public static LRValue constructOffHeapStructAccessLhs(final ILocation loc, final LocalLValue structBaseLhs,
//			final int i) {
//		final CStruct cStructType = (CStruct) structBaseLhs.getCType().getUnderlyingType();
//		final String fieldName = cStructType.getFieldIds()[i];
//		final StructLHS lhs = ExpressionFactory.constructStructAccessLhs(loc, structBaseLhs.getLHS(), fieldName);
//		return new LocalLValue(lhs, cStructType.getFieldTypes()[i]);
//	}

//	public static HeapLValue constructOnHeapStructAccessLhs(final HeapLValue structBaseLhs, final int i) {
//		final CStruct cStructType = (CStruct) structBaseLhs.getCType();
//		// TODO
//		return null;
//	}

	public static HeapLValue constructAddressForArrayAtIndex(final ILocation loc, final Dispatcher main,
			final HeapLValue arrayBaseAddress, final List<Integer> arrayIndex, final IASTNode hook) {
		final CArray cArrayType = (CArray) arrayBaseAddress.getCType().getUnderlyingType();

		final List<Integer> arrayBounds = getConstantDimensionsOfArray(cArrayType,
				main.mCHandler.getExpressionTranslation(), hook);

		Integer product = 0;
		for (int i = 0; i < arrayIndex.size(); i++) {
			final int factor = i == arrayIndex.size() - 1 ? 1 : arrayBounds.get(i + 1);
			product = product +  factor * arrayIndex.get(i);
		}
		final CPrimitive sizeT = main.mCHandler.getTypeSizeAndOffsetComputer().getSizeT();

		final Expression flatCellNumber = main.mCHandler.getExpressionTranslation()
				.constructLiteralForIntegerType(loc, sizeT, new BigInteger(product.toString()));

		final Expression pointerBase = MemoryHandler.getPointerBaseAddress(arrayBaseAddress.getAddress(), loc);
		final Expression pointerOffset = MemoryHandler.getPointerOffset(arrayBaseAddress.getAddress(), loc);
		final Expression cellOffset = main.mCHandler.getMemoryHandler().multiplyWithSizeOfAnotherType(loc,
				cArrayType.getValueType(), flatCellNumber, sizeT, hook);
		final Expression sum = main.mCHandler.getExpressionTranslation().constructArithmeticExpression(loc,
				IASTBinaryExpression.op_plus, pointerOffset, sizeT, cellOffset, sizeT);
		final StructConstructor newPointer = MemoryHandler.constructPointerFromBaseAndOffset(pointerBase, sum, loc);

		return new HeapLValue(newPointer, cArrayType.getValueType(), null);
	}

	public static HeapLValue constructAddressForArrayAtIndex(final ILocation loc, final Dispatcher main,
			final HeapLValue arrayBaseAddress, final Integer arrayIndex, final IASTNode hook) {
		final CArray cArrayType = (CArray) arrayBaseAddress.getCType().getUnderlyingType();

		final CPrimitive pointerComponentType = main.mCHandler.getExpressionTranslation().getCTypeOfPointerComponents();

		final Expression flatCellNumber = main.mCHandler.getExpressionTranslation()
				.constructLiteralForIntegerType(loc, pointerComponentType, new BigInteger(arrayIndex.toString()));

		final Expression pointerBase = MemoryHandler.getPointerBaseAddress(arrayBaseAddress.getAddress(), loc);
		final Expression pointerOffset = MemoryHandler.getPointerOffset(arrayBaseAddress.getAddress(), loc);

		final CType cellType = cArrayType.getValueType();

		final Expression cellOffset = main.mCHandler.getMemoryHandler().multiplyWithSizeOfAnotherType(loc,
				cellType, flatCellNumber, pointerComponentType, hook);


		final Expression sum = main.mCHandler.getExpressionTranslation().constructArithmeticExpression(loc,
				IASTBinaryExpression.op_plus, pointerOffset, pointerComponentType, cellOffset, pointerComponentType);

		final StructConstructor newPointer = MemoryHandler.constructPointerFromBaseAndOffset(pointerBase, sum, loc);

		return new HeapLValue(newPointer, cellType, null);
	}

	public static HeapLValue constructAddressForStructField(final ILocation loc, final Dispatcher main,
			final HeapLValue baseAddress, final int fieldIndex, final IASTNode hook) {
		final CStruct cStructType = (CStruct) baseAddress.getCType().getUnderlyingType();

		final CPrimitive sizeT = main.mCHandler.getTypeSizeAndOffsetComputer().getSizeT();

		final Expression fieldOffset = main.mCHandler.getTypeSizeAndOffsetComputer().constructOffsetForField(
						loc, cStructType, fieldIndex, hook);

		final Expression pointerBase = MemoryHandler.getPointerBaseAddress(baseAddress.getAddress(), loc);
		final Expression pointerOffset = MemoryHandler.getPointerOffset(baseAddress.getAddress(), loc);
		final Expression sum = main.mCHandler.getExpressionTranslation().constructArithmeticExpression(loc,
				IASTBinaryExpression.op_plus, pointerOffset, sizeT, fieldOffset, sizeT);
		final StructConstructor newPointer = MemoryHandler.constructPointerFromBaseAndOffset(pointerBase, sum, loc);


		return new HeapLValue(newPointer, cStructType.getFieldTypes()[fieldIndex], null);
	}
	public static boolean isVarlengthArray(final CArray cArrayType, final ExpressionTranslation expressionTranslation,
			final IASTNode hook) {
		CArray currentArrayType = cArrayType;
		while (true) {
			if (expressionTranslation.extractIntegerValue(currentArrayType.getBound(), hook) == null) {
				// found a variable length bound
				return true;
			}
			final CType valueType = currentArrayType.getValueType().getUnderlyingType();
			if (valueType instanceof CArray) {
				currentArrayType = (CArray) valueType;
			} else {
				// reached at non-array type, found no varlength bound
				return false;
			}
		}
	}

	public static boolean isToplevelVarlengthArray(final CArray cArrayType,
			final ExpressionTranslation expressionTranslation, final IASTNode hook) {
		return expressionTranslation.extractIntegerValue(cArrayType.getBound(), hook) == null;
	}

	public static List<Integer> getConstantDimensionsOfArray(final CArray cArrayType,
			final ExpressionTranslation expressionTranslation, final IASTNode hook) {
		if (CTranslationUtil.isVarlengthArray(cArrayType, expressionTranslation, hook)) {
			throw new IllegalArgumentException("only call this for non-varlength array types");
		}
		CArray currentArrayType = cArrayType;

		final List<Integer> result = new ArrayList<>();
		while (true) {
			result.add(Integer.parseUnsignedInt(expressionTranslation.extractIntegerValue(currentArrayType.getBound(),
					hook).toString()));

			final CType valueType = currentArrayType.getValueType().getUnderlyingType();
			if (valueType instanceof CArray) {
				currentArrayType = (CArray) valueType;
			} else {
				return Collections.unmodifiableList(result);
			}
		}
	}

	public static boolean isAggregateType(final CType valueType) {
		return (valueType instanceof CStruct && !(valueType instanceof CUnion)) || valueType instanceof CArray;
	}

	public static int getConstantFirstDimensionOfArray(final CArray cArrayType,
			final ExpressionTranslation expressionTranslation, final IASTNode hook) {
		final RValue dimRVal = cArrayType.getBound();

		final BigInteger extracted = expressionTranslation.extractIntegerValue(dimRVal, hook);
		if (extracted == null) {
			throw new IllegalArgumentException("only call this for non-varlength first dimension types");
		}

		final int dimInt = Integer.parseUnsignedInt(extracted.toString());
		return dimInt;
	}

	/**
	 * The given result must be an ExpressionResult or an ExpressionListResult.
	 *  case ExpressionResult: the ExpressionResult is returned unchanged
	 *  case ExpressionListResult: we evaluate all expressions, also switching to rvalue in every case, and we
	 *    accumulate the corresponding statements in an ExpressionResult
	 *
	 * @param loc
	 * @param main
	 * @param dispatch
	 * @return
	 */
	public static ExpressionResult convertExpressionListToExpressionResultIfNecessary(final ILocation loc,
			final Dispatcher main, final Result dispatch, final IASTNode hook) {
		assert dispatch instanceof ExpressionListResult || dispatch instanceof ExpressionResult;
		if (dispatch instanceof ExpressionResult) {
			return (ExpressionResult) dispatch;
		}
		final ExpressionListResult listResult = (ExpressionListResult) dispatch;

		final ExpressionResultBuilder result = new ExpressionResultBuilder();

		for (int i = 0; i < listResult.list.size(); i++) {
			/*
			 * Note:
			 * C11 6.5.17.2, footnote:
			 *  A comma operator does not yield an lvalue.
			 * --> thus we can immediately switch to rvalue here
			 */
			result.addAllExceptLrValue(listResult.list.get(i).switchToRValueIfNecessary(main, loc, hook));
		}
		result.setLRVal(listResult.list.get(listResult.list.size() - 1).getLrValue());

		return result.build();
	}

	public static int findIndexOfStructField(final CStruct targetCType, final String rootDesignator) {
		for (int i = 0; i < targetCType.getFieldCount(); i++) {
			if (targetCType.getFieldIds()[i].equals(rootDesignator)) {
				return i;
			}
		}
		throw new AssertionError("designator does not occur in struct type");
	}

	public static LocalLValue constructOffHeapStructAccessLhs(final ILocation loc,
			final LocalLValue structBaseLhsToInitialize, final int i) {
		final CStruct cStructType = (CStruct) structBaseLhsToInitialize.getCType().getUnderlyingType();

		final String fieldId = cStructType.getFieldIds()[i];

		final StructLHS lhs = ExpressionFactory.constructStructAccessLhs(loc, structBaseLhsToInitialize.getLHS(), fieldId);

		return new LocalLValue(lhs, cStructType.getFieldTypes()[i], null);
	}

}
