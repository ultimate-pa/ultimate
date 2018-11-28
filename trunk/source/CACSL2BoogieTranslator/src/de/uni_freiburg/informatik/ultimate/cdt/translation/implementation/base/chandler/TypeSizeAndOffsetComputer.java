/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Axiom;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ConstDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStructOrUnion;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStructOrUnion.StructOrUnion;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * Class that is used to compute the bytesize (what that is returned by the sizeof operator) of types and the memory
 * offsets for fields of structs.
 *
 * @author Matthias Heizmann
 */
public class TypeSizeAndOffsetComputer {

	/**
	 * A set of constants, required for the memory model. E.g. sizeof and offset constants.
	 */
	private final LinkedHashSet<ConstDeclaration> mConstants;
	/**
	 * A set of axioms, required for the memory model. E.g. for sizeof and offset constants.
	 */
	private final LinkedHashSet<Axiom> mAxioms;

	private final HashMap<CType, SizeTValue> mTypeSizeCache;
	private final HashMap<CStructOrUnion, Offset[]> mStructOffsets;
	private final ITypeHandler mTypeHandler;

	private final TypeSizes mTypeSizes;

	private final ExpressionTranslation mExpressionTranslation;
	private final boolean mBitPreciseBitfields;

	/**
	 * Given the field of a struct myStruct.myField such that the offset of the field is n, the computation can
	 * <ul>
	 * <li>return the number n or
	 * <li>return a constant #offset~myStruct~myField and add an axiom #offset~myStruct~myField == 4
	 * </ul>
	 * If false we do the first, if true we do the latter.
	 */
	private final boolean mPreferConstantsOverValues = false;

	private SizeTValue mTypeSizePointer = null;

	public TypeSizeAndOffsetComputer(final TypeSizes typeSizes, final ExpressionTranslation expressionTranslation,
			final ITypeHandler typeHandler, final boolean bitpreciseBitfields) {
		mExpressionTranslation = expressionTranslation;
		mTypeHandler = typeHandler;
		mTypeSizes = typeSizes;
		mTypeSizeCache = new HashMap<>();
		mStructOffsets = new HashMap<>();
		mConstants = new LinkedHashSet<>();
		mAxioms = new LinkedHashSet<>();
		mBitPreciseBitfields = bitpreciseBitfields;
	}

	/**
	 * @return An Expression that represents the size (in bytes) of the given CType. If needed additional constant
	 *         declarations and axioms are constructed. The additional constant declarations and axioms can be obtained
	 *         using the {@link TypeSizeAndOffsetComputer#getConstants()} and
	 *         {@link TypeSizeAndOffsetComputer#getAxioms()} methods.
	 */
	public Expression constructBytesizeExpression(final ILocation loc, final CType cType, final IASTNode hook) {
		final SizeTValue value = computeSize(loc, cType, hook);
		return value.asExpression(loc);
	}

	/**
	 * @return An Expression that represents the offset (in bytes) at which a certain field of a stuct is stored (on the
	 *         heap).
	 */
	public Offset constructOffsetForField(final ILocation loc, final CStructOrUnion cStruct, final int fieldIndex,
			final IASTNode hook) {
		if (!mTypeSizeCache.containsKey(cStruct)) {
			assert !mStructOffsets.containsKey(cStruct) : "both or none";
			computeSize(loc, cStruct, hook);
		}
		final Offset[] offsets = mStructOffsets.get(cStruct);
		assert offsets.length == cStruct.getFieldCount() : "inconsistent struct";
		return offsets[fieldIndex];
	}

	public Offset constructOffsetForField(final ILocation loc, final CStructOrUnion cStruct, final String fieldId,
			final IASTNode hook) {
		final int fieldIndex = Arrays.asList(cStruct.getFieldIds()).indexOf(fieldId);
		return constructOffsetForField(loc, cStruct, fieldIndex, hook);
	}

	private Expression constructTypeSizeConstant(final ILocation loc, final CType cType) {
		final String id = SFO.SIZEOF + cType.toString();
		declareConstant(loc, id);
		final IdentifierExpression idexpr = // new IdentifierExpression(loc, id);
				ExpressionFactory.constructIdentifierExpression(loc, BoogieType.TYPE_INT, id,
						DeclarationInformation.DECLARATIONINFO_GLOBAL);
		return idexpr;
	}

	private Expression constructTypeSizeConstant_Pointer(final ILocation loc) {
		final String id = SFO.SIZEOF + SFO.POINTER;
		declareConstant(loc, id);
		final IdentifierExpression idexpr = // new IdentifierExpression(loc, id);
				ExpressionFactory.constructIdentifierExpression(loc, BoogieType.TYPE_INT, id,
						DeclarationInformation.DECLARATIONINFO_GLOBAL);
		return idexpr;
	}

	/**
	 * Construct Expression that represents the field of a struct or union.
	 */
	private Expression constructTypeSizeConstantForStructField(final ILocation loc, final CStructOrUnion cStruct,
			final int fieldNumber) {
		final String fieldId = cStruct.getFieldIds()[fieldNumber];
		final String resultId = SFO.OFFSET + cStruct.toString() + "~" + fieldId;
		declareConstant(loc, resultId);
		final Expression result = // new IdentifierExpression(loc, resultId);
				ExpressionFactory.constructIdentifierExpression(loc, BoogieType.TYPE_INT, resultId,
						DeclarationInformation.DECLARATIONINFO_GLOBAL);
		return result;
	}

	private void declareConstant(final ILocation loc, final String id) {
		final ASTType astType = mTypeHandler.cType2AstType(loc, getSizeT());
		final VarList varList = new VarList(loc, new String[] { id }, astType);
		final ConstDeclaration decl = new ConstDeclaration(loc, new Attribute[0], false, varList, null, false);
		mConstants.add(decl);
	}

	private SizeTValue computeSize(final ILocation loc, final CType cType, final IASTNode hook) {
		final CType underlyingType = cType.getUnderlyingType();
		if (underlyingType instanceof CPointer) {
			if (mTypeSizePointer == null) {
				mTypeSizePointer = constructSizeTValue_Pointer(loc);
			}
			return mTypeSizePointer;
		} else if (underlyingType instanceof CEnum) {
			// an Enum contains constants of type int
			return computeSize(loc, new CPrimitive(CPrimitives.INT), hook);
		} else {
			SizeTValue sizeTValue = mTypeSizeCache.get(underlyingType);
			if (sizeTValue == null) {
				if (underlyingType instanceof CPrimitive) {
					sizeTValue = constructSizeTValue_Primitive(loc, (CPrimitive) underlyingType);
				} else if (underlyingType instanceof CArray) {
					sizeTValue = constructSizeTValue_Array(loc, (CArray) underlyingType, hook);
				} else if (underlyingType instanceof CStructOrUnion) {
					sizeTValue = constructSizeTValueAndOffsets_StructAndUnion(loc, (CStructOrUnion) underlyingType, hook);
				} else {
					throw new UnsupportedOperationException("Unsupported type" + underlyingType);
				}
				mTypeSizeCache.put(underlyingType, sizeTValue);
			}
			return sizeTValue;
		}
	}

	private SizeTValue constructSizeTValue_Primitive(final ILocation loc, final CPrimitive cPrimitive) {
		final SizeTValue result;
		if (mTypeSizes.useFixedTypeSizes()) {
			final int size = mTypeSizes.getSize(cPrimitive.getType());
			result = new SizeTValue_Integer(BigInteger.valueOf(size));
		} else {
			final Expression sizeConstant = constructTypeSizeConstant(loc, cPrimitive);
			result = new SizeTValue_Expression(sizeConstant);
			final Axiom axiom = constructNonNegativeAxiom(loc, sizeConstant);
			mAxioms.add(axiom);
		}
		return result;
	}

	private SizeTValue constructSizeTValue_Array(final ILocation loc, final CArray cArray, final IASTNode hook) {

		final SizeTValue valueSize = computeSize(loc, cArray.getValueType(), hook);
		final SizeTValue factor = extractSizeTValue(cArray.getBound(), hook);

		final SizeTValue size = (new SizeTValueAggregator_Multiply()).aggregate(loc,
				Arrays.asList(new SizeTValue[] { valueSize, factor }));
		final SizeTValue result;
		if (mPreferConstantsOverValues) {
			final Expression sizeConstant = constructTypeSizeConstant(loc, cArray);
			result = new SizeTValue_Expression(sizeConstant);
			final Expression equality = mExpressionTranslation.constructBinaryComparisonExpression(loc,
					IASTBinaryExpression.op_equals, sizeConstant, getSizeT(), size.asExpression(loc), getSizeT());
			final Axiom axiom = new Axiom(loc, new Attribute[0], equality);
			mAxioms.add(axiom);
		} else {
			result = size;
		}
		return result;
	}

	/**
	 * Returns the size of a CStructOrUnion and as a side-effects computes the
	 * {@link Offset}s for each member to the {@code mStructOffsets} array.
	 */
	private SizeTValue constructSizeTValueAndOffsets_StructAndUnion(final ILocation loc, final CStructOrUnion cStruct,
			final IASTNode hook) {
		if (cStruct.isIncomplete()) {
			// according to C11 6.5.3.4.1
			throw new IllegalArgumentException("cannot determine size of incomplete type");
		}
		if (mStructOffsets.containsKey(cStruct)) {
			throw new AssertionError("must not be computed");
		}
		final Offset[] offsets = new Offset[cStruct.getFieldCount()];
		mStructOffsets.put(cStruct, offsets);
		final SizeTValue result;
		if (cStruct.getFieldCount() == 0) {
			result = new SizeTValue_Integer(BigInteger.ZERO);
		} else {
			if (cStruct.isStructOrUnion() == StructOrUnion.UNION) {
				final SizeTValue[] fieldTypeSizes = new SizeTValue[cStruct.getFieldCount()];
				for (int i = 0; i < cStruct.getFieldCount(); i++) {
					final CType fieldType = cStruct.getFieldTypes()[i];
					final int bitsize;
					if (mBitPreciseBitfields) {
						bitsize = cStruct.getBitFieldWidths().get(i);
					} else {
						bitsize = -1;
					}
					final int startBit;
					if (bitsize == -1) {
						startBit = -1;
					} else {
						startBit = 0;
					}
					offsets[i] = new Offset(new SizeTValue_Integer(BigInteger.ZERO), startBit, bitsize);
					fieldTypeSizes[i] = computeOffsetOfNextByte(offsets[i], fieldType, loc, hook);
				}
				result = new SizeTValueAggregator_Max().aggregate(loc, Arrays.asList(fieldTypeSizes));
			} else {
				for (int i = 0; i < cStruct.getFieldCount(); i++) {
					final int bitsize;
					if (mBitPreciseBitfields) {
						bitsize = cStruct.getBitFieldWidths().get(i);
					} else {
						bitsize = -1;
					}
					final int startBit;
					if (i == 0) {
						if (bitsize == -1) {
							startBit = -1;
						} else {
							startBit = 0;
						}
						offsets[i] = new Offset(new SizeTValue_Integer(BigInteger.ZERO), startBit, bitsize);
					} else {
						offsets[i] = computeMemberOffset(offsets[i - 1], cStruct.getFieldTypes()[i - 1], bitsize,
								loc, hook);
					}
				}
				final int lastPosition = cStruct.getFieldCount()-1;
				result = computeOffsetOfNextByte(offsets[lastPosition], cStruct.getFieldTypes()[lastPosition], loc, hook);
			}
		}
		mTypeSizeCache.put(cStruct, result);
		return result;
	}

	private SizeTValue constructSizeTValue_Pointer(final ILocation loc) {
		final SizeTValue result;
		if (mTypeSizes.useFixedTypeSizes()) {
			final int size = mTypeSizes.getSizeOfPointer();
			result = new SizeTValue_Integer(BigInteger.valueOf(size));
		} else {
			final Expression sizeConstant = constructTypeSizeConstant_Pointer(loc);
			result = new SizeTValue_Expression(sizeConstant);
			final Axiom axiom = constructNonNegativeAxiom(loc, sizeConstant);
			mAxioms.add(axiom);
		}
		return result;
	}

	private Axiom constructNonNegativeAxiom(final ILocation loc, final Expression sizeConstant) {
		final Expression zero = mTypeSizes.constructLiteralForIntegerType(loc, getSizeT(), BigInteger.ZERO);
		final Expression isNonNegative = mExpressionTranslation.constructBinaryComparisonExpression(loc,
				IASTBinaryExpression.op_greaterEqual, sizeConstant, getSizeT(), zero, getSizeT());
		final Axiom axiom = new Axiom(loc, new Attribute[0], isNonNegative);
		return axiom;
	}

	private SizeTValue extractSizeTValue(final RValue rvalue, final IASTNode hook) {
		final BigInteger value = mTypeSizes.extractIntegerValue(rvalue, hook);
		if (value != null) {
			return new SizeTValue_Integer(value);
		}
		return new SizeTValue_Expression(rvalue.getValue());
	}

	/**
	 * Get the CType that represents <em> size_t </em>. TODO: Currently hard-coded to int. Should probably be a setting.
	 * This is unsound, but in the integer translation more efficient than uint (no wraparound). TODO: maybe this class
	 * is not the right place.
	 */
	public CPrimitive getSizeT() {
		return new CPrimitive(CPrimitives.INT);
	}

	public LinkedHashSet<ConstDeclaration> getConstants() {
		return mConstants;
	}

	public LinkedHashSet<Axiom> getAxioms() {
		return mAxioms;
	}

	private abstract class SizeTValueAggregator {

		public SizeTValue aggregate(final ILocation loc, final List<SizeTValue> values) {
			if (values.isEmpty()) {
				return new SizeTValue_Integer(resultForZeroOperandCase());
			}
			final LinkedList<SizeTValue> tmpValues = new LinkedList<>(values);
			BigInteger aggregatedIntegers = null;
			final Iterator<SizeTValue> it = tmpValues.iterator();
			while (it.hasNext()) {
				final SizeTValue current = it.next();
				if (current instanceof SizeTValue_Integer) {
					final BigInteger currentInteger = ((SizeTValue_Integer) current).getInteger();
					if (aggregatedIntegers == null) {
						aggregatedIntegers = currentInteger;
					} else {
						aggregatedIntegers = aggregateIntegers(aggregatedIntegers, currentInteger);
					}
					it.remove();
				}
			}
			if (tmpValues.isEmpty()) {
				return new SizeTValue_Integer(aggregatedIntegers);
			}
			if (aggregatedIntegers != null) {
				tmpValues.add(new SizeTValue_Integer(aggregatedIntegers));
			}
			if (tmpValues.size() == 1) {
				return tmpValues.getFirst();
			}
			return aggregateExpressions(loc, tmpValues);
		}

		private SizeTValue aggregateExpressions(final ILocation loc, final LinkedList<SizeTValue> values) {
			assert !values.isEmpty() : "at least one needed";
			final SizeTValue first = values.removeFirst();
			Expression aggregatedExpressions = first.asExpression(loc);
			for (final SizeTValue value : values) {
				final Expression expr = value.asExpression(loc);
				aggregatedExpressions = aggregateExpressions(loc, aggregatedExpressions, expr);
			}
			return new SizeTValue_Expression(aggregatedExpressions);
		}

		protected abstract Expression aggregateExpressions(ILocation loc, Expression op1, Expression op2);

		protected abstract BigInteger aggregateIntegers(BigInteger op1, BigInteger op2);

		protected abstract BigInteger resultForZeroOperandCase();
	}

	private class SizeTValueAggregator_Add extends SizeTValueAggregator {

		@Override
		protected Expression aggregateExpressions(final ILocation loc, final Expression op1, final Expression op2) {
			return mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_plus, op1,
					getSizeT(), op2, getSizeT());
		}

		@Override
		protected BigInteger aggregateIntegers(final BigInteger op1, final BigInteger op2) {
			return op1.add(op2);
		}

		@Override
		protected BigInteger resultForZeroOperandCase() {
			return BigInteger.ZERO;
		}
	}

	private class SizeTValueAggregator_Multiply extends SizeTValueAggregator {

		@Override
		protected Expression aggregateExpressions(final ILocation loc, final Expression op1, final Expression op2) {
			return mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_multiply, op1,
					getSizeT(), op2, getSizeT());
		}

		@Override
		protected BigInteger aggregateIntegers(final BigInteger op1, final BigInteger op2) {
			return op1.multiply(op2);
		}

		@Override
		protected BigInteger resultForZeroOperandCase() {
			return BigInteger.ONE;
		}
	}

	private class SizeTValueAggregator_Max extends SizeTValueAggregator {

		@Override
		protected Expression aggregateExpressions(final ILocation loc, final Expression op1, final Expression op2) {
			final Expression firstIsGreater = mExpressionTranslation.constructBinaryComparisonExpression(loc,
					IASTBinaryExpression.op_greaterEqual, op1, getSizeT(), op2, getSizeT());
			final Expression result = ExpressionFactory.constructIfThenElseExpression(loc, firstIsGreater, op1, op2);
			return result;
		}

		@Override
		protected BigInteger aggregateIntegers(final BigInteger op1, final BigInteger op2) {
			return op1.max(op2);
		}

		@Override
		protected BigInteger resultForZeroOperandCase() {
			return BigInteger.ZERO;
		}
	}

	private abstract class SizeTValue {
		public abstract Expression asExpression(ILocation loc);
	}

	private class SizeTValue_Integer extends SizeTValue {
		private final BigInteger mValue;

		public SizeTValue_Integer(final BigInteger value) {
			mValue = value;
		}

		@Override
		public Expression asExpression(final ILocation loc) {
			return mTypeSizes.constructLiteralForIntegerType(loc, getSizeT(), mValue);
		}

		public BigInteger getInteger() {
			return mValue;
		}

		@Override
		public String toString() {
			return String.valueOf(mValue);
		}
	}

	private class SizeTValue_Expression extends SizeTValue {
		private final Expression mValue;

		public SizeTValue_Expression(final Expression value) {
			mValue = value;
		}

		@Override
		public Expression asExpression(final ILocation loc) {
			return mValue;
		}

		@Override
		public String toString() {
			return String.valueOf(mValue);
		}
	}

	public class Offset {
		private final SizeTValue_Integer mAddressOffset;
		private final int mStartBit;
		private final int mBitsize;
		public Offset(final SizeTValue_Integer addressOffset, final int startBit, final int bitsize) {
			super();
			mAddressOffset = addressOffset;
			mStartBit = startBit;
			mBitsize = bitsize;
			assert (startBit == -1 && bitsize == -1) || (startBit >= 0 && bitsize >= 0);
		}
		public Expression getAddressOffsetAsExpression(final ILocation loc) {
			return mAddressOffset.asExpression(loc);
		}
		public SizeTValue_Integer getAddressOffset() {
			return mAddressOffset;
		}
		public int getStartBit() {
			return mStartBit;
		}
		public int getBitFieldSize() {
			return mBitsize;
		}
		public boolean isBitfieldOffset() {
			return getStartBit() != -1;
		}
		@Override
		public String toString() {
			if (!isBitfieldOffset()) {
				return getAddressOffset() + "bytes";
			} else {
				return getAddressOffset() + "bytes+bit" + getStartBit() + "to"
						+ (getStartBit() + getBitFieldSize() - 1);
			}
		}
	}

	private Offset computeMemberOffset(final Offset precedingMemberOffset, final CType precedingMemberType,
			final int bitfieldSize, final ILocation loc, final IASTNode hook) {
		final boolean precedingMemberIsBitfield = precedingMemberOffset.isBitfieldOffset();
		final boolean currentMemberIsBitfield = (bitfieldSize != -1);
		final Offset result;
		if (precedingMemberIsBitfield) {
			if (precedingMemberOffset.getBitFieldSize() == 0) {
				throw new UnsupportedOperationException("Bitfields: case that previous is zero not yet implemented.");
			}
			if (currentMemberIsBitfield) {
				final int occupiedSize = precedingMemberOffset.getStartBit() + precedingMemberOffset.getBitFieldSize();
				final int completelyOccupiedBytes = occupiedSize / 2;
				final int newStartBit = occupiedSize % 8;
				result = new Offset(new SizeTValue_Integer(precedingMemberOffset.getAddressOffset().getInteger()
						.add(BigInteger.valueOf(completelyOccupiedBytes))), newStartBit, bitfieldSize);
			} else {
				// !currentMemberIsBitfield
				final SizeTValue_Integer nextAddress = (SizeTValue_Integer) computeOffsetOfNextByte(
						precedingMemberOffset, precedingMemberType, loc, hook);
				result = new Offset(nextAddress, -1, -1);
			}
		} else {
			// !previousMemberIsBitfield
			if (currentMemberIsBitfield) {
				result = new Offset(precedingMemberOffset.getAddressOffset(), 0, bitfieldSize);
			} else {
				// !currentMemberIsBitfield
				final SizeTValue size = computeSize(loc, precedingMemberType, hook);
				if (!(size instanceof SizeTValue_Integer)) {
					throw new AssertionError("only flexible array member at the end can have non-constant size");
				}
				result = new Offset(new SizeTValue_Integer(precedingMemberOffset.getAddressOffset().getInteger()
						.add(((SizeTValue_Integer) size).getInteger())), -1, -1);
			}
		}
		return result;
	}


	private SizeTValue computeOffsetOfNextByte(final Offset offset, final CType precedingMemberType, final ILocation loc, final IASTNode hook) {
		if (offset.getStartBit() == -1) {
			final SizeTValue precedingTypeSize = computeSize(loc, precedingMemberType, hook);
			return new SizeTValueAggregator_Add().aggregate(loc, Arrays.asList(offset.getAddressOffset(), precedingTypeSize));
		}
		if (offset.getBitFieldSize() == 0) {
			return new SizeTValue_Integer(offset.getAddressOffset().getInteger().add(BigInteger.ONE));
		} else {
			final int lastOccupiedBit = offset.getStartBit() + offset.getBitFieldSize();
			final int additionalByes = (lastOccupiedBit / 8) + 1;
			return new SizeTValue_Integer(offset.getAddressOffset().getInteger().add(BigInteger.valueOf(additionalByes)));
		}

	}

}