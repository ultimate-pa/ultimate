/*
 * Copyright (C) 2013-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
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

import java.util.ArrayList;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTFieldReference;
import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.IDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizeAndOffsetComputer.Offset;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStructOrUnion;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStructOrUnion.StructOrUnion;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.BitfieldInformation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultTransformer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.HeapLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValueFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * Class that handles translation of Structs.
 *
 * @authors Markus Lindenmann, Alexander Nutz, Matthias Heizmann
 * @date 12.10.2012 modified (a lot) by Alexander Nutz in later 2013/early 2014
 */
public class StructHandler {

	private final MemoryHandler mMemoryHandler;
	private final TypeSizeAndOffsetComputer mTypeSizeAndOffsetComputer;
	private final ExpressionTranslation mExpressionTranslation;
	private final ITypeHandler mTypeHandler;
	private final LocationFactory mLocationFactory;

	public StructHandler(final MemoryHandler memoryHandler, final TypeSizeAndOffsetComputer typeSizeAndOffsetComputer,
			final ExpressionTranslation expressionTranslation, final ITypeHandler typeHandler,
			final LocationFactory locationFactory) {
		mMemoryHandler = memoryHandler;
		mTypeSizeAndOffsetComputer = typeSizeAndOffsetComputer;
		mExpressionTranslation = expressionTranslation;
		mTypeHandler = typeHandler;
		mLocationFactory = locationFactory;
	}

	/**
	 * Handle IASTFieldReference.
	 *
	 * @param main
	 *            a reference to the main IDispatcher.
	 * @param node
	 *            the node to translate.
	 * @param mMemoryHandler
	 * @return the translation results.
	 */
	public Result handleFieldReference(final IDispatcher main, final ExpressionResultTransformer transformer,
			final IASTFieldReference node) {
		final ILocation loc = mLocationFactory.createCLocation(node);
		final String field = node.getFieldName().toString();

		ExpressionResult fieldOwner = (ExpressionResult) main.dispatch(node.getFieldOwner());

		LRValue newValue = null;

		final List<ExpressionResult> unionFieldToCType =
				fieldOwner.getNeighbourUnionFields() == null ? new ArrayList<>()
						: new ArrayList<>(fieldOwner.getNeighbourUnionFields());

		final CType foType = (node.isPointerDereference()
				? ((CPointer) fieldOwner.getLrValue().getUnderlyingType()).getPointsToType()
				: fieldOwner.getLrValue().getUnderlyingType());

		final CStructOrUnion cStructType = (CStructOrUnion) foType.getUnderlyingType();
		final CType cFieldType = cStructType.getFieldType(field);
		final int bitfieldWidth = cStructType.getBitfieldWidth(field);

		if (node.isPointerDereference()) {
			final ExpressionResult rFieldOwnerRex = transformer.switchToRValue(fieldOwner, loc, node);
			final Expression address = rFieldOwnerRex.getLrValue().getValue();
			fieldOwner = new ExpressionResult(rFieldOwnerRex.getStatements(),
					LRValueFactory.constructHeapLValue(mTypeHandler, address, rFieldOwnerRex.getLrValue().getCType(),
							null),
					rFieldOwnerRex.getDeclarations(), rFieldOwnerRex.getAuxVars(), rFieldOwnerRex.getOverapprs());
		}

		if (fieldOwner.getLrValue() instanceof HeapLValue) {
			final HeapLValue fieldOwnerHlv = (HeapLValue) fieldOwner.getLrValue();

			// TODO: different calculations for unions
			final Expression startAddress = fieldOwnerHlv.getAddress();

			final Expression newStartAddressBase = MemoryHandler.getPointerBaseAddress(startAddress, loc);
			final Expression newStartAddressOffset = MemoryHandler.getPointerOffset(startAddress, loc);

			final Offset fieldOffset =
					mTypeSizeAndOffsetComputer.constructOffsetForField(loc, cStructType, field, node);
			if (fieldOffset.isBitfieldOffset()) {
				throw new UnsupportedOperationException("Bitfield reference");
			}

			final Expression sumOffset = mExpressionTranslation.constructArithmeticExpression(loc,
					IASTBinaryExpression.op_plus, newStartAddressOffset,
					mExpressionTranslation.getCTypeOfPointerComponents(), fieldOffset.getAddressOffsetAsExpression(loc),
					mExpressionTranslation.getCTypeOfPointerComponents());
			final Expression newPointer =
					MemoryHandler.constructPointerFromBaseAndOffset(newStartAddressBase, sumOffset, loc);
			final BitfieldInformation bi = constructBitfieldInformation(bitfieldWidth);
			newValue = LRValueFactory.constructHeapLValue(mTypeHandler, newPointer, cFieldType, bi);

			if (cStructType.isStructOrUnion() == StructOrUnion.UNION) {
				unionFieldToCType.addAll(computeNeighbourFieldsOfUnionField(main, loc, field, unionFieldToCType,
						cStructType, fieldOwnerHlv, node));
			}
		} else if (fieldOwner.getLrValue() instanceof RValue) {
			final RValue rVal = (RValue) fieldOwner.getLrValue();
			final StructAccessExpression sexpr =
					ExpressionFactory.constructStructAccessExpression(loc, rVal.getValue(), field);
			newValue = new RValue(sexpr, cFieldType);
		} else {
			final LocalLValue lVal = (LocalLValue) fieldOwner.getLrValue();
			final StructLHS slhs = ExpressionFactory.constructStructAccessLhs(loc, lVal.getLhs(), field);
			final BitfieldInformation bi = constructBitfieldInformation(bitfieldWidth);
			newValue = new LocalLValue(slhs, cFieldType, bi);

			if (cStructType.isStructOrUnion() == StructOrUnion.UNION) {
				unionFieldToCType.addAll(computeNeighbourFieldsOfUnionField(main, loc, field, unionFieldToCType,
						cStructType, lVal, node));
			}
		}

		return new ExpressionResult(fieldOwner.getStatements(), newValue, fieldOwner.getDeclarations(),
				fieldOwner.getAuxVars(), fieldOwner.getOverapprs(), unionFieldToCType);
	}

	private static BitfieldInformation constructBitfieldInformation(final int bitfieldWidth) {
		if (bitfieldWidth != -1) {
			return new BitfieldInformation(bitfieldWidth);
		}
		return null;
	}

	private List<ExpressionResult> computeNeighbourFieldsOfUnionField(final IDispatcher main, final ILocation loc,
			final String field, final List<ExpressionResult> unionFieldToCType, final CStructOrUnion foType,
			final LRValue fieldOwner, final IASTNode hook) {
		assert foType.isStructOrUnion() == StructOrUnion.UNION;

		List<ExpressionResult> result;
		if (unionFieldToCType == null) {
			result = new ArrayList<>();
		} else {
			result = new ArrayList<>(unionFieldToCType);
		}

		for (final String neighbourField : foType.getFieldIds()) {
			if (neighbourField.equals(field)) {
				continue;
			}
			final ExpressionResultBuilder builder = new ExpressionResultBuilder();

			if (fieldOwner instanceof LocalLValue) {
				final StructLHS havocSlhs = ExpressionFactory.constructStructAccessLhs(loc,
						((LocalLValue) fieldOwner).getLhs(), neighbourField);
				builder.setLrValue(new LocalLValue(havocSlhs, foType.getFieldType(neighbourField), null));
			} else {
				assert fieldOwner instanceof HeapLValue;
				final Offset fieldOffset =
						mTypeSizeAndOffsetComputer.constructOffsetForField(loc, foType, neighbourField, hook);
				if (fieldOffset.isBitfieldOffset()) {
					throw new UnsupportedOperationException("Bitfield union neighbor");
				}

				final Expression unionAddress = ((HeapLValue) fieldOwner).getAddress();
				final Expression summedOffset = mExpressionTranslation.constructArithmeticIntegerExpression(loc,
						IASTBinaryExpression.op_plus, MemoryHandler.getPointerOffset(unionAddress, loc),
						mExpressionTranslation.getCTypeOfPointerComponents(),
						fieldOffset.getAddressOffsetAsExpression(loc),
						mExpressionTranslation.getCTypeOfPointerComponents());
				final StructConstructor neighbourFieldAddress = MemoryHandler.constructPointerFromBaseAndOffset(
						MemoryHandler.getPointerBaseAddress(unionAddress, loc), summedOffset, loc);

				builder.setLrValue(LRValueFactory.constructHeapLValue(mTypeHandler, neighbourFieldAddress,
						foType.getFieldType(neighbourField), null));

			}

			result.add(builder.build());
		}

		return result;
	}

	public Result readFieldInTheStructAtAddress(final ILocation loc, final int fieldIndex,
			final Expression structAddress, final CStructOrUnion structType, final IASTNode hook) {
		Expression addressBaseOfFieldOwner;
		Expression addressOffsetOfFieldOwner;

		addressBaseOfFieldOwner =
				ExpressionFactory.constructStructAccessExpression(loc, structAddress, SFO.POINTER_BASE);
		addressOffsetOfFieldOwner =
				ExpressionFactory.constructStructAccessExpression(loc, structAddress, SFO.POINTER_OFFSET);

		final Expression newOffset =
				computeStructFieldOffset(mMemoryHandler, loc, fieldIndex, addressOffsetOfFieldOwner, structType, hook);

		final StructConstructor newPointer =
				MemoryHandler.constructPointerFromBaseAndOffset(addressBaseOfFieldOwner, newOffset, loc);

		final CType resultType = structType.getFieldTypes()[fieldIndex];

		final ExpressionResult call = mMemoryHandler.getReadCall(newPointer, resultType, hook);
		final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();
		resultBuilder.addAllExceptLrValue(call);
		resultBuilder.setLrValue(new RValue(call.getLrValue().getValue(), resultType));
		return resultBuilder.build();
	}

	Expression computeStructFieldOffset(final MemoryHandler memoryHandler, final ILocation loc, final int fieldIndex,
			final Expression addressOffsetOfFieldOwner, final CStructOrUnion structType, final IASTNode hook) {
		if (structType == null) {
			throw new IncorrectSyntaxException(loc, "Incorrect or unexpected field owner!");
		}
		final Offset fieldOffset =
				mTypeSizeAndOffsetComputer.constructOffsetForField(loc, structType, fieldIndex, hook);
		if (fieldOffset.isBitfieldOffset()) {
			throw new UnsupportedOperationException("Bitfield read");
		}

		final Expression result = mExpressionTranslation.constructArithmeticExpression(loc,
				IASTBinaryExpression.op_plus, addressOffsetOfFieldOwner, mTypeSizeAndOffsetComputer.getSizeT(),
				fieldOffset.getAddressOffsetAsExpression(loc), mTypeSizeAndOffsetComputer.getSizeT());
		return result;
	}

}
