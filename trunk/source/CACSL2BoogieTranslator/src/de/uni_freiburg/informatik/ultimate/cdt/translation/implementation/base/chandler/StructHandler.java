/*
 * Copyright (C) 2013-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2025-2026 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2026 University of Freiburg
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

import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizeAndOffsetComputer.Offset;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStructOrUnion;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStructOrUnion.StructOrUnion;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.ICType;
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

	public StructHandler(final MemoryHandler memoryHandler, final TypeSizeAndOffsetComputer typeSizeAndOffsetComputer,
			final ExpressionTranslation expressionTranslation, final ITypeHandler typeHandler) {
		mMemoryHandler = memoryHandler;
		mTypeSizeAndOffsetComputer = typeSizeAndOffsetComputer;
		mExpressionTranslation = expressionTranslation;
		mTypeHandler = typeHandler;
	}

	public ExpressionResult handleFieldReference(final ILocation loc, final ExpressionResultTransformer transformer,
			ExpressionResult fieldOwner, final String field, final boolean isPointerDereference, final IASTNode hook) {
		final List<ExpressionResult> unionFieldToCType =
				fieldOwner.getNeighbourUnionFields() == null ? new ArrayList<>()
						: new ArrayList<>(fieldOwner.getNeighbourUnionFields());

		final ICType foType =
				(isPointerDereference ? ((CPointer) fieldOwner.getLrValue().getUnderlyingType()).getPointsToType()
						: fieldOwner.getLrValue().getUnderlyingType());

		final CStructOrUnion cStructType = (CStructOrUnion) foType.getUnderlyingType();
		if (isPointerDereference) {
			final ExpressionResult rFieldOwnerRex = transformer.switchToRValue(fieldOwner, loc, hook);
			final Expression address = rFieldOwnerRex.getLrValue().getValue();
			fieldOwner = new ExpressionResult(rFieldOwnerRex.getStatements(),
					LRValueFactory.constructHeapLValue(mTypeHandler, address, rFieldOwnerRex.getLrValue().getCType(),
							null),
					rFieldOwnerRex.getDeclarations(), rFieldOwnerRex.getAuxVars(), rFieldOwnerRex.getOverapprs());
		}

		// Because of anonymous members, resolving the field access may result in a path of members.
		// Therefore, we iterate over this path here.
		final List<String> path = cStructType.getFieldPath(field);
		LRValue current = fieldOwner.getLrValue();
		CStructOrUnion currentStruct = cStructType;
		for (int i = 0; i < path.size(); i++) {
			final String currentField = path.get(i);
			final boolean isLast = i == path.size() - 1;
			final ICType cFieldType = currentStruct.getFieldType(currentField);
			final int bitfieldWidth = isLast ? currentStruct.getBitfieldWidth(currentField) : -1;

			current = switch (current) {
			case final HeapLValue fieldOwnerHlv -> {
				final Offset fieldOffset =
						mTypeSizeAndOffsetComputer.constructOffsetForField(loc, currentStruct, currentField);

				// TODO: different calculations for unions
				final Expression startAddress = fieldOwnerHlv.getAddress();

				final Expression newPointer = mMemoryHandler.constructAddressForStructField(loc, startAddress,
						fieldOffset, mExpressionTranslation.getCTypeOfPointerComponents());

				if (currentStruct.isStructOrUnion() == StructOrUnion.UNION) {
					unionFieldToCType.addAll(computeNeighbourFieldsOfUnionField(loc, currentField, unionFieldToCType,
							currentStruct, current));
				}

				final BitfieldInformation bi = constructBitfieldInformation(bitfieldWidth);
				yield LRValueFactory.constructHeapLValue(mTypeHandler, newPointer, cFieldType, bi);
			}

			case final RValue rVal -> {
				final Expression sexpr =
						ExpressionFactory.constructStructAccessExpression(loc, rVal.getValue(), currentField);
				yield new RValue(sexpr, cFieldType);
			}
			case final LocalLValue lVal -> {
				if (currentStruct.isStructOrUnion() == StructOrUnion.UNION) {
					unionFieldToCType.addAll(computeNeighbourFieldsOfUnionField(loc, currentField, unionFieldToCType,
							currentStruct, lVal));
				}
				final StructLHS slhs = ExpressionFactory.constructStructAccessLhs(loc, lVal.getLhs(), currentField);
				final BitfieldInformation bi = constructBitfieldInformation(bitfieldWidth);
				yield new LocalLValue(slhs, cFieldType, bi);
			}
			};
			if (!isLast) {
				currentStruct = (CStructOrUnion) cFieldType.getUnderlyingType();
			}
		}

		return new ExpressionResult(fieldOwner.getStatements(), current, fieldOwner.getDeclarations(),
				fieldOwner.getAuxVars(), fieldOwner.getOverapprs(), unionFieldToCType);
	}

	private static BitfieldInformation constructBitfieldInformation(final int bitfieldWidth) {
		if (bitfieldWidth != -1) {
			return new BitfieldInformation(bitfieldWidth);
		}
		return null;
	}

	private List<ExpressionResult> computeNeighbourFieldsOfUnionField(final ILocation loc, final String field,
			final List<ExpressionResult> unionFieldToCType, final CStructOrUnion foType, final LRValue fieldOwner) {
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

			final LRValue lrValue = switch (fieldOwner) {
			case final LocalLValue localLValue -> {
				final StructLHS havocSlhs =
						ExpressionFactory.constructStructAccessLhs(loc, localLValue.getLhs(), neighbourField);
				yield new LocalLValue(havocSlhs, foType.getFieldType(neighbourField), null);
			}
			case final HeapLValue heapLValue -> {
				final Expression unionAddress = heapLValue.getAddress();

				final Offset fieldOffset =
						mTypeSizeAndOffsetComputer.constructOffsetForField(loc, foType, neighbourField);

				final Expression neighbourFieldAddress = mMemoryHandler.constructAddressForStructField(loc,
						unionAddress, fieldOffset, mExpressionTranslation.getCTypeOfPointerComponents());

				yield LRValueFactory.constructHeapLValue(mTypeHandler, neighbourFieldAddress,
						foType.getFieldType(neighbourField), null);
			}
			case final RValue rValue -> throw new AssertionError("Union field owner must be an lvalue");
			};

			result.add(builder.setLrValue(lrValue).build());
		}

		return result;
	}

	public Result readFieldInTheStructAtAddress(final ILocation loc, final int fieldIndex,
			final Expression structAddress, final CStructOrUnion structType, final boolean unchecked) {
		final Expression newPointer = computeStructFieldAddress(loc, fieldIndex, structAddress, structType);

		final ICType resultType = structType.getFieldTypes()[fieldIndex];

		final ExpressionResult call = unchecked ? mMemoryHandler.getReadUnchecked(newPointer, resultType)
				: mMemoryHandler.getReadCall(newPointer, resultType);
		final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();
		resultBuilder.addAllExceptLrValue(call);
		resultBuilder.setLrValue(new RValue(call.getLrValue().getValue(), resultType));
		return resultBuilder.build();
	}

	public Expression computeStructFieldAddress(final ILocation loc, final int fieldIndex, final Expression address,
			final CStructOrUnion structType) {

		if (structType == null) {
			throw new IncorrectSyntaxException(loc, "Incorrect or unexpected field owner!");
		}
		final Offset fieldOffset = mTypeSizeAndOffsetComputer.constructOffsetForField(loc, structType, fieldIndex);

		return mMemoryHandler.constructAddressForStructField(loc, address, fieldOffset,
				mTypeSizeAndOffsetComputer.getSizeT());

	}
}
