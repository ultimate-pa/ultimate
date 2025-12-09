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

import java.math.BigInteger;
import java.util.Collections;
import java.util.List;
import java.util.Set;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.FunctionDeclarations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.IPointerIntegerConversion;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.NonBijectiveMapping1D;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.NonBijectiveMapping2D;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.OverapproximationUF1D;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.OverapproximationUF2D;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.ICType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.CheckMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.PointerIntegerConversion;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * Abstract base class for implementing specific memory addressing schemes based on a memory pointer representation.
 *
 * This class serves as base to implement memory addressing schemes that specify how a memory location is computed or
 * accessed based on the provided pointer representation.
 *
 * @param <T>
 *            the memory pointer representation used for addressing, which must implement {@link IMemoryPointer}.
 *
 * @author Jan Körner
 */
public abstract class MemoryAdressingBase<T extends IMemoryPointer> implements IMemoryAdressing {
	protected final ITypeHandler mTypeHandler;
	protected final ExpressionTranslation mExpressionTranslation;
	protected final IBooleanArrayHelper mBooleanArrayHelper;
	protected final TypeSizes mTypeSizes;
	protected final TypeSizeAndOffsetComputer mTypeSizeAndOffsetComputer;
	protected IPointerIntegerConversion mPointerIntegerConversion;
	protected final T mMemoryPointer;
	protected IMemoryManagementStrategy mMemoryManagementStrategy;
	private final IMemoryMetadata mMemoryMetadata;

	protected final BigInteger mFunctionPointerPointerBaseValue = BigInteger.valueOf(-1);

	public MemoryAdressingBase(final ITypeHandler typeHandler, final ExpressionTranslation exprTranslation,
			final IBooleanArrayHelper booleanArrayHelper, final TypeSizes typeSizes,
			final TypeSizeAndOffsetComputer typeSizeAndOffsetComputer, final T pointer,
			final PointerIntegerConversion pointerIntegerMode, final FunctionDeclarations functionDeclarations,
			final IMemoryMetadata memoryMetadata) {
		mTypeHandler = typeHandler;
		mExpressionTranslation = exprTranslation;
		mBooleanArrayHelper = booleanArrayHelper;
		mTypeSizes = typeSizes;
		mTypeSizeAndOffsetComputer = typeSizeAndOffsetComputer;
		mMemoryPointer = pointer;
		mMemoryMetadata = memoryMetadata;

		mPointerIntegerConversion = switch (pointerIntegerMode) {
		case NonBijectiveMapping:
			if (mMemoryPointer instanceof final MemoryPointer1D pointer1D) {
				yield new NonBijectiveMapping1D(exprTranslation, pointer1D);
			} else if (mMemoryPointer instanceof final MemoryPointer2D pointer2D) {
				yield new NonBijectiveMapping2D(exprTranslation, typeSizes, pointer2D);
			} else {
				throw new UnsupportedOperationException("Unknown pointer type " + mMemoryPointer.getClass());
			}
		case Overapproximate:
			if (mMemoryPointer instanceof final MemoryPointer1D pointer1D) {
				yield new OverapproximationUF1D(exprTranslation, functionDeclarations, typeHandler, pointer1D);
			} else if (mMemoryPointer instanceof final MemoryPointer2D pointer2D) {
				yield new OverapproximationUF2D(exprTranslation, functionDeclarations, typeHandler, typeSizes,
						pointer2D);
			} else {
				throw new UnsupportedOperationException("Unknown pointer type " + mMemoryPointer.getClass());
			}
		default:
			throw new UnsupportedOperationException(
					"Pointer-Integer conversion not yet implemented " + pointerIntegerMode);
		};
	}

	/**
	 * Multiply an integerExpresion with the size of another type.
	 *
	 * @return An {@link Expression} that represents <i>integerExpression * sizeof(valueType)</i>
	 */
	protected Expression multiplyWithSizeOfAnotherType(final ILocation loc, final ICType valueType,
			final Expression integerExpression, final CPrimitive integerExpresionType) {
		return mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_multiply,
				integerExpression, integerExpresionType, calculateSizeOf(loc, valueType), integerExpresionType);
	}

	/**
	 * Calculates the size of a given type.
	 *
	 * @return The size.
	 */
	private Expression calculateSizeOf(final ILocation loc, final ICType cType) {
		return mTypeSizeAndOffsetComputer.constructBytesizeExpression(loc, cType);
	}

	@Override
	public List<Pair<Expression, Set<VariableLHS>>> constructMallocSpecificationExpressions(final ILocation tuLoc,
			final MemoryArea memoryArea, final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		return mMemoryManagementStrategy.constructMallocSpecificationExpressions(tuLoc, memoryArea,
				requiredMemoryModelFeatures, memoryModelDeclarationsHandler);
	}

	@Override
	public List<Triple<Expression, Set<VariableLHS>, Boolean>> constructDeallocSpecificationExpressions(
			final ILocation tuLoc, final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		return mMemoryManagementStrategy.constructDeallocSpecificationExpressions(tuLoc, requiredMemoryModelFeatures,
				memoryModelDeclarationsHandler);
	}

	@Override
	public List<Statement> constructUltimateInitStatements(final ILocation loc,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler, final BigInteger fixedAddressCounter) {
		return mMemoryManagementStrategy.constructUltimateInitStatements(loc, requiredMemoryModelFeatures,
				memoryModelDeclarationsHandler, fixedAddressCounter);
	}

	@Override
	public List<Pair<Expression, Set<VariableLHS>>> constructAllocInitSpecificationExpressions(final ILocation tuLoc,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		return mMemoryManagementStrategy.constructAllocInitSpecificationExpressions(tuLoc, requiredMemoryModelFeatures,
				memoryModelDeclarationsHandler);
	}

	@Override
	public ExpressionResult convertPointerToInt(final ILocation loc, final ExpressionResult rexp,
			final CPrimitive newType) {
		return mPointerIntegerConversion.convertPointerToInt(loc, rexp, newType);
	}

	@Override
	public ExpressionResult convertIntToPointer(final ILocation loc, final ExpressionResult rexp,
			final CPointer newType) {
		return mPointerIntegerConversion.convertIntToPointer(loc, rexp, newType);
	}

	protected Expression baseEqualsNull(final ILocation loc, final Expression tmpExpr,
			final CPrimitive cTypeOfPointerComponent, final Expression nullPtrExpr) {
		// res.base == 0
		return mExpressionTranslation.constructBinaryComparisonIntegerExpression(loc, IASTBinaryExpression.op_equals,
				mMemoryPointer.getPointerAddress(tmpExpr, loc), cTypeOfPointerComponent,
				mMemoryPointer.getPointerAddress(nullPtrExpr, loc), cTypeOfPointerComponent);
	}

	protected Expression baseEqual(final ILocation loc, final Expression tmpExpr,
			final CPrimitive cTypeOfPointerComponent, final Expression argSPtr) {
		// res.base == arg_s.base
		return mExpressionTranslation.constructBinaryComparisonIntegerExpression(loc, IASTBinaryExpression.op_equals,
				mMemoryPointer.getPointerAddress(tmpExpr, loc), cTypeOfPointerComponent,
				mMemoryPointer.getPointerAddress(argSPtr, loc), cTypeOfPointerComponent);
	}

	@Override
	public Expression[] constructRhsAssignmentStatementHda(final ILocation loc, final HeapDataArray hda,
			final Expression baseAddress) {
		return new Expression[] { ExpressionFactory.constructFunctionApplication(loc,
				MemoryHandler.getNameOfHeapInitFunction(hda.getName()),
				new Expression[] { hda.getIdentifierExpression(), mMemoryPointer.getPointerAddress(baseAddress, loc) },
				(BoogieType) hda.getIdentifierExpression().getType()) };
	}

	@Override
	public Expression constructPointerValidityCheckExpr(final ILocation loc, final Expression ptr,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		throw new UnsupportedOperationException("The pointer base validity check is not compatible with the selected: "
				+ this.getClass() + " addressing mode!");
	}

	@Override
	public Expression constructPointerTargetFullyAllocatedCheckExpr(final ILocation loc, final Expression ptr,
			final Expression size, final boolean isBitVectorTranslation,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		throw new UnsupportedOperationException(
				"The target pointer fully allocated check is not compatible with the selected: " + this.getClass()
						+ "  addressing mode!");
	}

	@Override
	public List<Statement> getChecksForFreeCall(final ILocation loc, final RValue pointerToBeFreed,
			final boolean isPointerCheckRequired, final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		assert pointerToBeFreed.getCType().getUnderlyingType() instanceof CPointer;

		if (!isPointerCheckRequired) {
			return Collections.emptyList();
		}

		throw new UnsupportedOperationException(
				"The check if the freed pointer is valid is not compatible with the selected: " + this.getClass()
						+ "  addressing mode!");
	}

	@Override
	public List<Statement> constructMemSafeStatementsForPointerExpression(final ILocation loc, final Expression ptr,
			final CheckMode pointerBaseValid, final CheckMode pointerTargetFullyAllocated,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		if (pointerBaseValid == CheckMode.IGNORE && pointerTargetFullyAllocated == CheckMode.IGNORE) {
			return Collections.emptyList();
		}

		throw new UnsupportedOperationException(
				"The MemSafety checks are not compatible with the selected: " + this.getClass() + "  addressing mode!");
	}

	@Override
	public Statement checksForStringCopyOverlapping(final ILocation loc, final Expression src, final Expression srcId,
			final Expression destId, final Expression dest) {
		throw new UnsupportedOperationException(
				"The string copy overlapping check is not compatible with the selected: " + this.getClass()
						+ "  addressing mode!");
	}

	/**
	 * Creates a valid expression representing a pointer subtractions of a pointer component. The component is either
	 * base or offset.
	 *
	 * @return The expression.
	 */
	protected Expression pointerComponentSubtraction(final ILocation loc, final Expression ptrComp1,
			final Expression ptrComp2, final ICType pointsToType) {
		final CPrimitive typesizeType = mExpressionTranslation.getCTypeOfPointerComponents();

		final Expression offsetDifference = mExpressionTranslation.constructArithmeticExpression(loc,
				IASTBinaryExpression.op_minus, ptrComp1, typesizeType, ptrComp2, typesizeType);

		final Expression typesize = mTypeSizeAndOffsetComputer.constructBytesizeExpression(loc, pointsToType);

		final Expression offsetDifferenceDividedByTypesize = mExpressionTranslation.constructArithmeticExpression(loc,
				IASTBinaryExpression.op_divide, offsetDifference, typesizeType, typesize, typesizeType);

		return offsetDifferenceDividedByTypesize;
	}

	@Override
	public List<Declaration> constructMetaData(final RequiredMemoryModelFeatures requiredFeatures) {
		return mMemoryMetadata.constructMetaData(requiredFeatures);
	}

	@Override
	public List<MemoryModelDeclarations> getMetaDataDeclarations() {
		return mMemoryMetadata.getMetaDataDeclarations();
	}
}
