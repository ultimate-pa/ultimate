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
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.StatementFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.FunctionDeclarations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TranslationSettings;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizeAndOffsetComputer.Offset;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.ICType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * Implements a specific memory addressing scheme for a one-dimensional memory layout.
 *
 * This class provides the logic to calculate and access memory locations within a linear, one-dimensional memory
 * structure, based on a memory pointer representation of type {@link MemoryPointer1D}. It extends
 * {@link MemoryAdressingBase} to implement the specific addressing behavior for one-dimensional memory structures.
 *
 * @author Jan Körner
 */
public class MemoryAddressing1D extends MemoryAdressingBase<MemoryPointer1D> {
	public MemoryAddressing1D(final ITypeHandler typeHandler, final ExpressionTranslation exprTranslation,
			final IBooleanArrayHelper booleanArrayHelper, final TypeSizes typeSizes,
			final TypeSizeAndOffsetComputer typeSizeAndOffsetComputer, final TranslationSettings settings,
			final FunctionDeclarations functionDeclarations, final MemoryPointer1D pointer) {
		super(typeHandler, exprTranslation, booleanArrayHelper, typeSizes, typeSizeAndOffsetComputer, pointer,
				settings.getPointerIntegerCastMode(), functionDeclarations,
				new MemoryMetadataDefault1D(typeHandler, exprTranslation, booleanArrayHelper));
		mMemoryManagementStrategy =
				new SimpleIncreasingStrategy(typeSizes, exprTranslation, typeHandler, typeSizeAndOffsetComputer,
						settings.isBitvectorTranslation(), settings.assumeHeapAllocationAlwaysSucceeds());
	}

	@Override
	public Expression doPointerArithmetic(final int operator, final ILocation loc, final Expression ptrAddress,
			final RValue integer, final ICType valueType, final CPrimitive integerExpressionType) {

		if (mTypeSizes.getSize(((CPrimitive) integer.getCType().getUnderlyingType()).getType()) != mTypeSizes
				.getSize(integerExpressionType.getType())) {
			throw new UnsupportedOperationException("not yet implemented, conversion is needed");
		}

		final Expression pointerBase = mMemoryPointer.getPointerAddress(ptrAddress, loc);
		final Expression timesSizeOf =
				multiplyWithSizeOfAnotherType(loc, valueType, integer.getValue(), integerExpressionType);

		final Expression sum = mExpressionTranslation.constructArithmeticExpression(loc, operator, pointerBase,
				integerExpressionType, timesSizeOf, integerExpressionType);

		return mMemoryPointer.createPointerFromBase(sum, loc);
	}

	@Override
	public BigInteger getFixedAddressCounterCountingStep(final Expression size) {
		return mTypeSizes.extractIntegerValue(size, new CPrimitive(CPrimitives.LONG));
	}

	@Override
	public Expression constructAddressForStructField(final ILocation loc, final Expression baseAddress,
			final Offset fieldOffset, final CPrimitive sizeT) {

		final Expression pointerBase = mMemoryPointer.getPointerAddress(baseAddress, loc);
		final Expression sum = mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_plus,
				pointerBase, sizeT, fieldOffset.getAddressOffsetAsExpression(loc), sizeT);

		return mMemoryPointer.createPointerFromBase(sum, loc);
	}

	@Override
	public Expression addIntegerConstantToPointer(final ILocation loc, final Expression ptrExpr,
			final BigInteger integerConstant) {
		final Expression integerExpr =
				mTypeSizes.constructLiteralForIntegerType(loc, mTypeSizeAndOffsetComputer.getSizeT(), integerConstant);

		return addExpressionToPointer(loc, ptrExpr, integerExpr);
	}

	@Override
	public Expression constructFunctionPointer(final ILocation loc, final BigInteger offset) {
		final Expression base = mTypeSizes.constructLiteralForIntegerType(loc,
				mExpressionTranslation.getCTypeOfPointerComponents(), mFunctionPointerPointerBaseValue);

		final Expression integerExpr =
				mTypeSizes.constructLiteralForIntegerType(loc, mTypeSizeAndOffsetComputer.getSizeT(), offset);

		final Expression baseMinus =
				mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_minus, base,
						mTypeSizeAndOffsetComputer.getSizeT(), integerExpr, mTypeSizeAndOffsetComputer.getSizeT());

		return mMemoryPointer.createPointerFromBase(baseMinus, loc);
	}

	@Override
	public Expression addExpressionToPointer(final ILocation loc, final Expression ptrExpr, final Expression expr) {
		final Expression base = mMemoryPointer.getPointerAddress(ptrExpr, loc);

		final Expression basePlus =
				mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_plus, base,
						mTypeSizeAndOffsetComputer.getSizeT(), expr, mTypeSizeAndOffsetComputer.getSizeT());

		return mMemoryPointer.createPointerFromBase(basePlus, loc);
	}

	@Override
	public Expression getLastCharOfString(final ILocation loc, final CPrimitive sizeT, final IdentifierExpression len,
			final IdentifierExpression returnValue) {
		final var lenMinusOne = mExpressionTranslation.constructArithmeticIntegerExpression(loc,
				IASTBinaryExpression.op_minus, mExpressionTranslation.applyWraparound(loc, sizeT, len), sizeT,
				mTypeSizes.constructLiteralForIntegerType(loc, sizeT, BigInteger.ONE), sizeT);

		return mMemoryPointer.createPointerFromBase(lenMinusOne, loc);
	}

	@Override
	public AssumeStatement constructStrChrAssumeStatement(final ILocation loc, final Expression tmpExpr,
			final Expression argSPtr, final Expression nullPtrExpr,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		// TODO check if this is valid, we cannot check for in range in the one dimensional model
		final var cTypeOfPointerComponent = mExpressionTranslation.getCTypeOfPointerComponents();

		final var baseEqualNull = baseEqualsNull(loc, tmpExpr, cTypeOfPointerComponent, nullPtrExpr);
		final var baseEqual = baseEqual(loc, tmpExpr, cTypeOfPointerComponent, argSPtr);

		return new AssumeStatement(loc,
				ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, baseEqualNull, baseEqual));
	}

	@Override
	public Expression constructInitialPointerFromPointer(final ILocation loc, final Expression ptr) {
		return mMemoryPointer.createPointerFromBase(mMemoryPointer.getPointerAddress(ptr, loc), loc);
	}

	@Override
	public Expression doPointerSubtraction(final ILocation loc, final Expression ptr1, final Expression ptr2,
			final ICType pointsToType) {
		final Expression ptr1Base = mMemoryPointer.getPointerAddress(ptr1, loc);
		final Expression ptr2Base = mMemoryPointer.getPointerAddress(ptr2, loc);

		return pointerComponentSubtraction(loc, ptr1Base, ptr2Base, pointsToType);
	}

	@Override
	public List<Statement> constructReallocBodyStatements(final ILocation loc, final String procName,
			final Collection<HeapDataArray> heapDataArrays, final BoogieType pointerType,
			final IdentifierExpression ptrIdExprImpl, final VariableLHS resultLhsImpl,
			final IdentifierExpression resultExprImpl, final IdentifierExpression sizeIdExprImpl,
			final RequiredMemoryModelFeatures requiredFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {

		final List<Statement> stmts = new ArrayList<>();

		final CallStatement call =
				StatementFactory.constructCallStatement(loc, false, new VariableLHS[] { resultLhsImpl }, SFO.C_MEMCPY,
						new Expression[] { resultExprImpl, ptrIdExprImpl, sizeIdExprImpl });

		// add marker for global declaration to memory handler
		MemoryModelExpressionHelper.requireMemoryModelFeature(MemoryModelDeclarations.C_MEMCPY, requiredFeatures,
				memoryModelDeclarationsHandler);

		stmts.add(call);

		return stmts;
	}

	@Override
	public Expression constructPointerValidityCheckExpr(final ILocation loc, final Expression ptr,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		throw new UnsupportedOperationException("The pointer validity check is not available with the 1D Addressing");

	}

	@Override
	public Expression getValidArray(final ILocation loc, final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		throw new UnsupportedOperationException(
				"The valid array is not part of the metadata values from the 1D Addressing");

	}
}
