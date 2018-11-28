/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2017-2018 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;
import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.IDispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TypeHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.StructHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizeAndOffsetComputer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizeAndOffsetComputer.Offset;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfo;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfoBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CFunction;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CNamed;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStructOrUnion;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class ExpressionResultTransformer {

	private final CHandler mCHandler;
	private final MemoryHandler mMemoryHandler;
	private final StructHandler mStructHandler;
	private final ExpressionTranslation mExprTrans;
	private final TypeSizes mTypeSizes;
	private final AuxVarInfoBuilder mAuxVarInfoBuilder;
	private final ITypeHandler mTypeHandler;
	private final TypeSizeAndOffsetComputer mTypeSizeAndOffsetComputer;

	public ExpressionResultTransformer(final CHandler chandler, final MemoryHandler memoryHandler,
			final StructHandler structHandler, final ExpressionTranslation exprTrans, final TypeSizes typeSizes,
			final AuxVarInfoBuilder auxVarInfoBuilder, final ITypeHandler typeHandler,
			final TypeSizeAndOffsetComputer typeAndOffsetComputer) {
		mCHandler = chandler;
		mMemoryHandler = memoryHandler;
		mStructHandler = structHandler;
		mExprTrans = exprTrans;
		mTypeSizes = typeSizes;
		mAuxVarInfoBuilder = auxVarInfoBuilder;
		mTypeHandler = typeHandler;
		mTypeSizeAndOffsetComputer = typeAndOffsetComputer;
	}

	/**
	 * Dispatch a function argument and do conversions that are applied to all function arguments:
	 * <ul>
	 * <li>dispatch
	 * <li>decayArrayToPointer
	 * <li>switchToRValueIfNecessary
	 * </ul>
	 */
	public ExpressionResult dispatchDecaySwitchToRValueFunctionArgument(final IDispatcher main, final ILocation loc,
			final IASTInitializerClause initClause) {
		final ExpressionResult dispatched = (ExpressionResult) main.dispatch(initClause);
		final ExpressionResult converted = mCHandler.decayArrayToPointer(dispatched, loc, initClause);
		return switchToRValueAndRexBoolToIntIfNecessary(converted, loc, initClause);
	}

	/**
	 * Dispatch a function argument and do conversions that are applied to all function arguments:
	 * <ul>
	 * <li>dispatch
	 * <li>decayArrayToPointer
	 * <li>switchToRValueIfNecessary
	 * <li>convert
	 * </ul>
	 *
	 * @param newTypeRaw
	 */
	public ExpressionResult dispatchDecaySwitchToRValueConvertFunctionArgument(final IDispatcher main,
			final ILocation loc, final IASTInitializerClause initClause, final CType newTypeRaw) {
		final ExpressionResult dispatched = (ExpressionResult) main.dispatch(initClause);
		final ExpressionResult converted = mCHandler.decayArrayToPointer(dispatched, loc, initClause);
		final ExpressionResult switched = switchToRValueIfNecessary(converted, loc, initClause);
		return convert(loc, switched, newTypeRaw);
	}

	public ExpressionResult switchToRValueAndRexBoolToIntIfNecessary(final ExpressionResult old, final ILocation loc,
			final IASTNode hook) {
		final ExpressionResult switchResult = switchToRValueIfNecessary(old, loc, hook);
		return rexBoolToIntIfNecessary(switchResult, loc);
	}

	public ExpressionResult switchToRValueAndRexIntToBoolIfNecessary(final ExpressionResult old, final ILocation loc,
			final IASTNode hook) {
		final ExpressionResult switchResult = switchToRValueIfNecessary(old, loc, hook);
		return rexIntToBoolIfNecessary(switchResult, loc);
	}

	public ExpressionResult switchToRValueIfNecessary(final ExpressionResult old, final ILocation loc,
			final IASTNode hook) {

		final ExpressionResult result;
		if (old.getLrValue() == null) {
			return old;
		} else if (old.getLrValue() instanceof RValue) {
			final ExpressionResult replaced = replaceCFunctionByCPointer(old);
			return replaceEnumByInt(replaced);
		} else if (old.getLrValue() instanceof LocalLValue) {
			final CType underlyingType = old.getLrValue().getCType().getUnderlyingType();
			mCHandler.moveArrayAndStructIdsOnHeap(loc, underlyingType, old.getLrValue().getValue(), old.getAuxVars(),
					hook);

			final CType resultType;
			if (underlyingType instanceof CArray) {
				resultType = new CPointer(((CArray) underlyingType).getValueType());
			} else if (underlyingType instanceof CFunction) {
				resultType = new CPointer(underlyingType);
			} else if (underlyingType instanceof CEnum) {
				resultType = new CPrimitive(CPrimitives.INT);
			} else {
				resultType = underlyingType;
			}
			final RValue newRVal = new RValue(((LocalLValue) old.getLrValue()).getValue(), resultType,
					old.getLrValue().isBoogieBool());
			result = new ExpressionResultBuilder(old).setOrResetLrValue(newRVal).build();
		} else if (old.getLrValue() instanceof HeapLValue) {
			final HeapLValue hlv = (HeapLValue) old.getLrValue();
			CType underlyingType = old.getLrValue().getCType().getUnderlyingType();
			if (underlyingType instanceof CEnum) {
				underlyingType = new CPrimitive(CPrimitives.INT);
			}

			final RValue newValue;
			if (underlyingType instanceof CPrimitive) {
				final ExpressionResult rex = mMemoryHandler.getReadCall(hlv.getAddress(), underlyingType, hook);
				newValue = (RValue) rex.getLrValue();
				result = new ExpressionResultBuilder().addAllExceptLrValue(old, rex).setLrValue(newValue).build();
			} else if (underlyingType instanceof CPointer) {
				final ExpressionResult rex = mMemoryHandler.getReadCall(hlv.getAddress(), underlyingType, hook);
				newValue = (RValue) rex.getLrValue();
				result = new ExpressionResultBuilder().addAllExceptLrValue(old, rex).setLrValue(newValue).build();
			} else if (underlyingType instanceof CArray) {
				final CArray cArray = (CArray) underlyingType;
				newValue = new RValue(hlv.getAddress(), new CPointer(cArray.getValueType()), false, false);
				result = new ExpressionResultBuilder().addAllExceptLrValue(old).setLrValue(newValue).build();
			} else if (underlyingType instanceof CEnum) {
				throw new AssertionError("handled above");
			} else if (underlyingType instanceof CStructOrUnion) {
				final ExpressionResult rex =
						readStructFromHeap(old, loc, hlv.getAddress(), (CStructOrUnion) underlyingType, hook);
				newValue = (RValue) rex.getLrValue();
				result = new ExpressionResultBuilder().addAllExceptLrValue(old, rex).setLrValue(newValue).build();
			} else if (underlyingType instanceof CNamed) {
				throw new AssertionError("This should not be the case as we took the underlying type.");
			} else if (underlyingType instanceof CFunction) {
				newValue = new RValue(hlv.getAddress(), new CPointer(underlyingType), false, false);
				result = new ExpressionResultBuilder().addAllExceptLrValue(old).setLrValue(newValue).build();
			} else {
				throw new UnsupportedSyntaxException(loc, "..");
			}
		} else {
			throw new AssertionError("an LRValue that is not null, and no LocalLValue, RValue or HeapLValue???");
		}
		return result;
	}

	/**
	 * Read the contents of a struct (given as a pointer) from the heap recursively (for nested structs) returning a
	 * StructConstructor.
	 *
	 * @param mStructHandler
	 * @param mMemoryHandler
	 * @param loc
	 * @param structOnHeapAddress
	 * @param structType
	 * @param mExprTrans
	 * @param mTypeSizes
	 * @param mAuxVarInfoBuilder
	 * @param mCHandler
	 *
	 * @return A result whose value is a StructConstructor and whose statements make the necessary calls to fill the
	 *         items inside the StructConstructor correctly
	 */
	ExpressionResult readStructFromHeap(final ExpressionResult old, final ILocation loc,
			final Expression structOnHeapAddress, final CStructOrUnion structType, final IASTNode hook) {

		final Expression startAddress = structOnHeapAddress;
		final Expression currentStructBaseAddress = MemoryHandler.getPointerBaseAddress(startAddress, loc);
		final Expression currentStructOffset = MemoryHandler.getPointerOffset(startAddress, loc);

		// everything for the new Result
		final ArrayList<Statement> newStmt = new ArrayList<>();
		final ArrayList<Declaration> newDecl = new ArrayList<>();
		final Set<AuxVarInfo> newAuxVars = new LinkedHashSet<>();

		final String[] fieldIds = structType.getFieldIds();
		final CType[] fieldTypes = structType.getFieldTypes();

		// the new Arrays for the StructConstructor
		final ArrayList<String> fieldIdentifiers = new ArrayList<>();
		final ArrayList<Expression> fieldValues = new ArrayList<>();

		for (int i = 0; i < fieldIds.length; i++) {
			fieldIdentifiers.add(fieldIds[i]);

			CType underlyingType;
			if (fieldTypes[i] instanceof CNamed) {
				underlyingType = ((CNamed) fieldTypes[i]).getUnderlyingType();
			} else {
				underlyingType = fieldTypes[i];
			}

			// ResultExpression fieldRead = null;
			final LRValue fieldLRVal;
			if (underlyingType instanceof CPrimitive) {
				final ExpressionResult fieldRead = (ExpressionResult) mStructHandler.readFieldInTheStructAtAddress(loc,
						i, structOnHeapAddress, structType, hook);
				fieldLRVal = fieldRead.getLrValue();
				newStmt.addAll(fieldRead.getStatements());
				newDecl.addAll(fieldRead.getDeclarations());
				newAuxVars.addAll(fieldRead.getAuxVars());
			} else if (underlyingType instanceof CPointer) {
				final ExpressionResult fieldRead = (ExpressionResult) mStructHandler.readFieldInTheStructAtAddress(loc,
						i, structOnHeapAddress, structType, hook);
				fieldLRVal = fieldRead.getLrValue();
				newStmt.addAll(fieldRead.getStatements());
				newDecl.addAll(fieldRead.getDeclarations());
				newAuxVars.addAll(fieldRead.getAuxVars());
			} else if (underlyingType instanceof CArray) {
				final ExpressionResult xres1 =
						readArrayFromHeap(old, loc, structOnHeapAddress, (CArray) underlyingType, hook);
				final ExpressionResult xres = xres1;

				fieldLRVal = xres.getLrValue();
				newStmt.addAll(xres.getStatements());
				newDecl.addAll(xres.getDeclarations());
				newAuxVars.addAll(xres.getAuxVars());

			} else if (underlyingType instanceof CEnum) {
				// like CPrimitive..
				final ExpressionResult fieldRead = (ExpressionResult) mStructHandler.readFieldInTheStructAtAddress(loc,
						i, structOnHeapAddress, structType, hook);
				fieldLRVal = fieldRead.getLrValue();
				newStmt.addAll(fieldRead.getStatements());
				newDecl.addAll(fieldRead.getDeclarations());
				newAuxVars.addAll(fieldRead.getAuxVars());
			} else if (underlyingType instanceof CStructOrUnion) {

				final Offset innerStructOffset =
						mTypeSizeAndOffsetComputer.constructOffsetForField(loc, structType, i, hook);
				if (innerStructOffset.isBitfieldOffset()) {
					throw new UnsupportedOperationException("Bitfield read struct from heap");
				}

				final Expression offsetSum = mExprTrans.constructArithmeticExpression(loc, IASTBinaryExpression.op_plus,
						currentStructOffset, mExprTrans.getCTypeOfPointerComponents(), innerStructOffset.getAddressOffsetAsExpression(loc),
						mExprTrans.getCTypeOfPointerComponents());
				final Expression innerStructAddress =
						MemoryHandler.constructPointerFromBaseAndOffset(currentStructBaseAddress, offsetSum, loc);

				final ExpressionResult fieldRead =
						readStructFromHeap(old, loc, innerStructAddress, (CStructOrUnion) underlyingType, hook);

				fieldLRVal = fieldRead.getLrValue();
				newStmt.addAll(fieldRead.getStatements());
				newDecl.addAll(fieldRead.getDeclarations());
				newAuxVars.addAll(fieldRead.getAuxVars());
			} else if (underlyingType instanceof CNamed) {
				throw new AssertionError("This should not be the case as we took the underlying type.");
			} else {
				throw new UnsupportedSyntaxException(loc, "..");
			}

			if (fieldLRVal instanceof RValue) {
				fieldValues.add(fieldLRVal.getValue());
			} else if (fieldLRVal instanceof HeapLValue) {
				fieldValues.add(((HeapLValue) fieldLRVal).getAddress());
			} else {
				throw new UnsupportedOperationException();
			}

		}
		final StructConstructor sc = ExpressionFactory.constructStructConstructor(loc,
				fieldIdentifiers.toArray(new String[fieldIdentifiers.size()]),
				fieldValues.toArray(new Expression[fieldValues.size()]));

		final ExpressionResult result = new ExpressionResult(newStmt, new RValue(sc, structType), newDecl, newAuxVars,
				old.getOverapprs(), old.getNeighbourUnionFields());
		return result;
	}

	/**
	 * Copy the contents of a given on-heap array (given via address parameter) in to a fresh Boogie array. Introduces a
	 * fresh auxvar for the Boogie Array, which is the LRValue of the returned expression result.
	 *
	 * @param mStructHandler
	 * @param mMemoryHandler
	 * @param loc
	 * @param address
	 * @param arrayType
	 * @param mCHandler
	 *
	 * @return
	 */
	ExpressionResult readArrayFromHeap(final ExpressionResult old, final ILocation loc, final Expression address,
			final CArray arrayType, final IASTNode hook) {
		final CType arrayValueType = arrayType.getValueType().getUnderlyingType();
		if (arrayValueType instanceof CArray) {
			throw new UnsupportedSyntaxException(loc,
					"we need to generalize this to nested and/or variable length arrays");
		}

		final BigInteger boundBigInteger = mTypeSizes.extractIntegerValue(arrayType.getBound(), hook);
		if (boundBigInteger == null) {
			throw new UnsupportedSyntaxException(loc, "variable length arrays not yet supported by this method");
		}
		final int bound = boundBigInteger.intValue();
		final AuxVarInfo newArrayAuxvar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, arrayType, SFO.AUXVAR.ARRAYCOPY);
		final LRValue resultValue = new RValueForArrays(newArrayAuxvar.getExp(), arrayType);
		ExpressionResultBuilder builder = new ExpressionResultBuilder();
		builder.addDeclaration(newArrayAuxvar.getVarDec());
		builder.addAuxVar(newArrayAuxvar);

		final Expression newStartAddressBase;
		final Expression newStartAddressOffset;
		if (address instanceof StructConstructor) {
			final StructConstructor structCtorAddress = (StructConstructor) address;
			newStartAddressBase = structCtorAddress.getFieldValues()[0];
			newStartAddressOffset = structCtorAddress.getFieldValues()[1];
		} else {
			newStartAddressBase = MemoryHandler.getPointerBaseAddress(address, loc);
			newStartAddressOffset = MemoryHandler.getPointerOffset(address, loc);
		}

		final Expression valueTypeSize = mMemoryHandler.calculateSizeOf(loc, arrayValueType, hook);

		Expression arrayEntryAddressOffset = newStartAddressOffset;

		for (int pos = 0; pos < bound; pos++) {

			final Expression readAddress =
					MemoryHandler.constructPointerFromBaseAndOffset(newStartAddressBase, arrayEntryAddressOffset, loc);
			final ExpressionResult readRex;
			if (arrayValueType instanceof CStructOrUnion) {
				readRex = readStructFromHeap(old, loc, readAddress, (CStructOrUnion) arrayValueType, hook);
			} else {
				readRex = mMemoryHandler.getReadCall(readAddress, arrayType.getValueType(), hook);
			}
			builder.addAllExceptLrValue(readRex);
			builder.setOrResetLrValue(readRex.getLrValue());

			final ArrayLHS arrayAccLhs = ExpressionFactory.constructNestedArrayLHS(loc, newArrayAuxvar.getLhs(),
					new Expression[] { mTypeSizes.constructLiteralForIntegerType(loc, new CPrimitive(CPrimitives.INT),
							BigInteger.valueOf(pos)) });
			final ExpressionResult assRex =
					mCHandler.makeAssignment(loc, new LocalLValue(arrayAccLhs, arrayType.getValueType(), null),
							Collections.emptyList(), builder.build(), hook);
			builder = new ExpressionResultBuilder().addAllExceptLrValue(assRex).setLrValue(assRex.getLrValue());

			arrayEntryAddressOffset = mExprTrans.constructArithmeticExpression(loc, IASTBinaryExpression.op_plus,
					arrayEntryAddressOffset, mExprTrans.getCTypeOfPointerComponents(), valueTypeSize,
					mExprTrans.getCTypeOfPointerComponents());
		}
		builder.setOrResetLrValue(resultValue);
		return builder.build();
	}

	/**
	 * Convert Expression of some type to an expression of boolean type. If the expression expr
	 * <ul>
	 * <li>has type boolean we return expr
	 * <li>has type int we return <i>expr != 0</i>
	 * <li>has type real we return <i>expr != 0.0</i>
	 * <li>has type $Pointer$ we return <i>expr != #NULL</i>
	 * </ul>
	 * Other types are not supported. If the expression was obtained by a conversion from bool to int, we try to get rid
	 * of the former conversion instead of applying a new one.
	 */
	private static RValue toBoolean(final ILocation loc, final RValue rVal,
			final ExpressionTranslation expressionTranslation) {
		assert !rVal.isBoogieBool();
		final CType underlyingType = CEnum.replaceEnumWithInt(rVal.getCType().getUnderlyingType());
		final Expression zero = expressionTranslation.constructZero(loc, underlyingType);

		final Expression resultEx;
		if (underlyingType instanceof CPrimitive) {
			resultEx = expressionTranslation.constructBinaryEqualityExpression(loc, IASTBinaryExpression.op_notequals,
					rVal.getValue(), rVal.getCType(), zero, underlyingType);
		} else if (underlyingType instanceof CPointer) {
			resultEx = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.COMPNEQ, rVal.getValue(),
					zero);
		} else {
			throw new UnsupportedSyntaxException(loc, "unsupported type " + underlyingType);
		}
		return new RValue(resultEx, new CPrimitive(CPrimitives.INT), true);
	}

	/**
	 * int <code>x</code> of form <code>y ? 1 : 0</code> becomes <code>!y ? 1 : 0</code> /** int <code>x</code> becomes
	 * <code>x == 0 ? 1 : 0</code>
	 */
	public ExpressionResult rexIntToBoolIfNecessary(final ExpressionResult old, final ILocation loc) {
		if (!(old.getLrValue() instanceof RValue)) {
			throw new UnsupportedOperationException("only RValue can switch");
		}
		if (old.getLrValue().isBoogieBool()) {
			return old;
		}
		return new ExpressionResultBuilder(old).setOrResetLrValue(toBoolean(loc, (RValue) old.getLrValue(), mExprTrans))
				.build();
	}

	/**
	 * boolean <code>p</code> becomes <code>!p ? 1 : 0</code>
	 *
	 */
	public ExpressionResult rexBoolToIntIfNecessary(final ExpressionResult old, final ILocation loc) {
		if (old.getLrValue() == null) {
			/*
			 * This ExpressionResult does not have a value (for example it may be the translation of a call to a void
			 * function). Void values like this are allowed for example in something like <code>0 ? foo() : 0</code>
			 * where foo is void. Do nothing here.
			 */
			return old;
		}

		if (!(old.getLrValue() instanceof RValue)) {
			throw new UnsupportedOperationException("only RValue can switch");
		}
		if (old.getLrValue().isBoogieBool()) {
			return new ExpressionResultBuilder(old)
					.setOrResetLrValue(RValue.boolToInt(loc, (RValue) old.getLrValue(), mTypeSizes)).build();
		}
		return old;
	}

	public ExpressionResult makeRepresentationReadyForConversionAndRexBoolToIntIfNecessary(final ExpressionResult expr,
			final CHandler main, final ILocation loc, final CType targetCType, final IASTNode hook) {
		final ExpressionResult readyExpr = makeRepresentationReadyForConversion(expr, main, loc, targetCType, hook);
		return rexBoolToIntIfNecessary(readyExpr, loc);
	}

	/**
	 * Switch our representation of the {@link ExpressionResult}'s value such that it can be converted to the
	 * targetCType. If the targetCType is a pointer or a primitive type and the type of this expression result is an
	 * {@link CArray} the array is decayed to a pointer, otherwise we just switch to an RValue.
	 */
	public ExpressionResult makeRepresentationReadyForConversion(final ExpressionResult expr, final CHandler main,
			final ILocation loc, final CType targetCType, final IASTNode hook) {
		if (expr.getLrValue().getCType().getUnderlyingType() instanceof CArray
				&& (targetCType.getUnderlyingType() instanceof CPointer
						|| targetCType.getUnderlyingType() instanceof CPrimitive)) {
			final ExpressionResultBuilder erb = new ExpressionResultBuilder().addAllExceptLrValue(expr);
			final RValue decayed = main.decayArrayLrValToPointer(loc, expr.getLrValue(), hook);
			return erb.setLrValue(decayed).build();
		}
		return switchToRValueIfNecessary(expr, loc, hook);
	}

	/**
	 * If the CType of this {@link ExpressionResult}'s {@link RValue} has CType enum, then replace it by CType int. If
	 * an enum variable occurs as an RValue we use this method to replace its type by int.
	 *
	 */
	private static ExpressionResult replaceEnumByInt(final ExpressionResult old) {
		if (old.getLrValue() instanceof RValue) {
			final RValue oldRValue = (RValue) old.getLrValue();
			if (oldRValue.getCType() instanceof CEnum) {
				final CPrimitive intType = new CPrimitive(CPrimitives.INT);
				return new ExpressionResultBuilder(old).setOrResetLrValue(new RValue(oldRValue.getValue(), intType,
						oldRValue.isBoogieBool(), oldRValue.isIntFromPointer())).build();
			}
			return old;
		}
		throw new UnsupportedOperationException("replaceEnumByInt only applicable for RValues");
	}

	/**
	 * If the CType of this {@link ExpressionResult}'s {@link RValue} has CType CFunction, then replace it by CType
	 * CPointer. If a function occurs as an RValue we use this method to replace its type by CPointer. 6.3.2.1 of C11
	 * says: A function designator is an expression that has function type. Except when it is the operand of the sizeof
	 * operator, the _Alignof operator,65) or the unary & operator, a function designator with type ‘‘function returning
	 * type’’ is converted to an expression that has type ‘‘pointer to function returning type’’.
	 *
	 */
	private static ExpressionResult replaceCFunctionByCPointer(final ExpressionResult old) {
		if (old.getLrValue() instanceof RValue) {
			final RValue oldRValue = (RValue) old.getLrValue();
			if (oldRValue.getCType() instanceof CFunction) {
				final CPointer pointerType = new CPointer(oldRValue.getCType());
				final RValue newRValue = new RValue(oldRValue.getValue(), pointerType, oldRValue.isBoogieBool(),
						oldRValue.isIntFromPointer());
				return new ExpressionResultBuilder(old).setOrResetLrValue(newRValue).build();
			}
			return old;
		}
		throw new UnsupportedOperationException("replaceEnumByInt only applicable for RValues");
	}

	/**
	 * Handle implicit conversions according to Section 6.3 of C11.
	 *
	 * See also {@link ExpressionTranslation#usualArithmeticConversions(ILocation, ExpressionResult, ExpressionResult)}.
	 *
	 * Modifies a given {@link ExpressionResult} such that the effect of a cast from the current {@link CType} of the
	 * {@link ExpressionResult} to resultType is captured. Method may exchange the {@link RValue} of the
	 * {@link ExpressionResult} and add additional objects (statements, auxVars, etc.).
	 *
	 */
	public ExpressionResult convert(final ILocation loc, final ExpressionResult expr, final CType newTypeRaw) {
		final RValue rValIn = (RValue) expr.getLrValue();
		final CType newType = newTypeRaw.getUnderlyingType();

		final CType oldType = rValIn.getCType().getUnderlyingType();

		final BoogieType oldBoogieType = (BoogieType) expr.getLrValue().getValue().getType();
		final BoogieType newBoogieType = mTypeHandler.getBoogieTypeForCType(newTypeRaw);

		if (TypeHandler.areMatchingTypes(newType, oldType) && oldBoogieType.equals(newBoogieType)) {
			// types are already identical -- nothing to do
			return expr;
		}

		if (newType instanceof CPrimitive) {
			final CPrimitive cPrimitive = (CPrimitive) newType;
			if (cPrimitive.isIntegerType()) {
				return convertToIntegerType(loc, expr, (CPrimitive) newType);
			}
			if (cPrimitive.isRealFloatingType()) {
				return convertToFloatingType(loc, expr, (CPrimitive) newType);
			}
			if (cPrimitive.getType().equals(CPrimitives.VOID)) {
				return convertToVoid(loc, expr, (CPrimitive) newType);
			}
			throw new AssertionError("unknown type " + newType);
		}
		if (newType instanceof CPointer) {
			return convertToPointer(loc, expr, (CPointer) newType);
		}
		if (newType instanceof CEnum) {
			// C standard 6.4.4.3.2
			// An identifier declared as an enumeration constant has type int.
			return convertToIntegerType(loc, expr, new CPrimitive(CPrimitives.INT));
		}
		if (newType instanceof CArray) {
			throw new AssertionError("cannot convert to CArray");
		}
		if (newType instanceof CFunction) {
			throw new AssertionError("cannot convert to CFunction");
		}
		if (newType instanceof CStructOrUnion) {
			throw new UnsupportedSyntaxException(loc, "conversion to CStruct not implemented.");
		}
		throw new AssertionError("unknown type " + newType);
	}

	private ExpressionResult convertToIntegerType(final ILocation loc, final ExpressionResult rexp,
			final CPrimitive newType) {
		assert rexp.getLrValue() instanceof RValue : "has to be converted to RValue";
		final CType oldType = rexp.getLrValue().getCType().getUnderlyingType();
		if (oldType instanceof CPrimitive) {
			final CPrimitive cPrimitive = (CPrimitive) oldType;
			if (cPrimitive.isIntegerType()) {
				return mExprTrans.convertIntToInt(loc, rexp, newType);
			}
			if (cPrimitive.isRealFloatingType()) {
				return mExprTrans.convertFloatToInt(loc, rexp, newType);
			}
			if (cPrimitive.getType().equals(CPrimitives.VOID)) {
				throw new IncorrectSyntaxException(loc, "cannot convert from void");
			}
			throw new AssertionError("unknown type " + newType);
		}
		if (oldType instanceof CPointer) {
			return mExprTrans.convertPointerToInt(loc, rexp, newType);
		}
		if (oldType instanceof CEnum) {
			return mExprTrans.convertIntToInt(loc, rexp, newType);
		}
		if (oldType instanceof CArray) {
			throw new AssertionError("cannot convert from CArray");
		}
		if (oldType instanceof CFunction) {
			throw new AssertionError("cannot convert from CFunction");
		}
		if (oldType instanceof CStructOrUnion) {
			throw new UnsupportedSyntaxException(loc, "conversion from CStruct not implemented.");
		}
		throw new AssertionError("unknown type " + newType);
	}

	private ExpressionResult convertToPointer(final ILocation loc, final ExpressionResult rexp,
			final CPointer newType) {
		assert rexp.getLrValue() instanceof RValue : "has to be converted to RValue";
		final CType oldType = rexp.getLrValue().getCType().getUnderlyingType();
		if (oldType instanceof CPrimitive) {
			final CPrimitive cPrimitive = (CPrimitive) oldType;
			if (cPrimitive.isIntegerType()) {
				return mExprTrans.convertIntToPointer(loc, rexp, newType);
			}
			if (cPrimitive.isRealFloatingType()) {
				throw new IncorrectSyntaxException(loc, "cannot convert float to pointer");
			}
			if (cPrimitive.getType().equals(CPrimitives.VOID)) {
				throw new IncorrectSyntaxException(loc, "cannot convert from void");
			}
			throw new AssertionError("unknown type " + newType);
		}
		if (oldType instanceof CPointer) {
			return convertPointerToPointer(loc, rexp, newType);
		}
		if (oldType instanceof CEnum) {
			return mExprTrans.convertIntToPointer(loc, rexp, newType);
		}
		if (oldType instanceof CArray) {
			if (rexp instanceof StringLiteralResult) {
				/*
				 * a string literal's char-array decays to a pointer the stringLiteralResult already has the correct
				 * RValue, we just need to change the type
				 */
				final RValue rVal =
						new RValue(rexp.getLrValue().getValue(), new CPointer(new CPrimitive(CPrimitives.CHAR)));
				return new ExpressionResultBuilder().addAllExceptLrValue(rexp).setLrValue(rVal).build();
			}
			throw new AssertionError("cannot convert from CArray");
		}
		if (oldType instanceof CFunction) {
			throw new AssertionError("cannot convert from CFunction");
		}
		if (oldType instanceof CStructOrUnion) {
			throw new UnsupportedSyntaxException(loc, "conversion from CStruct not implemented.");
		}
		throw new AssertionError("unknown type " + newType);
	}

	private static ExpressionResult convertPointerToPointer(final ILocation loc, final ExpressionResult rexp,
			final CPointer newType) {
		// TODO: check if types are compatible
		assert rexp.getLrValue() instanceof RValue : "has to be converted to RValue";
		final RValue oldRvalue = (RValue) rexp.getLrValue();
		assert oldRvalue.getCType() instanceof CPointer : "has to be pointer";
		final RValue rVal = new RValue(oldRvalue.getValue(), newType);
		return new ExpressionResultBuilder().addAllExceptLrValue(rexp).setLrValue(rVal).build();
	}

	private static ExpressionResult convertToVoid(final ILocation loc, final ExpressionResult rexp,
			final CPrimitive newType) {
		assert rexp.getLrValue() instanceof RValue : "has to be converted to RValue";
		final CType oldType = rexp.getLrValue().getCType().getUnderlyingType();
		if (oldType instanceof CPrimitive) {
			// ok
		} else if (oldType instanceof CPointer) {
			// ok
		} else if (oldType instanceof CEnum) {
			// ok
		} else if (oldType instanceof CArray) {
			throw new AssertionError("cannot convert from CArray");
		} else if (oldType instanceof CFunction) {
			throw new AssertionError("cannot convert from CFunction");
		} else if (oldType instanceof CStructOrUnion) {
			if (newType.getType() == CPrimitives.VOID) {
				// ok: we just keep the old value but change the type
				// alternative might be to set the value to null because it should never be used
			} else {
				throw new UnsupportedSyntaxException(loc, "cannot convert from CStruct to " + newType);
			}
		} else {
			throw new AssertionError("unknown type " + newType);
		}
		final RValue oldRValue = (RValue) rexp.getLrValue();
		final RValue rVal =
				new RValue(oldRValue.getValue(), newType, oldRValue.isBoogieBool(), oldRValue.isIntFromPointer());
		return new ExpressionResultBuilder().addAllExceptLrValue(rexp).setLrValue(rVal).build();
	}

	private ExpressionResult convertToFloatingType(final ILocation loc, final ExpressionResult rexp,
			final CPrimitive newType) {
		assert rexp.getLrValue() instanceof RValue : "has to be converted to RValue";
		final CType oldType = rexp.getLrValue().getCType().getUnderlyingType();
		if (oldType instanceof CPrimitive) {
			final CPrimitive cPrimitive = (CPrimitive) oldType;
			if (cPrimitive.isIntegerType()) {
				return mExprTrans.convertIfNecessary(loc, rexp, newType);
			}
			if (cPrimitive.isRealFloatingType()) {
				return mExprTrans.convertIfNecessary(loc, rexp, newType);
			}
			if (cPrimitive.getType().equals(CPrimitives.VOID)) {
				throw new IncorrectSyntaxException(loc, "cannot convert from void");
			}
			throw new AssertionError("unknown type " + newType);
		}
		if (oldType instanceof CPointer) {
			throw new IncorrectSyntaxException(loc, "cannot convert pointer to float");
		}
		if (oldType instanceof CEnum) {
			return mExprTrans.convertIfNecessary(loc, rexp, newType);
		}
		if (oldType instanceof CArray) {
			throw new AssertionError("cannot convert from CArray");
		}
		if (oldType instanceof CFunction) {
			throw new AssertionError("cannot convert from CFunction");
		}
		if (oldType instanceof CStructOrUnion) {
			throw new UnsupportedSyntaxException(loc, "conversion from CStruct not implemented.");
		}
		throw new AssertionError("unknown type " + newType);
	}

}
