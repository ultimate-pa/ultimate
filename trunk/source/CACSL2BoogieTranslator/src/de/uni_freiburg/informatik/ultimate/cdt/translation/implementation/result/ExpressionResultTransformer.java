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
import java.util.List;
import java.util.Objects;
import java.util.Set;

import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.StatementFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CompatibleTypes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.DataRaceChecker;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.IDispatcher;
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
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitiveCategory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStructOrUnion;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.ICType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO.AUXVAR;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class ExpressionResultTransformer {

	public enum Transformation {
		/**
		 * @see ExpressionResultTransformer#switchToRValue(ExpressionResult, ILocation, IASTNode)
		 */
		SWITCH_TO_RVALUE((ert, expr, ttype, loc, hook) -> ert.switchToRValue(expr, loc, hook)),

		/**
		 * @see ExpressionResultTransformer#rexBoolToInt(ExpressionResult, ILocation)
		 */
		REX_BOOL_TO_INT((ert, expr, ttype, loc, hook) -> ert.rexBoolToInt(expr, loc)),

		/**
		 * @see ExpressionResultTransformer#rexIntToBool(ExpressionResult, ILocation)
		 */
		REX_INT_TO_BOOL((ert, expr, ttype, loc, hook) -> ert.rexIntToBool(expr, loc)),

		/**
		 * @see ExpressionResultTransformer#decayArrayToPointer(ExpressionResult, ILocation, IASTNode)
		 */
		DECAY_ARRAY_TO_POINTER((ert, expr, ttype, loc, hook) -> ert.decayArrayToPointer(expr, loc, hook)),

		/**
		 * @see ExpressionResultTransformer#performImplicitConversion(ExpressionResult, CType, ILocation)
		 */
		IMPLICIT_CONVERSION((ert, expr, ttype, loc, hook) -> ert.performImplicitConversion(expr, ttype, loc)),

		/**
		 * @see ExpressionResultTransformer#convertNullPointerConstantToPointer(ExpressionResult, CType, ILocation)
		 */
		CONVERT_NULL_POINTER_TO_CONSTANT(
				(ert, expr, ttype, loc, hook) -> ert.convertNullPointerConstantToPointer(expr, ttype, loc));

		private final ITransformationFunction mFun;

		Transformation(final ITransformationFunction fun) {
			mFun = Objects.requireNonNull(fun);
		}

	}

	private final CHandler mCHandler;
	private final MemoryHandler mMemoryHandler;
	private final StructHandler mStructHandler;
	private final ExpressionTranslation mExprTrans;
	private final TypeSizes mTypeSizes;
	private final AuxVarInfoBuilder mAuxVarInfoBuilder;
	private final ITypeHandler mTypeHandler;
	private final TypeSizeAndOffsetComputer mTypeSizeAndOffsetComputer;
	private final DataRaceChecker mDataRaceChecker;

	public ExpressionResultTransformer(final CHandler chandler, final MemoryHandler memoryHandler,
			final StructHandler structHandler, final ExpressionTranslation exprTrans, final TypeSizes typeSizes,
			final AuxVarInfoBuilder auxVarInfoBuilder, final ITypeHandler typeHandler,
			final TypeSizeAndOffsetComputer typeAndOffsetComputer, final DataRaceChecker dataRaceChecker) {
		mCHandler = chandler;
		mMemoryHandler = memoryHandler;
		mStructHandler = structHandler;
		mExprTrans = exprTrans;
		mTypeSizes = typeSizes;
		mAuxVarInfoBuilder = auxVarInfoBuilder;
		mTypeHandler = typeHandler;
		mTypeSizeAndOffsetComputer = typeAndOffsetComputer;
		mDataRaceChecker = dataRaceChecker;
	}

	private ExpressionResult transform(final ExpressionResult expr, final ICType targetCType, final ILocation loc,
			final IASTNode hook, final Transformation... transformations) {
		if (transformations == null || transformations.length == 0) {
			return expr;
		}

		ExpressionResult result = expr;
		for (final Transformation transformation : transformations) {
			if (transformation == null) {
				throw new IllegalArgumentException("transformation cannot be null");
			}
			result = transformation.mFun.apply(this, result, targetCType, loc, hook);
		}
		return result;
	}

	/**
	 * Dispatch a function argument and do conversions that are applied to all function arguments:
	 * <ul>
	 * <li>dispatch
	 * <li>DECAY_ARRAY_TO_POINTER
	 * <li>SWITCH_TO_RVALUE
	 * <li>REX_BOOL_TO_INT
	 * </ul>
	 */
	public ExpressionResult transformDispatchDecaySwitchRexBoolToInt(final IDispatcher main, final ILocation loc,
			final IASTInitializerClause hook) {
		final ExpressionResult dispatched = (ExpressionResult) main.dispatch(hook);
		return transform(dispatched, null, loc, hook, Transformation.DECAY_ARRAY_TO_POINTER,
				Transformation.SWITCH_TO_RVALUE, Transformation.REX_BOOL_TO_INT);
	}

	/**
	 * Dispatch a function argument and do conversions that are applied to all function arguments:
	 * <ul>
	 * <li>dispatch
	 * <li>DECAY_ARRAY_TO_POINTER
	 * <li>SWITCH_TO_RVALUE
	 * <li>IMPLICIT_CONVERSION
	 * </ul>
	 */
	public ExpressionResult transformDispatchDecaySwitchImplicitConversion(final IDispatcher main, final ILocation loc,
			final IASTInitializerClause hook, final ICType newTypeRaw) {
		final ExpressionResult dispatched = (ExpressionResult) main.dispatch(hook);
		return transform(dispatched, newTypeRaw, loc, hook, Transformation.DECAY_ARRAY_TO_POINTER,
				Transformation.SWITCH_TO_RVALUE, Transformation.IMPLICIT_CONVERSION);
	}

	public ExpressionResult transformDispatchSwitchRexBoolToInt(final IDispatcher main, final ILocation loc,
			final IASTInitializerClause hook) {
		final ExpressionResult dispatched = (ExpressionResult) main.dispatch(hook);
		return transform(dispatched, null, loc, hook, Transformation.SWITCH_TO_RVALUE, Transformation.REX_BOOL_TO_INT);
	}

	public ExpressionResult transformDecaySwitchRexBoolToInt(final ExpressionResult expr, final ILocation loc,
			final IASTNode hook) {
		return transform(expr, null, loc, hook, Transformation.DECAY_ARRAY_TO_POINTER, Transformation.SWITCH_TO_RVALUE,
				Transformation.REX_BOOL_TO_INT);
	}

	public ExpressionResult transformDecaySwitch(final ExpressionResult expr, final ILocation loc,
			final IASTNode hook) {
		return transform(expr, null, loc, hook, Transformation.DECAY_ARRAY_TO_POINTER, Transformation.SWITCH_TO_RVALUE);
	}

	public ExpressionResult transformSwitchRexBoolToInt(final ExpressionResult expr, final ILocation loc,
			final IASTNode hook) {
		return transform(expr, null, loc, hook, Transformation.SWITCH_TO_RVALUE, Transformation.REX_BOOL_TO_INT);
	}

	public ExpressionResult transformSwitchRexIntToBool(final ExpressionResult expr, final ILocation loc,
			final IASTNode hook) {
		return transform(expr, null, loc, hook, Transformation.SWITCH_TO_RVALUE, Transformation.REX_INT_TO_BOOL);
	}

	private ExpressionResult switchToRValue(final ExpressionResult expr, final ILocation loc, final IASTNode hook,
			final boolean unchecked) {
		final LRValue lrVal = expr.getLrValue();

		if (lrVal == null) {
			return expr;
		}
		if (lrVal instanceof RValue) {
			return replaceEnumByInt(replaceCFunctionByCPointer(expr));
		}
		if (lrVal instanceof LocalLValue) {
			final ICType underlyingType = lrVal.getCType().getUnderlyingType();
			mCHandler.moveArrayAndStructIdsOnHeap(underlyingType, lrVal.getValue(), hook);

			final ICType resultType;
			if (underlyingType instanceof final CArray cArray) {
				resultType = new CPointer(cArray.getValueType());
			} else if (underlyingType instanceof CFunction) {
				resultType = new CPointer(underlyingType);
			} else if (underlyingType instanceof CEnum) {
				resultType = new CPrimitive(CPrimitives.INT);
			} else {
				resultType = underlyingType;
			}
			final RValue newRVal = new RValue(lrVal.getValue(), resultType, lrVal.isBoogieBool());
			final ExpressionResultBuilder erb = new ExpressionResultBuilder(expr).setOrResetLrValue(newRVal);
			if (mDataRaceChecker != null) {
				mDataRaceChecker.checkOnRead(erb, loc, lrVal);
			}
			return erb.build();
		}
		if (lrVal instanceof final HeapLValue hlv) {
			ICType underlyingType = expr.getLrValue().getCType().getUnderlyingType();
			if (underlyingType instanceof CEnum) {
				underlyingType = new CPrimitive(CPrimitives.INT);
			}

			final ExpressionResultBuilder erb = new ExpressionResultBuilder().addAllExceptLrValue(expr);
			final RValue newValue;
			if (underlyingType instanceof CPrimitive || underlyingType instanceof CPointer) {
				final ExpressionResult rex =
						unchecked ? mMemoryHandler.getReadUnchecked(hlv.getAddress(), underlyingType)
								: mMemoryHandler.getReadCall(hlv.getAddress(), underlyingType);
				newValue = (RValue) rex.getLrValue();
				erb.addAllExceptLrValue(rex);
			} else if (underlyingType instanceof final CArray cArray) {
				newValue = new RValue(hlv.getAddress(), new CPointer(cArray.getValueType()), false, false);
			} else if (underlyingType instanceof CEnum) {
				throw new AssertionError("handled above");
			} else if (underlyingType instanceof final CStructOrUnion cStructOrUnion) {
				final ExpressionResult rex =
						readStructFromHeap(expr, loc, hlv.getAddress(), cStructOrUnion, hook, unchecked);
				newValue = (RValue) rex.getLrValue();
				erb.addAllExceptLrValue(rex);
			} else if (underlyingType instanceof CNamed) {
				throw new AssertionError("This should not be the case as we took the underlying type.");
			} else if (underlyingType instanceof CFunction) {
				newValue = new RValue(hlv.getAddress(), new CPointer(underlyingType), false, false);
			} else {
				throw new UnsupportedSyntaxException(loc, "..");
			}

			if (mDataRaceChecker != null) {
				mDataRaceChecker.checkOnRead(erb, loc, lrVal);
			}
			return erb.setLrValue(newValue).build();
		}
		throw new AssertionError("an LRValue that is not null, and no LocalLValue, RValue or HeapLValue???");
	}

	public ExpressionResult switchToRValue(final ExpressionResult expr, final ILocation loc, final IASTNode hook) {
		return switchToRValue(expr, loc, hook, false);
	}

	public ExpressionResult switchToRValueUnchecked(final ExpressionResult expr, final ILocation loc,
			final IASTNode hook) {
		return switchToRValue(expr, loc, hook, true);
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
	 * @param unchecked
	 * @param mExprTrans
	 * @param mTypeSizes
	 * @param mAuxVarInfoBuilder
	 * @param mCHandler
	 *
	 * @return A result whose value is a StructConstructor and whose statements make the necessary calls to fill the
	 *         items inside the StructConstructor correctly
	 */
	private ExpressionResult readStructFromHeap(final ExpressionResult old, final ILocation loc,
			final Expression structOnHeapAddress, final CStructOrUnion structType, final IASTNode hook,
			final boolean unchecked) {

		// everything for the new Result
		final ArrayList<Statement> newStmt = new ArrayList<>();
		final ArrayList<Declaration> newDecl = new ArrayList<>();
		final Set<AuxVarInfo> newAuxVars = new LinkedHashSet<>();

		final String[] fieldIds = structType.getFieldIds();
		final ICType[] fieldTypes = structType.getFieldTypes();

		// the new Arrays for the StructConstructor
		final ArrayList<String> fieldIdentifiers = new ArrayList<>();
		final ArrayList<Expression> fieldValues = new ArrayList<>();

		for (int i = 0; i < fieldIds.length; i++) {
			fieldIdentifiers.add(fieldIds[i]);

			final ICType underlyingType;
			if (fieldTypes[i] instanceof final CNamed cNamed) {
				underlyingType = cNamed.getUnderlyingType();
			} else {
				underlyingType = fieldTypes[i];
			}

			// ResultExpression fieldRead = null;
			final LRValue fieldLRVal;
			if (underlyingType instanceof CPrimitive) {
				final ExpressionResult fieldRead = (ExpressionResult) mStructHandler.readFieldInTheStructAtAddress(loc,
						i, structOnHeapAddress, structType, unchecked);
				fieldLRVal = fieldRead.getLrValue();
				newStmt.addAll(fieldRead.getStatements());
				newDecl.addAll(fieldRead.getDeclarations());
				newAuxVars.addAll(fieldRead.getAuxVars());
			} else if (underlyingType instanceof CPointer) {
				final ExpressionResult fieldRead = (ExpressionResult) mStructHandler.readFieldInTheStructAtAddress(loc,
						i, structOnHeapAddress, structType, unchecked);
				fieldLRVal = fieldRead.getLrValue();
				newStmt.addAll(fieldRead.getStatements());
				newDecl.addAll(fieldRead.getDeclarations());
				newAuxVars.addAll(fieldRead.getAuxVars());
			} else if (underlyingType instanceof final CArray cArray) {
				final Expression arrayPointer =
						mStructHandler.computeStructFieldAddress(loc, i, structOnHeapAddress, structType);
				final ExpressionResult xres1 = readArrayFromHeap(old, loc, arrayPointer, cArray, hook, unchecked);
				final ExpressionResult xres = xres1;

				fieldLRVal = xres.getLrValue();
				newStmt.addAll(xres.getStatements());
				newDecl.addAll(xres.getDeclarations());
				newAuxVars.addAll(xres.getAuxVars());

			} else if (underlyingType instanceof CEnum) {
				// like CPrimitive..
				final ExpressionResult fieldRead = (ExpressionResult) mStructHandler.readFieldInTheStructAtAddress(loc,
						i, structOnHeapAddress, structType, unchecked);
				fieldLRVal = fieldRead.getLrValue();
				newStmt.addAll(fieldRead.getStatements());
				newDecl.addAll(fieldRead.getDeclarations());
				newAuxVars.addAll(fieldRead.getAuxVars());
			} else if (underlyingType instanceof final CStructOrUnion cStructOrUnion) {

				final Offset innerStructOffset = mTypeSizeAndOffsetComputer.constructOffsetForField(loc, structType, i);
				if (innerStructOffset.isBitfieldOffset()) {
					throw new UnsupportedOperationException("Bitfield read struct from heap");
				}

				final var newAddress = mMemoryHandler.constructAddressForStructField(loc, structOnHeapAddress,
						innerStructOffset, mExprTrans.getCTypeOfPointerComponents());

				final ExpressionResult fieldRead =
						readStructFromHeap(old, loc, newAddress, cStructOrUnion, hook, unchecked);

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
			} else if (fieldLRVal instanceof final HeapLValue hlv) {
				fieldValues.add(hlv.getAddress());
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
	private ExpressionResult readArrayFromHeap(final ExpressionResult old, final ILocation loc,
			final Expression address, final CArray arrayType, final IASTNode hook, final boolean unchecked) {
		final ICType arrayValueType = arrayType.getValueType().getUnderlyingType();
		if (arrayValueType instanceof CArray) {
			throw new UnsupportedSyntaxException(loc,
					"we need to generalize this to nested and/or variable length arrays");
		}

		final BigInteger boundBigInteger = mTypeSizes.extractIntegerValue(arrayType.getBound());
		if (boundBigInteger == null) {
			throw new UnsupportedSyntaxException(loc, "variable length arrays not yet supported by this method");
		}
		final int bound = boundBigInteger.intValue();
		final AuxVarInfo newArrayAuxvar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, arrayType, SFO.AUXVAR.ARRAYCOPY);
		final LRValue resultValue = new RValue(newArrayAuxvar.getExp(), arrayType);
		ExpressionResultBuilder builder = new ExpressionResultBuilder();
		builder.addAuxVarWithDeclaration(newArrayAuxvar);

		final Expression valueTypeSize = mMemoryHandler.calculateSizeOf(loc, arrayValueType);
		final int typeSize = mTypeSizes.extractIntegerValue(valueTypeSize, arrayValueType).intValue();

		for (int pos = 0; pos < bound; pos++) {

			final var addressExpr =
					mMemoryHandler.addIntegerConstantToPointer(loc, address, BigInteger.valueOf(pos * typeSize));

			final ExpressionResult readRex;
			if (arrayValueType instanceof final CStructOrUnion cStructOrUnion) {
				readRex = readStructFromHeap(old, loc, addressExpr, cStructOrUnion, hook, unchecked);
			} else if (unchecked) {
				readRex = mMemoryHandler.getReadUnchecked(addressExpr, arrayType.getValueType());
			} else {
				readRex = mMemoryHandler.getReadCall(addressExpr, arrayType.getValueType());
			}
			builder.addAllExceptLrValue(readRex);
			builder.setOrResetLrValue(readRex.getLrValue());

			final ArrayLHS arrayAccLhs = ExpressionFactory.constructNestedArrayLHS(loc, newArrayAuxvar.getLhs(),
					new Expression[] { mTypeSizes.constructLiteralForIntegerType(loc,
							mExprTrans.getCTypeOfPointerComponents(), BigInteger.valueOf(pos)) });
			final ExpressionResult assRex =
					mCHandler.makeAssignment(loc, new LocalLValue(arrayAccLhs, arrayType.getValueType(), null),
							Collections.emptyList(), builder.build(), hook);
			builder = new ExpressionResultBuilder().addAllExceptLrValue(assRex).setLrValue(assRex.getLrValue());

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
	private RValue toBoolean(final ILocation loc, final RValue rVal) {
		assert !rVal.isBoogieBool();
		final Expression resultEx = mExprTrans.toBool(loc, rVal.getValue(), rVal.getCType());
		return new RValue(resultEx, new CPrimitive(CPrimitives.INT), true);
	}

	/**
	 * int <code>x</code> of form <code>y ? 1 : 0</code> becomes <code>!y ? 1 : 0</code> /** int <code>x</code> becomes
	 * <code>x == 0 ? 1 : 0</code>
	 */
	public ExpressionResult rexIntToBool(final ExpressionResult old, final ILocation loc) {
		if (!(old.getLrValue() instanceof final RValue rValue)) {
			throw new UnsupportedOperationException("only RValue can switch");
		}
		if (rValue.isBoogieBool()) {
			return old;
		}
		return new ExpressionResultBuilder(old).setOrResetLrValue(toBoolean(loc, rValue)).build();
	}

	private RValue toInteger(final ILocation loc, final RValue rVal) {
		assert rVal.isBoogieBool();
		return new RValue(mExprTrans.boolToInt(loc, rVal.getValue()), rVal.getCType(), false);
	}

	/**
	 * boolean <code>p</code> becomes <code>!p ? 1 : 0</code>
	 *
	 */
	public ExpressionResult rexBoolToInt(final ExpressionResult old, final ILocation loc) {
		if (old.getLrValue() == null || !old.getLrValue().isBoogieBool()) {
			/*
			 * This ExpressionResult does not have a value (for example it may be the translation of a call to a void
			 * function) or its value is not a bool. Void values like this are allowed for example in something like
			 * <code>0 ? foo() : 0</code> where foo is void. Do nothing here.
			 */
			return old;
		}

		if (!(old.getLrValue() instanceof final RValue rValue)) {
			throw new UnsupportedOperationException("only RValue can switch");
		}
		return new ExpressionResultBuilder(old).setOrResetLrValue(toInteger(loc, rValue)).build();
	}

	public ExpressionResult makeRepresentationReadyForConversionAndRexBoolToInt(final ExpressionResult expr,
			final ILocation loc, final ICType targetCType, final IASTNode hook) {
		final ExpressionResult readyExpr = makeRepresentationReadyForConversion(expr, loc, targetCType, hook);
		return rexBoolToInt(readyExpr, loc);
	}

	/**
	 * Switch our representation of the {@link ExpressionResult}'s value such that it can be converted to the
	 * targetCType. If the targetCType is a pointer or a primitive type and the type of this expression result is an
	 * {@link CArray} the array is decayed to a pointer, otherwise we just switch to an RValue.
	 */
	public ExpressionResult makeRepresentationReadyForConversion(final ExpressionResult expr, final ILocation loc,
			final ICType targetCType, final IASTNode hook) {
		if (expr.getLrValue() == null) {
			throw new AssertionError("Missing value " + loc);
		}
		if (expr.getLrValue().getCType().getUnderlyingType() instanceof CArray
				&& (targetCType.getUnderlyingType() instanceof CPointer
						|| targetCType.getUnderlyingType() instanceof CPrimitive)) {
			final ExpressionResultBuilder erb = new ExpressionResultBuilder().addAllExceptLrValue(expr);
			final RValue decayed = mCHandler.decayArrayLrValToPointer(expr.getLrValue(), hook);
			return erb.setLrValue(decayed).build();
		}
		return switchToRValue(expr, loc, hook);
	}

	/**
	 * If the CType of this {@link ExpressionResult}'s {@link RValue} has CType enum, then replace it by CType int. If
	 * an enum variable occurs as an RValue we use this method to replace its type by int.
	 *
	 */
	private static ExpressionResult replaceEnumByInt(final ExpressionResult old) {
		if (old.getLrValue() instanceof final RValue oldRValue) {
			if (oldRValue.getCType().getUnderlyingType() instanceof CEnum) {
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
		if (old.getLrValue() instanceof final RValue oldRValue) {
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
	 * If the {@link ICType} of is a {@link CArray}, we will return a new {@link ExpressionResult} in which the
	 * representation was switched from array to pointer. Otherwise this object is returned (without any modifications).
	 *
	 * Triggers that the array is moved on heap, if necessary.
	 *
	 * (this can be used for example for function parameters, when an array is passed by reference (which is the
	 * standard case).)
	 *
	 */
	public ExpressionResult decayArrayToPointer(final ExpressionResult result, final ILocation loc,
			final IASTNode hook) {
		if (result.getLrValue().getCType().getUnderlyingType() instanceof CArray) {
			final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();
			resultBuilder.addAllExceptLrValue(result);
			resultBuilder.setLrValue(mCHandler.decayArrayLrValToPointer(result.getLrValue(), hook));
			return resultBuilder.build();
		}
		return result;
	}

	/**
	 * Handle implicit conversions according to Section 6.3 of C11.
	 *
	 * See also {@link ExpressionTranslation#usualArithmeticConversions(ILocation, ExpressionResult, ExpressionResult)}.
	 *
	 * Modifies a given {@link ExpressionResult} such that the effect of a cast from the current {@link ICType} of the
	 * {@link ExpressionResult} to resultType is captured. Method may exchange the {@link RValue} of the
	 * {@link ExpressionResult} and add additional objects (statements, auxVars, etc.).
	 *
	 */
	public ExpressionResult performImplicitConversion(final ExpressionResult expr, final ICType targetCType,
			final ILocation loc) {
		final RValue rValIn = (RValue) expr.getLrValue();
		final ICType newType = targetCType.getUnderlyingType();
		final ICType oldType = rValIn.getCType().getUnderlyingType();

		final BoogieType oldBoogieType = (BoogieType) expr.getLrValue().getValue().getType();
		final BoogieType newBoogieType = mTypeHandler.getBoogieTypeForCType(targetCType);

		if (CompatibleTypes.areCompatible(newType, oldType) && !newType.equals(new CPrimitive(CPrimitives.BOOL))
				&& oldBoogieType.equals(newBoogieType)) {
			// types are already identical -- nothing to do
			// For _Bool we always do the conversion to ensure that the resulting value is 0 or 1
			return expr;
		}

		return switch (newType) {
		case final CPrimitive cPrimitive when cPrimitive.isIntegerType() -> convertToIntegerType(loc, expr, cPrimitive);
		case final CPrimitive cPrimitive when cPrimitive.isVoidType() -> convertToVoid(loc, expr, cPrimitive);
		case final CPrimitive cPrimitive when cPrimitive.isRealFloatingType() ->
				convertToFloatingType(loc, expr, cPrimitive);

		// could happen e.g. for COMPLEX_FLOAT etc
		case final CPrimitive cPrimitive -> throw new AssertionError("unknown primitive type " + cPrimitive.getType());

		// C standard 6.4.4.3.2
		// An identifier declared as an enumeration constant has type int.
		case final CEnum cEnum -> convertToIntegerType(loc, expr, new CPrimitive(CPrimitives.INT));

		case final CPointer cPointer -> convertToPointer(loc, expr, cPointer);

		case final CArray cArray -> throw new AssertionError("cannot convert to CArray");
		case final CFunction cFunction -> throw new AssertionError("cannot convert to CFunction");
		case final CNamed cNamed -> throw new AssertionError("getUnderlyingType() must not return CNamed");
		case final CStructOrUnion cStructOrUnion ->
				throw new UnsupportedSyntaxException(loc, "conversion to CStructOrUnion not implemented.");
		};
	}

	private ExpressionResult convertToIntegerType(final ILocation loc, final ExpressionResult rexp,
			final CPrimitive newType) {
		assert rexp.getLrValue() instanceof RValue : "has to be converted to RValue";
		final ICType oldType = rexp.getLrValue().getCType().getUnderlyingType();

		return switch (oldType) {
		case final CPrimitive cPrimitive when cPrimitive.isIntegerType() ->
				mExprTrans.convertIntToInt(loc, rexp, newType);
		case final CPrimitive cPrimitive when cPrimitive.isVoidType() ->
				throw new IncorrectSyntaxException(loc, "cannot convert from void");
		case final CPrimitive cPrimitive when cPrimitive.isRealFloatingType() ->
				mExprTrans.convertFloatToInt(loc, rexp, newType);
		// could happen e.g. for COMPLEX_FLOAT etc
		case final CPrimitive cPrimitive -> throw new AssertionError("unknown primitive type " + cPrimitive.getType());
		case final CPointer cPointer -> mMemoryHandler.convertPointerToInt(loc, rexp, newType);
		case final CEnum cEnum -> mExprTrans.convertIntToInt(loc, rexp, newType);
		case final CArray cArray -> throw new AssertionError("cannot convert from CArray");
		case final CFunction cFunction -> throw new AssertionError("cannot convert from CFunction");
		case final CNamed cNamed -> throw new AssertionError("getUnderlyingType() must not return CNamed");
		case final CStructOrUnion cStructOrUnion ->
				throw new UnsupportedSyntaxException(loc, "conversion from CStructOrUnion not implemented.");
		};
	}

	private ExpressionResult convertToPointer(final ILocation loc, final ExpressionResult rexp,
			final CPointer newType) {
		assert rexp.getLrValue() instanceof RValue : "has to be converted to RValue";
		final ICType oldType = rexp.getLrValue().getCType().getUnderlyingType();
		return switch (oldType) {
		case final CPrimitive cPrimitive when cPrimitive.isIntegerType() ->
				mMemoryHandler.convertIntToPointer(loc, rexp, newType);
		case final CPrimitive cPrimitive when cPrimitive.isRealFloatingType() ->

				throw new IncorrectSyntaxException(loc, "cannot convert float to pointer");
		case final CPrimitive cPrimitive when cPrimitive.isVoidType() ->
				throw new IncorrectSyntaxException(loc, "cannot convert from void");

		// could happen e.g. for COMPLEX_FLOAT etc
		case final CPrimitive cPrimitive -> throw new AssertionError("unknown primitive type " + cPrimitive.getType());
		case final CPointer cPointer -> convertPointerToPointer(loc, rexp, newType);
		case final CEnum cEnum -> mMemoryHandler.convertIntToPointer(loc, rexp, newType);
		case final CArray array when rexp instanceof StringLiteralResult -> {
			// a string literal's char-array decays to a pointer the stringLiteralResult already has the correct
			// RValue,we just need to change the type
			final RValue rVal =
					new RValue(rexp.getLrValue().getValue(), new CPointer(new CPrimitive(CPrimitives.CHAR)));
			yield new ExpressionResultBuilder().addAllExceptLrValue(rexp).setLrValue(rVal).build();
		}
		case final CArray cArray -> throw new AssertionError("cannot convert from CArray");
		case final CFunction cFunction -> throw new AssertionError("cannot convert from CFunction");
		case final CNamed cNamed -> throw new AssertionError("getUnderlyingType() must not return CNamed");
		case final CStructOrUnion cStructOrUnion ->
				throw new UnsupportedSyntaxException(loc, "conversion from CStructOrUnion not implemented.");
		};

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
		final ICType oldType = rexp.getLrValue().getCType().getUnderlyingType();

		switch (oldType) {
		case final CPrimitive cPrimitive -> {
			/* ok */ }
		case final CPointer cPointer -> {
			/* ok */ }
		case final CEnum cEnum -> {
			/* ok */ }
		case final CArray cArray -> throw new AssertionError("cannot convert from CArray");
		case final CFunction cFunction -> throw new AssertionError("cannot convert from CFunction");
		case final CStructOrUnion cStructOrUnion when newType.isVoidType() -> {
			// ok: we just keep the old value but change the type
			// alternative might be to set the value to null because it should never be used
		}
		case final CStructOrUnion cStructOrUnion ->
				throw new UnsupportedSyntaxException(loc, "cannot convert from CStructOrUnion to " + newType);
		case final CNamed cNamed -> throw new AssertionError("getUnderlyingType() must not return CNamed");
		}

		final RValue oldRValue = (RValue) rexp.getLrValue();
		final RValue rVal =
				new RValue(oldRValue.getValue(), newType, oldRValue.isBoogieBool(), oldRValue.isIntFromPointer());
		return new ExpressionResultBuilder().addAllExceptLrValue(rexp).setLrValue(rVal).build();
	}

	private ExpressionResult convertToFloatingType(final ILocation loc, final ExpressionResult rexp,
			final CPrimitive newType) {
		assert rexp.getLrValue() instanceof RValue : "has to be converted to RValue";
		final ICType oldType = rexp.getLrValue().getCType().getUnderlyingType();

		return switch (oldType) {
		case final CPrimitive cPrimitive when cPrimitive.isIntegerType() -> convertIfNecessary(loc, rexp, newType);
		case final CPrimitive cPrimitive when cPrimitive.isRealFloatingType() -> convertIfNecessary(loc, rexp, newType);
		case final CPrimitive cPrimitive when cPrimitive.isVoidType() ->
				throw new IncorrectSyntaxException(loc, "cannot convert from void");

		// could happen e.g. for COMPLEX_FLOAT etc
		case final CPrimitive cPrimitive -> throw new AssertionError("unknown primitive type " + cPrimitive.getType());

		case final CPointer cPointer -> throw new IncorrectSyntaxException(loc, "cannot convert pointer to float");
		case final CEnum cEnum -> convertIfNecessary(loc, rexp, newType);
		case final CArray cArray -> throw new AssertionError("cannot convert from CArray");
		case final CFunction cFunction -> throw new AssertionError("cannot convert from CFunction");
		case final CNamed cNamed -> throw new AssertionError("getUnderlyingType() must not return CNamed");
		case final CStructOrUnion cStructOrUnion ->
				throw new UnsupportedSyntaxException(loc, "conversion from CStructOrUnion not implemented.");
		};
	}

	/**
	 * Apply usual arithmetic conversion according to 6.3.1.8 of the C11 standard. Therefore we determine the determine
	 * the CType of the result. Afterwards we convert both operands to the result CType.
	 *
	 * TODO: This is not correct for complex types. E.g., if double and complex float are operands, the complex float is
	 * converted to a complex double not to a (real double). Fixing this will be postponed until we want to support
	 * complex types.
	 *
	 * @return A Pair of new {@link ExpressionResult}s, first for left and second for right.
	 */
	public Pair<ExpressionResult, ExpressionResult> usualArithmeticConversions(final ILocation loc,
			final ExpressionResult leftRex, final ExpressionResult rightRex) {
		final ExpressionResult leftPromoted = promoteToIntegerIfNecessary(loc, leftRex);
		final ExpressionResult rightPromoted = promoteToIntegerIfNecessary(loc, rightRex);

		final CPrimitive resultType = determineResultOfUsualArithmeticConversions(
				(CPrimitive) leftPromoted.getLrValue().getCType().getUnderlyingType(),
				(CPrimitive) rightPromoted.getLrValue().getCType().getUnderlyingType());

		final ExpressionResult resultLeft = convertIfNecessary(loc, leftPromoted, resultType);
		final ExpressionResult resultRight = convertIfNecessary(loc, rightPromoted, resultType);

		if (!resultLeft.getLrValue().getCType().getUnderlyingType().equals(resultType)) {
			throw new AssertionError("conversion failed");
		}
		if (!resultRight.getLrValue().getCType().getUnderlyingType().equals(resultType)) {
			throw new AssertionError("conversion failed");
		}
		return new Pair<>(resultLeft, resultRight);
	}

	private CPrimitive determineResultOfUsualArithmeticConversions(final CPrimitive leftPrimitive,
			final CPrimitive rightPrimitive) {
		if (leftPrimitive.getGeneralType() == CPrimitiveCategory.FLOATTYPE
				|| rightPrimitive.getGeneralType() == CPrimitiveCategory.FLOATTYPE) {
			if (leftPrimitive.isComplexType() || rightPrimitive.isComplexType()) {
				throw new UnsupportedOperationException("complex types not yet supported");
			}
			if (leftPrimitive.getType() == CPrimitives.LONGDOUBLE
					|| rightPrimitive.getType() == CPrimitives.LONGDOUBLE) {
				return new CPrimitive(CPrimitives.LONGDOUBLE);
			}
			if (leftPrimitive.getType() == CPrimitives.DOUBLE || rightPrimitive.getType() == CPrimitives.DOUBLE) {
				return new CPrimitive(CPrimitives.DOUBLE);
			}
			if (leftPrimitive.getType() == CPrimitives.FLOAT || rightPrimitive.getType() == CPrimitives.FLOAT) {
				return new CPrimitive(CPrimitives.FLOAT);
			}
			throw new AssertionError("unknown FLOATTYPE " + leftPrimitive + ", " + rightPrimitive);
		}
		if (leftPrimitive.getGeneralType() == CPrimitiveCategory.INTTYPE
				&& rightPrimitive.getGeneralType() == CPrimitiveCategory.INTTYPE) {
			return determineResultOfUsualArithmeticConversionsForInteger(leftPrimitive, rightPrimitive);
		}
		throw new AssertionError("unsupported combination of CPrimitives: " + leftPrimitive + " and " + rightPrimitive);
	}

	/**
	 * Perform the integer promotions a specified in C11 6.3.1.1.2 on the operand. If no integer promotion has to be
	 * performed (because we don't have a smaller integer type), the operand is returned.
	 */
	public final ExpressionResult promoteToIntegerIfNecessary(final ILocation loc, final ExpressionResult operand) {
		final ICType ctype = CEnum.replaceEnumWithInt(operand.getLrValue().getCType().getUnderlyingType());
		if ((ctype instanceof final CPrimitive cPrimitive) && integerPromotionNeeded(cPrimitive)) {
			final CPrimitive promotedType = determineResultOfIntegerPromotion(cPrimitive);
			return mExprTrans.convertIntToInt(loc, operand, promotedType);
		}
		return operand;
	}

	private static boolean integerPromotionNeeded(final CPrimitive cPrimitive) {
		return List.of(CPrimitives.CHAR, CPrimitives.SCHAR, CPrimitives.UCHAR, CPrimitives.SHORT, CPrimitives.USHORT)
				.contains(cPrimitive.getType());
	}

	private CPrimitive determineResultOfUsualArithmeticConversionsForInteger(final CPrimitive typeLeft,
			final CPrimitive typeRight) {
		if (typeLeft.equals(typeRight)) {
			return typeLeft;
		}
		if (mTypeSizes.isUnsigned(typeLeft) == mTypeSizes.isUnsigned(typeRight)) {
			return getMaximalType(typeLeft, typeRight);
		}
		final CPrimitive unsignedType;
		final CPrimitive signedType;
		if (mTypeSizes.isUnsigned(typeLeft)) {
			unsignedType = typeLeft;
			signedType = typeRight;
		} else {
			unsignedType = typeRight;
			signedType = typeLeft;
		}
		return getMaximalType(unsignedType, signedType);
	}

	private CPrimitive getMaximalType(final CPrimitive type1, final CPrimitive type2) {
		return mTypeSizes.getSize(type1.getType()) >= mTypeSizes.getSize(type2.getType()) ? type1 : type2;
	}

	private CPrimitive determineResultOfIntegerPromotion(final CPrimitive cPrimitive) {
		final int sizeOfArgument = mTypeSizes.getSize(cPrimitive.getType());
		final int sizeofInt = mTypeSizes.getSize(CPrimitive.CPrimitives.INT);

		if (sizeOfArgument < sizeofInt || !mTypeSizes.isUnsigned(cPrimitive)) {
			return new CPrimitive(CPrimitives.INT);
		}
		return new CPrimitive(CPrimitives.UINT);
	}

	/**
	 * Perform the necessary steps to convert {@link ExpressionResult} <code>operand</code> to a new type
	 * <code>resultType</code> if its type is not already <code>resultType</code>.
	 */
	public ExpressionResult convertIfNecessary(final ILocation loc, final ExpressionResult operand,
			final CPrimitive resultType) {
		if (operand.getLrValue().getCType().getUnderlyingType().equals(resultType)) {
			// do nothing
			return operand;
		}
		if (operand.getLrValue().getCType().getUnderlyingType().isIntegerType()) {
			if (resultType.isIntegerType()) {
				return mExprTrans.convertIntToInt(loc, operand, resultType);
			}
			if (resultType.isRealFloatingType()) {
				return mExprTrans.convertIntToFloat(loc, operand, resultType);
			}
			throw new UnsupportedSyntaxException(loc,
					"conversion from " + operand.getLrValue().getCType().getUnderlyingType() + " to " + resultType);
		}
		if (operand.getLrValue().getCType().getUnderlyingType().isRealFloatingType()) {
			if (resultType.isIntegerType()) {
				return mExprTrans.convertFloatToInt(loc, operand, resultType);
			}
			if (resultType.isRealFloatingType()) {
				return mExprTrans.convertFloatToFloat(loc, operand, resultType);
			}
			throw new UnsupportedSyntaxException(loc,
					"conversion from " + operand.getLrValue().getCType().getUnderlyingType() + " to " + resultType);
		}
		throw new UnsupportedSyntaxException(loc,
				"conversion from " + operand.getLrValue().getCType().getUnderlyingType() + " to " + resultType);
	}

	/**
	 * Convert a null pointer constant into a pointer a given pointer type. A null pointer constant can be (at least in
	 * our translation) a "0" that has integer type or something that has pointer type. TODO 2018-11-17 Matthias: I
	 * think we need this method an cannot apply the usual conversion since the usual restrictions for
	 * pointer-to-pointer conversions might be too strict. Furthermore, if (in the future) we take the type information
	 * from eclipse CDT we might be immediately able to identify the correct type of a "0" in the code.
	 *
	 */
	public ExpressionResult convertNullPointerConstantToPointer(final ExpressionResult nullPointerConstant,
			final ICType desiredResultType, final ILocation loc) {
		if (nullPointerConstant.getLrValue().getCType().getUnderlyingType().isIntegerType()) {
			return mMemoryHandler.convertIntToPointer(loc, nullPointerConstant, (CPointer) desiredResultType);
		}
		assert nullPointerConstant.getLrValue().getCType().getUnderlyingType() instanceof CPointer;
		return nullPointerConstant;
	}

	/**
	 * Dispatches a pointer and ensures that the result contains either a {@code LocalLValue} or a {@code HeapLValue}.
	 * If possible (i.e., pointer is of the form {@code &x} where {@code x} is not already on the heap), a
	 * {@code LocalLValue} is returned as an optimization.
	 *
	 * @param main
	 *            Dispatcher
	 * @param loc
	 *            Location
	 * @param pointer
	 *            Pointer AST-expression
	 * @return The dispatched {@code ExpressionResult} with either a {@code LocalLValue} or a {@code HeapLValue}.
	 */
	public ExpressionResult dispatchPointerLValue(final IDispatcher main, final ILocation loc, final IASTNode pointer) {
		if (isAdressofOperator(pointer)) {
			// If pointer is of the form &x, simply dispatch x an return the result, if it contains a LocalLValue.
			// To match the type, create a new LocalLValue with a pointer type that points to the type of x.
			final ExpressionResult subresult =
					(ExpressionResult) main.dispatch(((IASTUnaryExpression) pointer).getOperand());
			if (subresult.getLrValue() instanceof final LocalLValue addressValue) {
				final LocalLValue resultValue = new LocalLValue(addressValue.getLhs(),
						new CPointer(subresult.getCType()), addressValue.isBoogieBool(),
						addressValue.isIntFromPointer(), addressValue.getBitfieldInformation());
				return new ExpressionResultBuilder(subresult).resetLrValue(resultValue).build();
			}
		}
		// Otherwise simply dispatch the expression, but make sure that the result contains a HeapLValue.
		final ExpressionResult result = decayArrayToPointer((ExpressionResult) main.dispatch(pointer), loc, pointer);
		if (result.getLrValue() instanceof HeapLValue) {
			return result;
		}
		final ExpressionResultBuilder builder = new ExpressionResultBuilder(result);
		builder.resetLrValue(LRValueFactory.constructHeapLValue(mTypeHandler, result.getLrValue().getValue(),
				result.getCType(), null));
		return builder.build();
	}

	private static boolean isAdressofOperator(final IASTNode node) {
		return node instanceof final IASTUnaryExpression unaryExp
				&& unaryExp.getOperator() == IASTUnaryExpression.op_amper;
	}

	/**
	 * Assigns the value of the expression {@code rhs} to the given {@code lhs} of pointer type. If {@code lhs} is a
	 * {@code LocalLValue}, a simple assignment is performed, otherwise a write in the memory.
	 *
	 * @param loc
	 *            Location
	 * @param lhs
	 *            A LRValue of pointer type
	 * @param rhs
	 *            The expression to be assigned
	 * @return The expression result containing the assignment
	 */
	public ExpressionResult makePointerAssignment(final ILocation loc, final LRValue lhs, final Expression rhs) {
		if (lhs instanceof RValue) {
			return makePointerAssignment(loc, new HeapLValue(lhs.getValue(), lhs.getCType(), null), rhs);
		}
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		if (lhs instanceof final LocalLValue llv) {
			builder.addStatement(StatementFactory.constructSingleAssignmentStatement(loc, llv.getLhs(), rhs));
		} else if (lhs instanceof final HeapLValue hlv) {
			final ICType resultType = ((CPointer) lhs.getCType()).getPointsToType();
			builder.addStatements(mMemoryHandler.getWriteCall(loc, hlv, rhs, resultType, false));
		}
		if (mDataRaceChecker != null) {
			mDataRaceChecker.checkOnWrite(builder, loc, lhs);
		}
		return builder.build();
	}

	/**
	 * Reads the value of the given {@code value} of pointer type. The result is guaranteed to return an aux-var as
	 * RValue. If {@code value} is a {@code LocalLValue}, the value is simply assigned to a fresh aux-var, otherwise a
	 * read in the memory is performed (which also assigns the return value to an aux-var).
	 *
	 * @param loc
	 *            Location
	 * @param value
	 *            A LRValue of pointer type
	 * @return The expression result containing the assignment
	 */
	public ExpressionResult readPointerValue(final ILocation loc, final LRValue value) {
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		final ICType resultType = ((CPointer) value.getCType()).getPointsToType();
		if (mDataRaceChecker != null) {
			mDataRaceChecker.checkOnRead(builder, loc, value);
		}
		if (value instanceof final HeapLValue heapValue) {
			builder.addAllIncludingLrValue(mMemoryHandler.getReadCall(heapValue.getAddress(), resultType));
		} else {
			// Introduce an auxvar for the result for consistency, mMemoryHandler.getReadCall also creates an auxvar
			final AuxVarInfo auxVar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, resultType, AUXVAR.RETURNED);
			builder.addAuxVarWithDeclaration(auxVar).setLrValue(new RValue(auxVar.getExp(), resultType));
			builder.addStatement(
					StatementFactory.constructSingleAssignmentStatement(loc, auxVar.getLhs(), value.getValue()));
		}
		return builder.build();
	}

	@FunctionalInterface
	private interface ITransformationFunction {
		ExpressionResult apply(final ExpressionResultTransformer ert, final ExpressionResult expr,
				final ICType targetCType, final ILocation loc, final IASTNode hook);
	}
}
